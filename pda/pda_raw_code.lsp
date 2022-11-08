(include-book "pda/pda")
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)

:q
(in-package "ACL2S")
(import 'acl2s-interface::(acl2s-event acl2s-query acl2s-compute itest?-query))

(declaim (optimize (safety 3) (speed 0) (space 0) (debug 3)))
(declaim (sb-ext:muffle-conditions style-warning))


;;------------------------------------------------------------------------
;; Symbol name manipulation
;;------------------------------------------------------------------------

(defun gen-symb (x n)
  (read-from-string (format nil x n)))

(defun gen-sym-pred (x)
  (gen-symb "~ap" x))

(defun gen-symb-const (x)
  (gen-symb "*~a*" x))

(gen-sym-pred 'pda)

;;------------------------------------------------------------------------
;; PDA make/reset events generation
;;------------------------------------------------------------------------

(defun reset-history ()
  (acl2s-event `acl2s::(ubt 1)))

(defun reset-pda-def (d)
  (acl2s-event `acl2s::(ubt ',(gen-sym-pred d))))

(defun error-and-reset (msg def)
  (reset-dfa-def def)
  (cons nil (format nil "[~a]" msg)))


(defun query-function-has-start (txf start-state)
  (in (list start-state :e :e) (strip-cars txf) :test 'equal))

(defun query-function-start-state-adds-base (txf start-state)
  (not (endp (remove :e (mapcar 'second (pda-trx-lookup txf (list start-state :e :e)))))))

(defun query-function-distinctdom (txf)
  (let ((domain (strip-cars txf)))
    (not (== (len domain)
             (len (remove-duplicates domain :test 'equal))))))

(defun query-extra-functiondom (state-def elem-def stk-elem-def txf)
  (let ((es1 (gen-sym-pred elem-def))
        (es2 (gen-sym-pred stk-elem-def))
	(ss (gen-sym-pred state-def))
        (doma (strip-cars txf)))
    (itest?-query
     `acl2s::(=> (in state-element-pair= (quote ,doma))
                 (and  (,ss (first state-element-pair=))
                       (,es1 (second state-element-pair=))
                       (,es2 (third state-element-pair=)))))))

;; generates defdata events while also checking if input is actually a PDA
(defun mk-pda-events (name states alphabet stack-alphabet
			   start-state accept-states transition-fun)
  (b* ((p-state (gen-symb "~a-state" name))
       (p-states (gen-symb "~a-states" name))
       (p-elem (gen-symb "~a-element" name))
       (p-word (gen-symb "~a-word" name))
       (p-ab (gen-symb "~a-alphabet" name))
       (p-stk-elem (gen-symb "~a-stk-element" name))
       (p-stk-word (gen-symb "~a-stk-word" name))
       (p-stk-ab (gen-symb "~a-stk-alphabet" name))
       (p-tdom (gen-symb "~a-t-domain" name))
       (p-trange (gen-symb "~a-t-range" name))
       (p-f (gen-symb "~a-transition-function" name))
       (p-fp (gen-sym-pred p-f))
       (pda-name (gen-symb-const name))
       (- (acl2s-event `acl2s::(defdata ,p-state  (enum (quote ,states)))))
       ((unless (statesp `acl2s::,states))
	(error-and-reset "incorrect states" p-state))
       (- (acl2s-event `acl2s::(defdata ,p-states (listof ,p-state))))
       (- (acl2s-event `acl2s::(defdata ,p-elem  (enum (quote ,alphabet)))))
       (- (acl2s-event `acl2s::(defdata ,p-word (listof ,p-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-ab ,p-word)))
       (- (acl2s-event `acl2s::(defdata ,p-stk-elem  (enum (quote ,stack-alphabet)))))
       (- (acl2s-event `acl2s::(defdata ,p-stk-word (listof ,p-stk-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-stk-ab ,p-stk-word)))
       ((unless (in start-state `acl2s::,states)) (error-and-reset "incorrect start state" p-state))
       ((unless (subset `acl2s::,accept-states `acl2s::,states))
        (error-and-reset "incorrect accept states" p-state))
       (- (acl2s-event `acl2s::(defdata ,p-tdom (list ,p-state ,p-elem ,p-stk-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-trange (listof (list ,p-state ,p-stk-elem)))))
       (- (acl2s-event `acl2s::(defdata ,p-f (alistof ,p-tdom ,p-trange))))
       (res (query-function-distinctdom transition-fun))
       ((when res) (error-and-reset "transition function domain is not distinct." p-state))
       (res (query-extra-functiondom p-state p-elem p-stk-elem transition-fun))
       ((when (car res)) (error-and-reset (format nil "Domain of transition function is not of type : states x input alphabet x stack alphabet ~a." (cdr res)) p-state))
       ((unless (query-function-has-start transition-fun start-state))
        (error-and-reset (format nil "Starting
transition from (~a :e :e) missing from the transition function." start-state) p-state))
       ((unless (query-function-start-state-adds-base transition-fun start-state))
        (error-and-reset (format nil "Start state
transition does not add a base stack symbol" start-state) p-state))
       ;;(if (not (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun)))))
       ;; with all the other checks we added for functions, we do not really need to enforce it as a map
       ;;  (error-and-reset "incorrect transition function" d-state)
       (- (acl2s-event `acl2s::(defconst ,pda-name (list ',states ',alphabet ',stack-alphabet ',transition-fun ',start-state ',accept-states)))))
    (cons t (format nil "Legal PDA : ~a" `acl2s::(,states ,alphabet ,stack-alphabet ,transition-fun ,start-state ,accept-states)))))
  

(defun gen-pda-fn (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (mk-pda-events name states alphabet stack-alphabet start-state accept-states transition-fun))

(defmacro gen-pda (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (b* (((unless name) '(cons nil "name missing"))
       ((unless states) '(cons nil "states missing"))
       ((unless alphabet) '(cons nil "alphabet missing"))
       ((unless stack-alphabet) '(cons nil "stack alphabet missing"))
       ((unless start-state) '(cons nil "start state missing"))
       ((unless accept-states) '(cons nil "accept states missing"))
       ((unless transition-fun) '(cons nil "transition-fun missing"))
       (up-ab (cons :e alphabet))
       (up-stkab (cons :e stack-alphabet)))
    `(gen-pda-fn :name ',name
                 :states ',states
                 :alphabet ',up-ab
                 :stack-alphabet ',up-stkab
                 :start-state ',start-state
                 :accept-states ',accept-states
                 :transition-fun ',transition-fun)))

;;run-steps is set to explore a depth of 100 in the execution tree.
;;having more depth will require more time to find accepting states.


;;------------------------------------------------------------------------
;; DFA check events generation
;;------------------------------------------------------------------------

(defun query-alphabet-equal (pda1-name pda2-name)
  (let ((da1 (gen-symb "~a-alphabet" pda1-name))
	(da2 (gen-symb "~a-alphabet" pda2-name)))
    (acl2s-event
     `acl2s::(defdata-equal-strict ,da1 ,da2))))

(defun query-equivalence (pda1-name pda2-name)
  (let ((res (query-alphabet-equal pda1-name pda2-name))
	(dn (gen-symb "~a-wordp" pda1-name))
	(pda1 (gen-symb-const pda1-name))
	(pda2 (gen-symb-const pda2-name)))
    (unless (boundp pda1)
      (reset-and-exit :msg (format nil "Undefined PDA ~a" pda1-name)
                      :func query-equivalence))
    (unless (boundp pda2)
      (reset-and-exit :msg (format nil "Undefined PDA ~a" pda2-name)
                      :func query-equivalence))
    (if (car res)
	(cons nil "Incorrect alphabet provided.")
      (let ((res (itest?-query
                  `acl2s::(=> (,dn w)
                              (== (accept-pda ,pda1 w)
                                  (accept-pda ,pda2 w))))))
        (if (car res)
            (cons nil (format nil "Transition function error. The following words
  were misclassified :~% ~a" (substitute :e nil (mapcar #'cadar (cadadr res)))
  (gen-symb "~a-state" pda2-name)))
          (cons t (format nil "~a is correct." pda2-name)))))))



;;------------------------------------------------------------------------
;; PAPER EXAMPLES
;;------------------------------------------------------------------------
#|
(gen-pda
 :name instr
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 z)
 :start-state q0
 :accept-states (q0 q3)
 :transition-fun (((q0 :e :e) . ((q1 z)))
                  ((q1 0  :e) . ((q1 0)))
                  ((q1 1   0)   . ((q2 :e)))
                  ((q2 1   0)   . ((q2 :e)))
                  ((q2 :e z)   . ((q3 :e)))))

(gen-pda
 :name student
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 z)
 :start-state q0
 :accept-states (q3)
 :transition-fun (((q0 :e :e) . ((q1 z)))
                  ((q1 0  :e) . ((q1 0)))
                  ((q1 1   0)   . ((q2 :e)))
                  ((q2 1   0)   . ((q2 :e)))
                  ((q2 :e z)   . ((q3 :e)))))


(query-equivalence 'instr 'student)
(accept-pda *instr* nil)
(accept-pda *student* nil)


(gen-pda
 :name pda1
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 b)
 :start-state q0
 :accept-states (q0 q3)
 :transition-fun (((q0 :e :e) . ((q1 b)))
                  ((q1 :e 0) . ((q1 0)))
                  ((q1 0   :e) . ((q1 0)))
                  ((q1 1   0)   . ((q2 :e)))
                  ((q2 1   0)   . ((q2 :e)))
                  ((q2 :e b)   . ((q3 :e)))))

(accept-pda *pda1* '(0 0 0 0 0 0 0 1 1 1 1 1 1 1))


(gen-pda
 :name zn1n
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 z)
 :start-state q0
 :accept-states (q3)
 :transition-fun (((q0 :e :e) . ((q1 z)))
                  ((q1 0  :e) . ((q1 0)))
                  ((q1 1   0)   . ((q2 :e)))
                  ((q2 1   0)   . ((q2 :e)))
                  ((q2 :e z)   . ((q3 :e)))))


(accept-pda *ZN1N* '(0 0 1 1))
(accept-pda *ZN1N* '(0 0 1 1 1))
(accept-pda *ZN1N* '(0 0 0 0 0 0 0  0 1 1 1 1 1 1 1 1 1))
(accept-pda *ZN1N* '(0 0 0 0 0 0 0  0 1 1 1 1 1 1 1 1 1 0))
(accept-pda *ZN1N* '(0 0 0 0 0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1))
(accept-pda *ZN1N* '())

(gen-pda
 :name pda2
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 b)
 :start-state q0
 :accept-states (q3)
 :transition-fun (((q0 :e :e) . ((q1 b) (q3 :e)))
                  ((q1 :e 0) . ((q1 0)))
                  ((q1 0   :e) . ((q1 0)))
                  ((q2 :e 0) . ((q2 0)))
                  ((q2 0   :e) . ((q2 0)))
                  ((q1 1   0)   . ((q2 :e)))
                  ((q2 1   0)   . ((q2 :e)))
                  ((q2 :e b)   . ((q3 :e)))))

(accept-pda *pda2* '(0))
(accept-pda *pda2* '(0 0 0 0 0 0 0 1 1 1 1 1 1 1))
(accept-pda *pda2* '())
(time (accept-pda *pda2* '(0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1)))
(time (accept-pda *pda2* '(0 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1)))

|#
