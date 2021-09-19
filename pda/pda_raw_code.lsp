(include-book "../gradescope-acl2s/interface/top")
(include-book "pda")

:q
(in-package "ACL2S")
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
;; DFA make/reset events generation
;;------------------------------------------------------------------------

(defun reset-history ()
  (acl2s-event `acl2s::(ubt 1)))

(defun reset-pda-def (d)
  (acl2s-event `acl2s::(ubt ',(gen-sym-pred d))))

(defun error-and-reset (msg def)
  (progn (reset-pda-def def)
	 (cons nil (format nil "[~a]" msg))))


(defun query-function-has-start (txf start-state)
  (in (list start-state nil nil) (strip-cars txf) :test 'equal))


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
  (let* ((p-state (gen-symb "~a-state" name))
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
         (pda-name (gen-symb-const name)))
    (acl2s-event `acl2s::(defdata ,p-state  (enum (quote ,states))))
    (if (not (statesp `acl2s::,states))
	(error-and-reset "incorrect states" p-state)
      (progn (acl2s-event `acl2s::(defdata ,p-states (listof ,p-state)))
	     (acl2s-event `acl2s::(defdata ,p-elem  (enum (quote ,(cons nil alphabet)))))
	     (acl2s-event `acl2s::(defdata ,p-word (listof ,p-elem)))
	     (acl2s-event `acl2s::(defdata ,p-ab ,p-word))
             (acl2s-event `acl2s::(defdata ,p-stk-elem  (enum (quote ,(cons nil stack-alphabet)))))
             (acl2s-event `acl2s::(defdata ,p-stk-word (listof ,p-stk-elem)))
             (acl2s-event `acl2s::(defdata ,p-stk-ab ,p-stk-word))
	     (if (not (in start-state `acl2s::,states))
		 (error-and-reset "incorrect start state" p-state)
	       (progn
		 (if (not (subset `acl2s::,accept-states `acl2s::,states))
		     (error-and-reset "incorrect accept states" p-state)
		   (progn 
		     (acl2s-event `acl2s::(defdata ,p-tdom (list ,p-state ,p-elem ,p-stk-elem)))
                     (acl2s-event `acl2s::(defdata ,p-trange (listof (list ,p-state ,p-stk-elem))))
		     (acl2s-event `acl2s::(defdata ,p-f (alistof ,p-tdom ,p-trange)))
                     (let ((res (query-function-distinctdom transition-fun)))
                       (if res (error-and-reset "transition function domain is not distinct" p-state)
                         (let ((res (query-extra-functiondom p-state p-elem p-stk-elem transition-fun)))
                           (if (car res)
                               (error-and-reset (format nil "Domain of transition function is not of type : states x input alphabet x stack alphabet ~a" (cdr res)) p-state)
                             (if (not (query-function-has-start transition-fun start-state))
                                 (error-and-reset (format nil "Starting domain (~a nil nil) missing from the transition function" start-state) p-state)
                             ;;(if (not (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun)))))
                             ;; with all the other checks we added for functions, we do not really need to enforce it as a map
                             ;;  (error-and-reset "incorrect transition function" d-state)
                               (progn (acl2s-event `acl2s::(defconst ,pda-name (list ',states ',alphabet ',stack-alphabet ',transition-fun ',start-state ',accept-states)))
                                      (cons t (format nil "Legal PDA : ~a" `acl2s::(,states ,alphabet ,stack-alphabet ,transition-fun ,start-state ,accept-states)))))))))))))))))
  
  


(defun gen-pda-fn (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (let* ((df `acl2s::(,states ,alphabet ,stack-alphabet ,transition-fun ,start-state ,accept-states)))
    (mk-pda-events name states alphabet stack-alphabet start-state accept-states transition-fun)))

(defmacro gen-pda (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (unless name (error "name missing"))
  (unless states (error "states missing"))
  (unless alphabet (error "alphabet missing"))
  (unless stack-alphabet (error "stack alphabet missing"))
  (unless start-state (error "start state missing"))
  (unless accept-states (error "accept states missing"))
  (unless transition-fun (error "transition-fun missing"))
  (let ((up-ab (cons nil alphabet)))
  `(gen-pda-fn :name ',name
	       :states ',states
	       :alphabet ',up-ab
	       :stack-alphabet ',stack-alphabet
	       :start-state ',start-state
	       :accept-states ',accept-states
	       :transition-fun ',transition-fun)))


(gen-pda
 :name zn4n
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 b)
 :start-state q0
 :accept-states (q0 q3)
 :transition-fun (((q1 0   nil) . ((q1 0)))
                  ((q1 1   0)   . ((q2 nil)))
                  ((q2 1   0)   . ((q2 nil)))
                  ((q2 nil b)   . ((q3 nil)))))


(defun run-pda (pda w)
  (run-steps 20 pda `(,(list (pda-start pda) nil w))))


(run-pda *pda-test* '( #\( #\) ))
(run-pda *pda-test* '( #\( #\) #\( #\( #\) #\) #\( #\( #\( #\) #\) #\) ))
(run-pda *pda-test* '( #\( #\( ))     
(run-pda *pda-test* '( #\( #\) #\( ))

(run-pda *ZN1N* '(0 0 1 1))
(run-pda *ZN1N* '(0 0 1 1 1))
(run-pda *ZN1N* '())



#|
(save-exec "pda_run_exec" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::main (cdr sb-ext:*posix-argv*))' --disable-debugger")
|#


