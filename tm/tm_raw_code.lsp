(include-book "tm/tm")
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

(gen-sym-pred 'tm)

(defun gen-symb-const (x)
  (gen-symb "*~a*" x))

(defun display-tape (m)
  (format t "~%~A~%" (append (reverse (second m))
			     (list (first m))
			     (third m)
			     )))

;(display-tape (run-tm '(#\1 #\2 #\2 #\1 #\1) *tm-test*))


;;------------------------------------------------------------------------
;; TM make/reset events generation
;;------------------------------------------------------------------------

(defun reset-history ()
  (acl2s-event `acl2s::(ubt 1)))
 
(defun reset-tm-def (d)
  (acl2s-event `acl2s::(ubt ',(gen-sym-pred d))))

(defun error-and-reset (msg def)
  (reset-tm-def def)
  (cons nil (format nil "[~a]" msg)))

;; generates defdata events while also checking if input is actually a TM
(defun mk-tm-events (name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (b* ((p-state (gen-symb "~a-state" name))
       (p-states (gen-symb "~a-states" name))
       (p-elem (gen-symb "~a-element" name))
       (p-tape-elem (gen-symb "~a-tape-element" name))
       (p-word (gen-symb "~a-word" name))
       (p-tape-word (gen-symb "~a-tape-word" name))
       (p-ab (gen-symb "~a-alphabet" name))
       (p-tape-ab (gen-symb "~a-tape-alphabet" name))
       (p-dir (gen-symb "~a-direction" name))
       (p-tdom (gen-symb "~a-t-domain" name))
       (p-trange (gen-symb "~a-t-range" name))
       (p-f (gen-symb "~a-transition-function" name))
       (p-fp (gen-sym-pred p-f))
       (tm-name (gen-symb-const name))
       (- (acl2s-event `acl2s::(defdata ,p-state  (enum (quote ,states)))))
       ((unless (statesp `acl2s::,states)) (error-and-reset "incorrect states" p-state))
       (- (acl2s-event `acl2s::(defdata ,p-states (listof ,p-state))))
       (- (acl2s-event `acl2s::(defdata ,p-elem  (enum (quote ,alphabet)))))
       (- (acl2s-event `acl2s::(defdata ,p-word (listof ,p-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-ab ,p-word)))
       (- (acl2s-event `acl2s::(defdata ,p-tape-elem  (enum (quote ,tape-alphabet)))))
       (- (acl2s-event `acl2s::(defdata ,p-tape-word (listof ,p-tape-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-tape-ab ,p-tape-word)))
       ((unless (subset `acl2s::,alphabet `acl2s::,tape-alphabet))
        (error-and-reset "Input alphabet should be a subset of tape-alphabet" p-state))
       ((when (in nil `acl2s::,alphabet)) (error-and-reset (format nil "Blank tape symbol nil cannot be in alphabet" reject-state) p-state))
       ((unless (in start-state `acl2s::,states)) (error-and-reset (format nil "Incorrect start-state ~a" start-state) p-state))
       ((unless (in accept-state `acl2s::,states)) (error-and-reset (format nil "Incorrect accept-state ~a" accept-state) p-state))
       ((unless (in reject-state `acl2s::,states)) (error-and-reset (format nil "Incorrect reject-state ~a" reject-state) p-state))
       ((unless (in nil `acl2s::,tape-alphabet)) (error-and-reset (format nil "Blank tape symbol nil missing from tape-alphabet" reject-state) p-state))
       (- (acl2s-event `acl2s::(defdata ,p-dir (enum '(L R)))))
       (- (acl2s-event `acl2s::(defdata ,p-tdom (list ,p-state ,p-tape-elem))))
       (- (acl2s-event `acl2s::(defdata ,p-trange (list ,p-state ,p-tape-elem ,p-dir))))
       (- (acl2s-event `acl2s::(defdata ,p-f (alistof ,p-tdom ,p-trange))))
       ((unless (second (acl2s-compute `acl2s::(,p-fp (quote ,transition-fun)))))
        (error-and-reset "Incorrect transition function, check syntax" p-state))
       (doms (strip-cars transition-fun))
       (res (equal doms (remove-duplicates-equal doms)))
       ((unless res) (error-and-reset "Domain of the transition function is not unique" p-state))
       (- (acl2s-event `acl2s::(defconst ,tm-name (list ',states ',alphabet ',tape-alphabet ',transition-fun ',start-state ',accept-state ',reject-state)))))
    (cons t (format nil "Legal TM : ~a" `acl2s::(,states ,alphabet ,tape-alphabet ,transition-fun ,start-state ,accept-state ,reject-state)))))

(defun gen-tm-fn (&key name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (mk-tm-events name states alphabet tape-alphabet start-state accept-state reject-state transition-fun))

(defmacro gen-tm (&key name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (b* (((unless name) '(cons nil "name missing"))
       ((unless states) '(cons nil "states missing"))
       ((unless alphabet) '(cons nil "alphabet missing"))
       ((unless tape-alphabet) '(cons nil "tape alphabet missing"))
       ((unless start-state) '(cons nil "start state missing"))
       ((unless accept-state) '(cons nil "accept state missing"))
       ((unless reject-state) '(cons nil "reject state missing"))
       ((unless transition-fun) '(cons nil "transition-fun missing")))
    `(gen-tm-fn  :name ',name
                 :states ',states
                 :alphabet ',alphabet
                 :tape-alphabet ',tape-alphabet
                 :start-state ',start-state
                 :accept-state ',accept-state
                 :reject-state ',reject-state
                 :transition-fun ',transition-fun)))

(defun remove-forward-nils (xs)
  (cond ((and (consp xs)
	      (equal (car xs) nil)) (remove-forward-nils (cdr xs)))
	(t xs)))
	 
(defun prefixp (exp seq)
  (cond ((endp exp) t)
	((endp seq) nil)
	(t (and (equal (car exp) (car seq))
		(prefixp (cdr exp) (cdr seq))))))

(defun check-tm-output (f1 expected w)
  (b* ((tm1 (eval (with-open-file (infile f1) (read infile))))
	 (p (if (consp tm1)
		(format t "[~%~A ACCEPTED~%" (car tm1))
	      nil))
	 (res (run-tm w (cdr tm1))))
    (if (and (equal (car res) t)
	     (== expected (remove-forward-nils (left-of-head res))))
        (cons t "Passed test case]")
      (cons nil "Failed test case]"))))

(defun query-alphabet-equal (tm1-name tm2-name)
  (let ((da1 (gen-symb "~a-alphabet" tm1-name))
	(da2 (gen-symb "~a-alphabet" tm2-name)))
    (acl2s-event
     `acl2s::(defdata-equal-strict ,da1 ,da2))))


(defun query-equivalence-state (tm1-name tm2-name)
  (let ((res (query-alphabet-equal tm1-name tm2-name))
	(dn (gen-symb "~a-wordp" tm1-name))
	(tm1 (gen-symb-const tm1-name))
	(tm2 (gen-symb-const tm2-name)))
    (let ((res (itest?-query
                `acl2s::(=> (,dn w)
                            (== (accept-tm w ,tm1)
                                (accept-tm w ,tm2))))))
      (if (car res)
            (cons nil (format nil "Transition function error. The following words
  were misclassified :~% ~a" (mapcar #'cadar (cadadr res))))
  (gen-symb "~a-state" tm2-name)))
    (cons t (format nil "~a is correct." tm2-name))))

(defun query-equivalence-output (tm1-name tm2-name)
  (b* ((dn (gen-symb "~a-wordp" tm1-name))
       (tm1 (gen-symb-const tm1-name))
       (tm2 (gen-symb-const tm2-name))
       ((unless (boundp tm1))
        (cons nil (format nil "Undefined TM ~a" tm1-name)))
       ((unless (boundp tm2))
        (cons nil (format nil "Undefined TM ~a" tm2-name)))
       (res (query-alphabet-equal tm1-name tm2-name))
       ((when (car res))
        (cons nil "Incorrect alphabet provided."))
       (res (itest?-query
             `acl2s::(=> (,dn w)
                         (== (remove-final-nils (left-of-head (run-tm w ,tm1)))
                             (remove-final-nils (left-of-head (run-tm w ,tm2)))))))
       ((when (car res))
        (cons nil (format nil "Incorrect output produced when running submitted TM on the following words :~% ~a" (mapcar #'cadar (cadadr res))))))
    (cons t (format nil "~a is correct." tm2-name))))

#|
(gen-tm
 :name instructor-tm
 :states (q0 q1 q2 q3)
 :alphabet (#\0 #\1)
 :tape-alphabet (#\0 #\1 nil)
 :start-state q0
 :accept-state q1
 :reject-state q2
 :transition-fun (((q0 #\1) . (q0 #\0 R))
                  ((q0 #\0) . (q0 #\1 R))
                  ((q0 nil) . (q3 nil R))
                  ((q3 nil) . (q1 nil L))))

(gen-tm
 :name student-tm3
 :states (q0 q1 q2 q3)
 :alphabet (#\0 #\1)
 :tape-alphabet (#\0 #\1 nil)
 :start-state q0
 :accept-state q1
 :reject-state q2
 :transition-fun (((q0 #\1) . (q0 #\0 R))
                  ((q0 #\0) . (q0 #\0 R))
                  ((q0 nil) . (q3 nil R))
                  ((q3 nil) . (q1 nil L))))

(query-equivalence-output 'instructor-tm 'student-tm3)
|#
