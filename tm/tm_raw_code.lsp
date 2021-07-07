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

(gen-sym-pred 'tm)

(defun gen-symb-const (x)
  (gen-symb "*~a*" x))

(defun display-tape (m)
  (format t "~%~A~%" (append (reverse (second m))
			     (list (first m))
			     (third m)
			     )))

(display-tape (runtm-100 '(#\1 #\2 #\2 #\1 #\1) *tm-test*))


;;------------------------------------------------------------------------
;; TM make/reset events generation
;;------------------------------------------------------------------------


(defun check-tm-output-state (tm1 tm2)
    (acl2s-event `acl2s::(test? (=> (tape-wordp w)
				    (== (first (runtm-100 w ',tm1))
					(first (runtm-100 w ',tm2)))))))

(defun check-tm-output-tape (tm1 tm2)
    (acl2s-event `acl2s::(test? (=> (tape-wordp w)
				    (== (remove-beginnils (second (runtm-100 w ',tm1)))
					(remove-beginnils (second (runtm-100 w ',tm2))))))))




;; Testing if 2 TMs behave the same way
(check-tm-output-state *tm-test* *tm-test2*)
(check-tm-output-tape *tm-test* *tm-test2*)


  

(defun reset-history ()
  (acl2s-event `acl2s::(ubt 1)))
 
(defun reset-tm-def (d)
  (acl2s-event `acl2s::(ubt ',(gen-sym-pred d))))

(defun error-and-reset (msg def)
  (progn (reset-tm-def def)
	 (error (format nil "[~a]" msg))
         (sb-ext:exit)))

;; generates defdata events while also checking if input is actually a TM
(defun mk-tm-events (name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (let* ((p-state (gen-symb "~a-state" name))
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
         (tm-name (gen-symb-const name)))
    (acl2s-event `acl2s::(defdata ,p-state  (enum (quote ,states))))
    (unless (statesp `acl2s::,states) (error-and-reset "incorrect states" p-state))
    (acl2s-event `acl2s::(defdata ,p-states (listof ,p-state)))
    (acl2s-event `acl2s::(defdata ,p-elem  (enum (quote ,alphabet))))
    (acl2s-event `acl2s::(defdata ,p-word (listof ,p-elem)))
    (acl2s-event `acl2s::(defdata ,p-ab ,p-word))
    (acl2s-event `acl2s::(defdata ,p-tape-elem  (enum (quote ,tape-alphabet))))
    (acl2s-event `acl2s::(defdata ,p-tape-word (listof ,p-tape-elem)))
    (acl2s-event `acl2s::(defdata ,p-tape-ab ,p-tape-word))
    (unless (subset `acl2s::,alphabet `acl2s::,tape-alphabet)
      (error-and-reset "input alphabet should be a subset of tape alphabet" p-state))
    (unless (in start-state `acl2s::,states) (error-and-reset (format t "incorrect start state ~a" start-state) p-state))
    (unless (in accept-state `acl2s::,states) (error-and-reset (format t "incorrect accept state ~a" accept-state) p-state))
    (unless (in reject-state `acl2s::,states) (error-and-reset (format t "incorrect reject state ~a" reject-state) p-state))
    (acl2s-event `acl2s::(defdata ,p-dir (enum '(L R))))
    (acl2s-event `acl2s::(defdata ,p-tdom (list ,p-state ,p-tape-elem)))
    (acl2s-event `acl2s::(defdata ,p-trange (list ,p-state ,p-tape-elem ,p-dir)))
    (acl2s-event `acl2s::(defdata ,p-f (alistof ,p-tdom ,p-trange)))
    (unless (second (acl2s-compute `acl2s::(,p-fp (quote ,transition-fun))))
      (error-and-reset "incorrect transition function" p-state))

    (acl2s-event `acl2s::(defconst ,tm-name (list ',states ',alphabet ',tape-alphabet ',transition-fun ',start-state ',accept-state ',reject-state)))
    (cons t (format nil "Legal TM : ~a" `acl2s::(,states ,alphabet ,tape-alphabet ,transition-fun ,start-state ,accept-state ,reject-state)))))



(defun gen-tm-fn (&key name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (mk-tm-events name states alphabet tape-alphabet start-state accept-state reject-state transition-fun))



(defmacro gen-tm (&key name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (unless name (error "name missing"))
  (unless states (error "states missing"))
  (unless alphabet (error "alphabet missing"))
  (unless tape-alphabet (error "tape alphabet missing"))
  (unless start-state (error "start state missing"))
  (unless accept-state (error "accept state missing"))
  (unless reject-state (error "reject state missing"))
  (unless transition-fun (error "transition-fun missing"))
  `(gen-tm-fn  :name ',name
	       :states ',states
	       :alphabet ',alphabet
	       :tape-alphabet ',tape-alphabet
	       :start-state ',start-state
	       :accept-state ',accept-state
	       :reject-state ',reject-state
	       :transition-fun ',transition-fun))


#|
(gen-tm
 :name testxxxxxxxxxxxxxxxxxxxxxtm
 :states (q0 q1 q2)
 :alphabet (#\1 #\2)
 :tape-alphabet (#\1 #\2 #\4 nil)
 :start-state q0
 :accept-state q1
 :reject-state q2
 :transition-fun  (((q0 #\1) . (q0 #\2 R))
		   ((q0 #\2) . (q0 #\4 R))
		   ((q0 nil) . (q1 nil R))))
|#

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


(defun remove-forward-nils (xs)
  (cond ((and (consp xs)
	      (equal (car xs) nil)) (remove-forward-nils (cdr xs)))
	(t xs)))
	 
(defun prefixp (exp seq)
  (cond ((endp exp) t)
	((endp seq) nil)
	(t (and (equal (car exp) (car seq))
		(prefixp (cdr exp) (cdr seq))))))

(check= (prefixp '(1) '(1 2 3)) t)


(defun check-tm-output (f1 expected w)
  (let* ((tm1 (eval (with-open-file (infile f1) (read infile))))
	 (p (if (consp tm1)
		(format t "[~%~A ACCEPTED~%" (car tm1))
	      nil))
	 (res (runtm w (cdr tm1))))
    ;;start including output from here
    ;;check if ended in accept state and prefix of left tape matches the expected output
    
    (if (and (equal (car res) t)
	     (prefixp expected (remove-forward-nils (cdr res))))
        (format t "Passed test case]")
      (format t "Failed test case]"))))



(defun query-equivalence (tm1-name tm2-name)
  (let (
        ;(res (query-alphabet-equal dfa1-name dfa2-name))
	(dn (gen-symb "~a-wordp" tm1-name))
	(tm1 (gen-symb-const tm1-name))
	(tm2 (gen-symb-const tm2-name)))
    (let ((res (itest?-query
                `acl2s::(=> (,dn w)
                            (== (runtm-100 ,tm1 w)
                                (runtm-100 ,tm2 w))))))
      (if (car res)
            (cons nil (format nil "Transition function error. The following words
  were misclassified :~% ~a" (mapcar #'cadar (car (cdr res)))))
  (gen-symb "~a-state" tm2-name)))
          (cons t (format nil "~a is correct." tm2-name))))

#|
(query-equivalence 'instructor-tm 'student-tm)

(test? (=> (instructor-tm-wordp w)
           (== (runtm-100  w *instructor-tm*)
               (runtm-100  w *student-tm*))))
|#
