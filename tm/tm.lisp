(in-package "ACL2S")
(include-book "match")

(defdata state          var)
(defdata states         (listof state))
(defdata elem           (oneof character var))
(defdata tape-elem      (oneof character var nil))
(defdata word           (listof elem))
(defdata tape-word      (listof tape-elem))
(defdata alphabet       word)
(defdata tape-alphabet  tape-word)
(defdata direction      (oneof 'L 'R))
(defdata t-domain       (list state tape-elem))
(defdata t-range        (list state tape-elem direction))
(defdata transition-fun (alistof t-domain t-range))
(defdata lot-range      (listof t-range))

(check= (statep 'even) t)
(check= (tape-elemp '#\() t)
(check= (t-domainp '(q0 a)) t)
(check= (t-rangep '(q0 b R)) t)
(check= (transition-funp  '(((q0 #\() . (q0 #\) R))
			    ((q0 #\)) . (q0 #\( L)))) t)


(defdata tm  (list states         ;all states
                   alphabet       ;alphabet
		   tape-alphabet  ;alphabet
                   transition-fun ;transition function
                   state          ;start state
                   state          ;accept state
		   state          ;reject state
                   ))

(definec tm-states (d :tm) :states
  (car d))

(definec tm-alphabet (d :tm) :alphabet
  (second d))

(definec tm-tape-alphabet (d :tm) :tape-alphabet
  (third d))

(definec tm-trans (d :tm) :transition-fun
  (fourth d))

(definec tm-start (d :tm) :state
  (fifth d))

(definec tm-accept (d :tm) :state
  (sixth d))

(definec tm-reject (d :tm) :state
  (seventh d))


(defdata tape (list state tape-alphabet tape-alphabet))

(defthm tape-condition
  (implies (tapep m)
	   (t-domainp (list (car m)
			    (car (third m))))))

;;left | right-tape
;;_ _ _ _ _ _ _ _ _
;;      ^
;;      | head is printed to the left of the first element of right tape
;; note : left is stored as a reverse list

(set-ignore-ok t)

(definecd tmstep (m :tape trx :transition-fun) :tape
  :skip-tests t
  (cond ((endp trx) m)
	((equal (list (first  m)
		      (car (third m)))
		(caar trx))
	 (let ((left (second m))
	       (right (third m))
	       (next-state     (first (cdar trx)))
	       (next-tape-elem (second (cdar trx)))
	       (dir            (third (cdar trx))))
	   (if (equal dir 'L)
	       `(,next-state
		 ,(cdr left)
		 ,(cons (car left)
			(cons next-tape-elem (cdr right))))
	     `(,next-state
	       ,(cons next-tape-elem left)
	       ,(cdr right)))))
	(t (tmstep m (cdr trx)))))


(definec runtm-help (n :nat m :tape tm :tm ) :tape
  :skip-tests t
  (declare (xargs :measure n))
  (let ((m2 (tmstep m (tm-trans tm))))
    (cond ((zerop n) m2)
	  (t (runtm-help (- n 1) m2 tm)))))


(definec runtm-100 (input :tape-word tm :tm) :tape
  (runtm-help 100 (list (tm-start tm) nil input) tm))



(definec acceptedp (input :tape-word tm :tm) :boolean
  (equal (car (runtm-100 input tm))
	 (tm-accept tm)))


(definec remove-beginnils (l :tl) :tl
  (if (endp l)
      '()
    (if (equal (car l) nil)
	(remove-beginnils (cdr l))
      l)))
      
(definec remove-endnils (l :tl) :tl
  (reverse (remove-beginnils (reverse l))))


(defconst *tm-test*
  (list '(q0 q1 q2)
        '( #\1 #\2 )
	'( #\1 #\2 nil )
	'(((q0 #\1) . (q0 #\2 R))
	  ((q0 #\2) . (q0 #\1 R))
	  ((q0 nil) . (q1 nil R)))
	'q0
	'q1
	'q2))


(defconst *tm-test2*
  (list '(q0 q1 q2)
        '( #\1 #\2 )
	'( #\1 #\2 nil )
	'(((q0 #\1) . (q0 #\2 R))
	  ((q0 #\2) . (q0 #\2 R))
	  ((q0 nil) . (q1 nil R)))
	'q0
	'q1
	'q2))



;; Property based testing
(definec gen-word0n1n2np (n :nat) :word
  (append (make-list 3 :initial-element #\0)
	  (make-list 3 :initial-element #\1)
	  (make-list 3 :initial-element #\2)))

(defconst *tm-0n1n2n-recognizer*
    (list '(q0 q1 q2 q3 q4)
        '( #\0 #\1 #\2 #\3)
	'( #\0 #\1 #\2 #\3 nil )
	'(((q0 #\0) . (q1 #\3 R))
	  ((q0 #\3) . (q0 #\3 R))
	  ((q0 #\1) . (q7 #\1 R))
	  ((q0 #\2) . (q7 #\2 R))
	  ((q1 #\0) . (q1 #\0 R))
	  ((q1 #\1) . (q2 #\3 R))
	  ((q1 #\3) . (q1 #\3 R))
	  ((q2 #\1) . (q2 #\1 R))
	  ((q2 #\2) . (q3 #\3 L))
	  ((q2 #\3) . (q2 #\3 R))
	  ((q3 #\3) . (q3 #\3 L))
	  ((q3 #\2) . (q7 #\2 L))
	  ((q3 #\1) . (q3 #\1 L))
	  ((q3 #\0) . (q3 #\0 L))
	  ((q3 nil) . (q0 nil R))
	  ((q0 nil) . (q5 nil R)))
	'q0
	'q5
	'q7))


;;faker, always accepts
(defconst *tm-0n1n2n-faker*
    (list '(q0 q1 q2 q3 q4)
        '( #\0 #\1 #\2 #\3)
	'( #\0 #\1 #\2 #\3 nil )
	'(((q0 #\0) . (q0 #\3 R))
	  ((q0 #\1) . (q0 #\3 R))
	  ((q0 #\2) . (q0 #\1 R))
	  ((q0 nil) . (q5 nil R)))
	'q0
	'q5
	'q7))

(check= (tmp *tm-test*) t)
(check= (tmp *tm-0n1n2n-recognizer*) t)
(check= (tmp *tm-0n1n2n-faker*) t)


(runtm-100 '(#\1 #\2 #\2 #\1 #\1) *tm-test*)

(runtm-100 '(#\0 #\1 #\2) *tm-0n1n2n-recognizer*)
(runtm-100 '(#\0 #\1 #\1 #\2) *tm-0n1n2n-recognizer*)
(runtm-100 '(#\0 #\0 #\1 #\1 #\2) *tm-0n1n2n-recognizer*)
(runtm-100 '(#\0 #\0 #\1 #\1 #\2 #\2) *tm-0n1n2n-recognizer*)


;;Checks if numbers of the form 0^n1^n2^n are accepted by the submitted TM

;;Valid example

;;T
(test?  (=> (natp n) (wordp w) (not (equal (gen-word0n1n2np n) w)))
	    (acceptedp (gen-word0n1n2np n) *tm-0n1n2n-recognizer*)))

;;F
(test?  (=> (natp n)
	    (not (acceptedp (cons #\2 (gen-word0n1n2np n)) *tm-0n1n2n-recognizer*))))





;;Incorrect example
(test?  (=> (natp n)
	    (acceptedp (gen-word0n1n2np n) *tm-0n1n2n-faker*)))

(test?  (=> (natp n)
	    (not (acceptedp (cons #\2 (gen-word0n1n2np n)) *tm-0n1n2n-faker*))))




(include-book "interface/top")

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
	 (p-fp (gen-sym-pred p-f)))
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
    (acl2s-event `acl2s::(defdata ,name (list ,p-states ,p-ab ,p-tape-ab ,p-f ,p-state ,p-state ,p-state)))
    (unless (tmp `acl2s::(,states ,alphabet ,tape-alphabet ,transition-fun ,start-state ,accept-state ,reject-state))
      (error-and-reset "incorrect TM" p-state))))




(defun gen-tm-fn (&key name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
  (let* ((df `acl2s::(,states ,alphabet ,tape-alphabet ,transition-fun ,start-state ,accept-state ,reject-state)))
    (mk-tm-events name states alphabet tape-alphabet start-state accept-state reject-state transition-fun)
    (cons name df)))



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


(defun remove-forward-nils (xs)
  (cond ((and (consp xs)
	      (equal (car xs) nil)) (remove-forward-nils (cdr xs)))
	(t xs)))
	 
(defun prefixp (exp seq)
  (cond ((endp exp) t)
	((endp seq) nil)
	(t (and (equal (car exp) (car seq))
		(prefixp (cdr exp) (cdr seq))))))

(prefixp '(1) '(1 2 3))


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


(defun main (flist)
  (quiet-mode-on)
  (setq steps 1000)  
  (let* ((w (coerce (third flist) 'list))
	 (exp (coerce (second flist) 'list)))
    (check-tm-output (first flist) exp w))
    (terpri)
    (sb-ext:exit))


(save-exec "tm_run_exec" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::main (cdr sb-ext:*posix-argv*))' --disable-debugger")
u
