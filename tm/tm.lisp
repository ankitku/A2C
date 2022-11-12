(in-package "ACL2S")

(defdata state          var)
(defdata states         (listof state))
(defdata elem           (oneof nat character var))
(defdata tape-elem      (oneof nat character var nil))
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
			    ((q0 #\)) . (q0 #\( L))))
	t)


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

(definecd left-of-head (tape :tape) :tape-alphabet
  (reverse (second tape)))

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


(definec run-tm (input :tape-word tm :tm) :tape
  (runtm-help 100 (list (tm-start tm) nil input) tm))

(definec accept-tm (input :tape-word tm :tm) :boolean
  (equal (car (run-tm input tm))
	 (tm-accept tm)))

(definec remove-initial-nils (l :tl) :tl
  (if (endp l)
      '()
    (if (equal (car l) nil)
	(remove-initial-nils (cdr l))
      l)))

(defconst *tm-test*
  (list '(q0 q1 q2)
        '( #\1 #\0 )
	'( #\1 #\0 nil )
	'(((q0 #\1) . (q0 #\0 R))
	  ((q0 #\0) . (q0 #\1 R))
	  ((q0 nil) . (q1 nil R)))
	'q0
	'q1
	'q2))


(defconst *tm-test2*
  (list '(q0 q1 q2)
        '( #\1 #\0 )
	'( #\1 #\0 nil )
	'(((q0 #\1) . (q0 #\0 R))
	  ((q0 #\0) . (q0 #\0 R))
	  ((q0 nil) . (q1 nil R)))
	'q0
	'q1
	'q2))


;; utility functions
(definec subset (a :tl b :tl) :bool
  (cond ((endp a) t)
	((in (car a) b) (subset (cdr a) b))
	(t nil)))

(check= (subset '(1 1 3) '(1 2 3)) t)



#|

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


(run-tm '(#\1 #\2 #\2 #\1 #\1) *tm-test*)

(run-tm '(#\0 #\1 #\2) *tm-0n1n2n-recognizer*)
(run-tm '(#\0 #\1 #\1 #\2) *tm-0n1n2n-recognizer*)
(run-tm '(#\0 #\0 #\1 #\1 #\2) *tm-0n1n2n-recognizer*)
(run-tm '(#\0 #\0 #\1 #\1 #\2 #\2) *tm-0n1n2n-recognizer*)


;;Checks if numbers of the form 0^n1^n2^n are accepted by the submitted TM

;;Valid example


(test?  (=> (natp n) (wordp w) (not (equal (gen-word0n1n2np n) w)))
	    (accept-tm (gen-word0n1n2np n) *tm-0n1n2n-recognizer*)))

;;F
(test?  (=> (natp n)
	    (not (accept-tm (cons #\2 (gen-word0n1n2np n)) *tm-0n1n2n-recognizer*))))




;;Incorrect example
(test?  (=> (natp n)
	    (accept-tm (gen-word0n1n2np n) *tm-0n1n2n-faker*)))

(test?  (=> (natp n)
	    (not (accept-tm (cons #\2 (gen-word0n1n2np n)) *tm-0n1n2n-faker*))))
|#
