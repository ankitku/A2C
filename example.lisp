(in-package "ACL2S")


(defdata state          var)
(defdata states         (listof state))
(defdata element        all)
(defdata word           (listof element))
(defdata alphabet       word) 
(defdata t-domain       (list state element))
(defdata transition-fun (map t-domain state))

(check= (statep 'even) t)
(check= (elementp 1)   t)
(check= (transition-funp  '(((even 1) . odd))) t)


(defdata dfa (list states         ;all states
                   alphabet       ;alphabet
                   transition-fun ;transition function
                   state          ;start state
                   states         ;accepting states
                   ))

(definec dfa-states (d :dfa) :states
  (car d))

(definec dfa-alphabet (d :dfa) :alphabet
  (second d))

(definec dfa-trans (d :dfa) :transition-fun
  (third d))

(definec dfa-start (d :dfa) :state
  (fourth d))

(definec dfa-accept (d :dfa) :states
  (fifth d))

(defconst *dfa-test*
  (list '(even odd)
        '(0 1)
        '(((even 0) . even)
	  ((even 1) . odd)
	  ((odd  0) . odd)
	  ((odd  1) . even))
        'even
        '(odd)))

(check= (dfap *dfa-test*) t)

(definec apply-trans (trans :transition-fun st :state el :element) :state
  (cond ((endp trans) st)
	((== (caar trans) (list st el))
         (cdar trans))
	(t (apply-trans (cdr trans) st el))))


(definec run-dfa-help (s :state trans :transition-fun w :word) :state
  (if (endp w)
      s
    (run-dfa-help (apply-trans trans s (car w)) trans (cdr w))))

(definec run-dfa (m :dfa w :word) :state
  (b* ((trans  (dfa-trans m))
       (start  (dfa-start m)))
    (run-dfa-help start trans w)))

(definec accept-dfa (m :dfa w :word) :bool
  (in (run-dfa m w)
      (dfa-accept m)))

;; utility functions
(definec subset (a :tl b :tl) :bool
  (cond ((endp a) t)
	((in (car a) b) (subset (cdr a) b))
	(t nil)))

(check= (subset '(1 1 3) '(1 2 3)) t)







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

(defun gen-symb-const (x)
  (gen-symb "*~a*" x))

(gen-symb-const 'dfa1)

(defun gen-sym-pred (x)
  (gen-symb "~ap" x))

(gen-sym-pred 'dfa)

;;------------------------------------------------------------------------
;; DFA make/reset events generation
;;------------------------------------------------------------------------

(defun reset-history ()
  (acl2s-event `acl2s::(ubt 1)))

(defun reset-dfa-def (d)
  (acl2s-event `acl2s::(ubt ',(gen-sym-pred d))))

(defun error-and-reset (msg def)
  (progn (reset-dfa-def def)
	 (error (format nil "[~a]" msg))
         (sb-ext:exit)))


;; generates defdata events while also checking if input is actually a DFA
(defun mk-dfa-events (name states alphabet start accept transition-fun)
  (let* ((d-state (gen-symb "~a-state" name))
	 (d-states (gen-symb "~a-states" name))
	 (d-elem (gen-symb "~a-element" name))
	 (d-word (gen-symb "~a-word" name))
	 (d-ab (gen-symb "~a-alphabet" name))
	 (d-tdom (gen-symb "~a-t-domain" name))
	 (d-f (gen-symb "~a-transition-function" name))
	 (d-fp (gen-sym-pred d-f))
	 (dfa-name (gen-symb-const name)))
    (acl2s-event `acl2s::(defdata ,d-state  (enum (quote ,states))))
    (unless (statesp `acl2s::,states) (error-and-reset "incorrect states" d-state))
    (acl2s-event `acl2s::(defdata ,d-states (listof ,d-state)))
    (acl2s-event `acl2s::(defdata ,d-elem  (enum (quote ,alphabet))))
    (acl2s-event `acl2s::(defdata ,d-word (listof ,d-elem)))
    (acl2s-event `acl2s::(defdata ,d-ab ,d-word))
    (unless (alphabetp `acl2s::,alphabet) (error-and-reset "incorrect alphabet" d-state))
    (unless (in start `acl2s::,states) (error-and-reset "incorrect start state" d-state))
    (unless (subset `acl2s::,accept `acl2s::,states)
      (error-and-reset "incorrect accept states" d-state))
    (acl2s-event `acl2s::(defdata ,d-tdom (list ,d-state ,d-elem)))
    (acl2s-event `acl2s::(defdata ,d-f (map ,d-tdom ,d-state)))
    (unless (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun))))
       (error-and-reset "incorrect transition function" d-state))
    (acl2s-event `acl2s::(defconst ,dfa-name (list ',states ',alphabet ',transition-fun ',start ',accept)))
    (unless (not (dfap dfa-name))
	(error-and-reset "incorrect dfa" d-state))))



(defun gen-dfa-fn (&key name states alphabet start accept transition-fun)
 (let* ((df `acl2s::(,states ,alphabet ,transition-fun ,start ,accept)))
    (mk-dfa-events name states alphabet start accept transition-fun)
    (cons name df)))


(defun convert-trx-fun (tf)
  (if (endp tf)
      nil
    (cons (cons (list (first (car tf))
		      (second (car tf)))
		(third (car tf)))
	  (convert-trx-fun (cdr tf)))))


(defmacro gen-dfa (&key name states alphabet start accept transition-fun)
  (unless name (error "name missing"))
  (unless states (error "states missing"))
  (unless alphabet (error "alphabet missing"))
  (unless start (error "start missing"))
  (unless accept (error "accept missing"))
  (unless transition-fun (error "transition-fun missing"))
  (let ((ctf (convert-trx-fun transition-fun)))
  `(gen-dfa-fn :name ',name
	       :states ',states
	       :alphabet ',alphabet
	       :start ',start
	       :accept ',accept
	       :transition-fun ',ctf)))

;;------------------------------------------------------------------------
;; DFA check events generation
;;------------------------------------------------------------------------

(defun query-alphabet-equal (dfa1-name dfa2-name)
  (let ((da1 (gen-symb "~a-alphabet" dfa1-name))
	(da2 (gen-symb "~a-alphabet" dfa2-name)))
    (acl2s-event
     `acl2s::(defdata-equal-strict ,da1 ,da2))))

(defun query-equivalence (dfa1-name dfa2-name)
  (let ((res (query-alphabet-equal dfa1-name dfa2-name))
	(dn (gen-symb "~a-wordp" dfa1-name))
	(dfa1 (gen-symb-const dfa1-name))
	(dfa2 (gen-symb-const dfa2-name)))
    (if (car res)
	(error-and-reset "incorrect alphabet provided"
			 (gen-symb "~a-state" dfa2-name))
      (itest?-query
       `acl2s::(=> (,dn w)
		   (equal (accept-dfa ,dfa1 w)
			  (accept-dfa ,dfa2 w)))))))

;;------------------------------------------------------------------------
;; PAPER EXAMPLES
;;------------------------------------------------------------------------


(gen-dfa
 :name           instr-dfa
 :states         (even odd)
 :alphabet       (0 1)
 :start          even
 :accept         (odd)
 :transition-fun ((even 0 even)
		  (even 1 odd)
		  (odd  0 odd)
		  (odd  1 even)))


(gen-dfa
 :name           stud-dfa1
 :states         (e1 e2 o1 o2)
 :alphabet       (1)
 :start          e1   
 :accept         (o1 o2)
 :transition-fun ((e1 0 e1)
		  (e1 1 o1)
		  (e2 0 e2)
		  (e2 1 o2)
		  (o1 0 o2)
		  (o1 1 e2)
		  (o2 0 o1)
		  (o2 1 o1)))


(gen-dfa
 :name           stud-dfa2
 :states         (e1 e2 o1 o2)
 :alphabet       (0 1 2)
 :start          e1   
 :accept         (o1 o2)
 :transition-fun ((e1 0 e1)
		  (e1 1 o1)
		  (e2 0 e2)
		  (e2 1 o2)
		  (o1 0 o2)
		  (o1 1 e2)
		  (o2 0 o1)
		  (o2 1 o1)))

(query-equivalence 'instr-dfa 'stud-dfa2)

(gen-dfa
 :name           stud-dfa3
 :states         (e1 e2 o1 o2)
 :alphabet       (0 1)
 :start          e1   
 :accept         (o1 o2)
 :transition-fun ((e1 0 e1)
		  (e1 1 o1)
		  (e2 0 e2)
		  (e2 1 e2)
		  (o1 0 o2)
		  (o1 1 e2)
		  (o2 0 o1)
		  (o2 1 e1)))

(query-equivalence 'instr-dfa 'stud-dfa3)

(run-dfa *stud-dfa3* '(1 1 1))

(gen-dfa
 :name  stud-dfa4
 :states  (e1 e2 o1 o2)
 :alphabet       (0 1)
 :start          e1   
 :accept         (o1 o2)
 :transition-fun ((e1 0 e1)
		  (e1 1 o1)
		  (e2 0 e2)
		  (e2 1 o2)
		  (o1 0 o2)
		  (o1 1 e2)
		  (o2 0 o1)
		  (o2 1 e1)))

(query-equivalence 'instr-dfa 'stud-dfa4)


;; f1 is instructor file (minimal and correct).
;; f2 is student file (may be buggy)
(defun check-dfa-input-run (f1 f2 w)
  (let* ((dfa1 (eval (with-open-file (infile f1) (read infile))))
	 (dfa2 (eval (with-open-file (infile f2) (read infile))))
	 (dfa2st (gen-symb "~a-state" (first dfa2))))
    ;; Check if student is using same alphabet
    (unless (and (subset (third dfa1) (third dfa2))
		 (subset (third dfa2) (third dfa1)))
      (error-and-reset "incorrect alphabet provided"
		       (gen-symb "~a-state" (first dfa2))))
    ;;we find state-word maps of dfa2, then map those states to dfa1 (assumed minimal)
    (if (equal (run-dfa (cdr dfa1) w)
	       (run-dfa (cdr dfa2) w))
	(print (format t "[Passed test case]"))
      (print (format t "[Failed test case]")))
    ))


;; f1 is instructor file (minimal and correct).
;; f2 is student file (may be buggy)
(defun check-dfa-equivalence (f1 f2)
  (let* ((dfa1 (eval (with-open-file (infile f1) (read infile))))
	 (dfa2 (eval (with-open-file (infile f2) (read infile))))
	 (dfa2st (gen-symb "~a-state" (first dfa2))))
    (let ((res (query-equivalence (car dfa1) (cdr dfa1) (car dfa2 )(cdr dfa2))))
      (reset-dfa-def dfa2st)
      (if (car res)
	  (print (format t "[Following words do not lead to the correct state :~a]" (cdr res)))
	(print (format t "[Passed equivalence check!]")))
      )))









