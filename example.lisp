(in-package "ACL2S")

(include-book "interface/top")

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
	 (cons nil (format nil "[~a]" msg))))


(defun query-function-total (elem-def state-def txf)
  (let ((es (gen-sym-pred elem-def))
	(ss (gen-sym-pred state-def))
        (domain (strip-cars txf)))
    (itest?-query
       `acl2s::(=> (and (,es e) (,ss s))
		   (in (list s e) ',domain)))))


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
    (if (not (statesp `acl2s::,states))
	(error-and-reset "incorrect states" d-state)
      (progn (acl2s-event `acl2s::(defdata ,d-states (listof ,d-state)))
	     (acl2s-event `acl2s::(defdata ,d-elem  (enum (quote ,alphabet))))
	     (acl2s-event `acl2s::(defdata ,d-word (listof ,d-elem)))
	     (acl2s-event `acl2s::(defdata ,d-ab ,d-word))
	     (if (not (in start `acl2s::,states))
		 (error-and-reset "incorrect start state" d-state)
	       (progn
		 (if (not (subset `acl2s::,accept `acl2s::,states))
		     (error-and-reset "incorrect accept states" d-state)
		   (progn 
		     (acl2s-event `acl2s::(defdata ,d-tdom (list ,d-state ,d-elem)))
		     (acl2s-event `acl2s::(defdata ,d-f (map ,d-tdom ,d-state)))
		     (let ((res (query-function-total d-elem d-state transition-fun)))
		       (if (car res)
			   (error-and-reset (format nil "transition function is not defined for inputs : ~a" (cdr res)) d-state)
			 (if (not (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun)))))
			     (error-and-reset "incorrect transition function" d-state)
			   (progn (acl2s-event `acl2s::(defconst ,dfa-name (list ',states ',alphabet ',transition-fun ',start ',accept)))
				  `acl2s::(,states ,alphabet ,transition-fun ,start ,accept)))))))))))))



(defun gen-dfa-fn (&key name states alphabet start accept transition-fun)
  (mk-dfa-events name states alphabet start accept transition-fun))

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
	(error-and-reset "Incorrect alphabet provided."
			 (gen-symb "~a-state" dfa2-name))
      (let ((res (itest?-query
                  `acl2s::(=> (,dn w)
                              (equal (accept-dfa ,dfa1 w)
                                     (accept-dfa ,dfa2 w))))))
        (if (car res)
            (cons nil (format nil "Transition function error. The following words
  were misclassified :~% ~a" (mapcar #'cadar (car (cdr res)))
  (gen-symb "~a-state" dfa2-name)))
          (cons t (format nil "~a is correct." dfa2-name)))))))

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



;; load acl2s grading infrastructure
(load "autograder_raw_code.lsp")

(defun run-tests ()
  ;; Load the student submission
  (let ((rr (with-open-file (s "student.lisp")
		(read s))))
    (grade "test-valid-dfa"
	   10
	   (eval rr)))

  ;; Grade form to grade student submission
  (grade "test-equivalence"          ;; test case name
	 10                          ;; points allocated to this test
	 (query-equivalence 'instr-dfa 'student-dfa))  ;; should return (bool . string)
  (finish-grading))


;; the following command is necessary to create an executable
;; named run_autograder according to gradescope specification
(save-exec "run_autograder" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::run-tests)' --disable-debugger")


