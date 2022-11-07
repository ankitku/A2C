#|

 PETE: I modified Ankit's version to allow one to compare DFAs with
 different alphabets and sketched out aspects of the user interface,
 i.e., how a user defines DFAs and also how one can automatically test
 and automate the reasoning of equivalence of DFAs.

 Here are some roughly written todos: 

 1. Write a macro that generates all of the stuff below.

 Something like

 (gen-dfa
  :name           *dfa1*
  :states         (even odd)
  :alphabet       (0 1)
  :start          even
  :accept         (odd)
  :transition-fun ((even 0 even)
    	           (even 1 odd)
 	           (odd  0 odd)
 	           (odd  1 even)))

 will do the following.

 A. Check that name is a new name, types, that transitions is
    complete and unambiguous, etc.

 B. Generate all the data, function definitions. 

 2. Define a generic dfa recognizer.

 The problem right now is that a user will have to define run-dfa on
 their own because the states, etc can be different. So, a generic
 version may allow any atoms, or symbols, or whatever as states and
 similarly for elements. Then the dfa-specific types get automatically
 generated. Make sure you can compare 2 DFAs that are supposed to
 accept the same language but have different states and transitions
 with the user only having to define the dfa, as in the defconst
 below. 

 From an implementation point of view, you can do all of this in
 ACL2s. See defunc.lisp and definec.lisp for examples, or you can do
 this in lisp using the ACL2s interface functions and the z3 code and
 ccg are good examples of how to do that. I would go this route. So,

 define a lisp function gen-dfa that takes input as shown above, does
 checking in lisp and generates the appropriate acl2s-events. You can
 turn that into an ACL2s function.


|#

; This is a supertype of DFAs. One can change some of the data
; definition, eg, one could allow states to be numbers or lists or
; whatever

(in-package "ACL2S")

(defdata state          var)
(defdata states         (listof state))
(defdata element        all)
(defdata word           (listof element))
(defdata alphabet       word) 
(defdata t-domain       (list state element))
(defdata transition-fun (alistof t-domain state))

(check= (statep 'even) t)
(check= (elementp 1)   t)
(check= (transition-funp  '(((even 1) . odd))) t)


(defdata dfa (list states         ;all states
                   alphabet       ;alphabet
                   transition-fun ;transition function
                   state          ;start state
                   states         ;accepting states
                   ))

(definecd dfa-states (d :dfa) :states
  (car d))

(definecd dfa-alphabet (d :dfa) :alphabet
  (second d))

(definecd dfa-trans (d :dfa) :transition-fun
  (third d))

(definecd dfa-start (d :dfa) :state
  (fourth d))

(definecd dfa-accept (d :dfa) :states
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

(definecd apply-trans (trans :transition-fun st :state el :element) :state
  (cond ((endp trans) st)
	((== (caar trans) (list st el))
         (cdar trans))
	(t (apply-trans (cdr trans) st el))))


(definecd run-dfa-help (s :state trans :transition-fun w :word) :state
  (if (endp w)
      s
    (run-dfa-help (apply-trans trans s (car w))
		  trans
		  (cdr w))))

(definecd run-dfa (m :dfa w :word) :bool
  (b* ((trans  (dfa-trans m))
       (start  (dfa-start m))
       (accept (dfa-accept m)))
    (in (run-dfa-help start trans w) accept)))
  

;; utility functions
(definecd subset (a :tl b :tl) :bool
  (cond ((endp a) t)
	((in (car a) b) (subset (cdr a) b))
	(t nil)))

(check= (subset '(1 1 3) '(1 2 3)) t)

(defdata trans-comps (cons states word))
(definecd get-trans-components (trans :transition-fun acc :trans-comps) :trans-comps
  (cond ((endp trans) acc)
	(t (get-trans-components (cdr trans)
				 (cons (cons (caaar trans)
					     (cons (cdar trans)
						   (car acc)))
				       (cons (cadaar trans)
					     (cdr acc)))))))
