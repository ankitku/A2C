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


(definecd run-dfa (s :state trans :transition-fun w :word) :state
  (if (endp w)
      s
    (run-dfa (apply-trans trans s (car w))
		  trans
		  (cdr w))))

(definecd accept-dfa (m :dfa w :word) :bool
  (b* ((trans  (dfa-trans m))
       (start  (dfa-start m))
       (accept (dfa-accept m)))
    (in (run-dfa start trans w) accept)))
  

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
