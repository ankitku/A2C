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
