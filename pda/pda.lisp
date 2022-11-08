(in-package "ACL2S")
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)

(defdata state                var)
(defdata states               (listof state))
(defdata element              (oneof character var nat :e))
(defdata word                 (listof element))
(defdata-alias alphabet       word)
(defdata-alias stack-alphabet word)
(defdata-alias stack          word)
(defdata t-domain             (list state element element))
(defdata t-range              (listof (list state element)))
(defdata transition-fun       (alistof t-domain t-range))

(check= (statep 'even) t)
(check= (elementp '#\() t)
(check= (t-domainp '(q0 a z0)) t)
(check= (t-rangep '((q0 #\( ))) t)
(check= (transition-funp  '(((q0 #\( #\( ) . ((q0 #\( )))
			    ((q0 #\( z0  ) . ((q0 #\( )))))
        t)

(check= (transition-funp '(((q0 :e :e) . ((q1 b)))
                   ((q1 0   :e) . ((q1 0)))
                   ((q1 1   0)   . ((q2 :e)))
                   ((q2 1   0)   . ((q2 :e)))
                   ((q2 :e b)   . ((q3 :e)))))
        t)

(definecd word-car (w :word) :element
  (match w
    (() :e)
    ((e . &) e)))

(defdata pda (list states         ;all states
                   alphabet       ;alphabet
		   stack-alphabet ;alphabet
                   transition-fun ;transition function
                   state          ;start state
		   states         ;accepting states
                   ))

(definecd pda-states (d :pda) :states
  (car d))

(definecd pda-alphabet (d :pda) :alphabet
  (second d))

(definecd pda-stack-alphabet (d :pda) :stack-alphabet
  (third d))

(definecd pda-trans (d :pda) :transition-fun
  (fourth d))

(definecd pda-start (d :pda) :state
  (fifth d))

(definecd pda-accept (d :pda) :states
  (sixth d))

(defconst *pda-test*
  (list '(q0 q1 q2)
        '(#\( #\) )
	'(z0  #\( )
	'(((q0 :e :e ) . ((q1 z0  )))
          ((q1 #\( :e ) . ((q1 #\( )))
	  ((q1 #\) #\( ) . ((q1 :e)))
	  ((q1 :e z0 )  . ((q2 :e) (q0 :e))))
	'q0
	'(q2)))


(check= (pdap *pda-test*) t)

(defdata [statexstackxword] (listof (list state stack word)))

(definecd pda-trx-lookup (trans :transition-fun dom :t-domain) :t-range
  (match trans
    (() '())
    (((!dom . val) . &) val)
    ((& . rst) (pda-trx-lookup rst dom))))

;;converts a list of statexelement pairs to a list of statexstack pairs
(definecd es->stks (rs :t-range stk :stack w :word) :[statexstackxword]
  (match rs
    (() '())
    (((s :e) . tl) (cons (list s (cdr stk) w)
                          (es->stks tl stk w)))
    (((s e) . tl) (cons (list s (cons e (cdr stk)) w)
                        (es->stks tl stk w)))))

(defthm app-[statexstackxword]
  (=> (and ([statexstackxword]p r) ([statexstackxword]p s))
      ([statexstackxword]p (append r s))))

(definecd pdastep (trans :transition-fun in :[statexstackxword])
  :[statexstackxword]
  (match in
    (() '())
    (((s stk w) . tl) (append (es->stks (pda-trx-lookup trans `(,s ,(word-car w) ,(word-car stk)))
                                        stk
                                        (cdr w)) ;; one letter was used up
                              ;;stack epsilon transition
                              (es->stks (pda-trx-lookup trans `(,s ,(word-car w) :e))
                                        (cons :e stk)
                                        (cdr w))
                              ;;word epsilon transition
                              (es->stks (pda-trx-lookup trans `(,s :e ,(word-car stk)))
                                        stk
                                        w) ;;word remains unchanged
                              ;;stack and word eps transition
                              (es->stks (pda-trx-lookup trans `(,s :e ,(word-car stk)))
                                        (cons :e stk)
                                        w)
                              (pdastep trans tl)))))

(definecd accepted (res :[statexstackxword] accept-states :states) :boolean
  (if (endp res)
      nil
    (or (and (endp (third (car res))) ;;no remaining word
             (in (first (car res)) accept-states)) ;;accept state reached
        (accepted (cdr res) accept-states))))

(property rem-dups-statexstackxword (res :[statexstackxword])
          ([statexstackxword]p (remove-duplicates-equal res)))
  
(definecd run-steps (n :nat pda :pda sstws :[statexstackxword]) :boolean
  (cond
   ((== n 0) nil)
   ((accepted sstws (pda-accept pda)) t)
   (t (run-steps (1- n) pda (remove-duplicates-equal (pdastep (pda-trans pda) sstws))))))

(definecd accept-pda (pda :pda w :word) :boolean
  (run-steps 100 pda `(,(list (pda-start pda) nil w))))

(check= (accept-pda *pda-test* '( #\( #\) )) t)
(check= (accept-pda *pda-test* '( #\( #\) #\( #\( #\) #\) #\( #\( #\( #\) #\) #\) )) t)
(check= (accept-pda *pda-test* '( #\( #\( )) nil)     
(check= (accept-pda *pda-test* '( #\( #\) #\( )) nil)     

;; utility functions
(definecd subset (a :tl b :tl) :bool
  (cond ((endp a) t)
	((in (car a) b) (subset (cdr a) b))
	(t nil)))

(check= (subset '(1 1 3) '(1 2 3)) t)

