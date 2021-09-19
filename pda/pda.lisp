(in-package "ACL2S")

(defdata state          var)
(defdata states         (listof state))
(defdata element        (oneof character var nat nil))
(defdata word           (listof element))
(defdata alphabet       word)
(defdata stack-alphabet word)
(defdata-alias stack    word)
(defdata t-domain       (list state element element))
(defdata t-range        (listof (list state element)))
(defdata transition-fun (alistof t-domain t-range))

(check= (statep 'even) t)
(check= (elementp '#\() t)
(check= (t-domainp '(q0 a z0)) t)
(check= (t-rangep '((q0 #\( ))) t)
(check= (transition-funp  '(((q0 #\( #\( ) . ((q0 #\( )))
			    ((q0 #\( z0  ) . ((q0 #\( )))))
        t)

(check= (transition-funp '(((q0 nil nil) . ((q1 b)))
                   ((q1 0   nil) . ((q1 0)))
                   ((q1 1   0)   . ((q2 nil)))
                   ((q2 1   0)   . ((q2 nil)))
                   ((q2 nil b)   . ((q3 nil)))))
        t)


(defdata pda (list states         ;all states
                   alphabet       ;alphabet
		   stack-alphabet ;alphabet
                   transition-fun ;transition function
                   state          ;start state
		   states         ;accepting states
                   ))

(definec pda-states (d :pda) :states
  (car d))

(definec pda-alphabet (d :pda) :alphabet
  (second d))

(definec pda-stack-alphabet (d :pda) :stack-alphabet
  (third d))

(definec pda-trans (d :pda) :transition-fun
  (fourth d))

(definec pda-start (d :pda) :state
  (fifth d))

(definec pda-accept (d :pda) :states
  (sixth d))

(defconst *pda-test*
  (list '(q0 q1 q2)
        '(#\( #\) )
	'(z0  #\( )
	'(((q0 nil nil ) . ((q1 z0  )))
          ((q1 #\( nil ) . ((q1 #\( )))
	  ((q1 #\) #\( ) . ((q1 nil)))
	  ((q1 nil z0 )  . ((q2 nil) (q0 nil))))
	'q0
	'(q2)))


(check= (pdap *pda-test*) t)

(defdata res2 (listof (list state stack word)))

(definecd lookup (trans :transition-fun dom :t-domain) :t-range
  (cond ((endp trans) '())
        ((equal (caar trans) dom) (cdar trans))
        (t (lookup (cdr trans) dom))))


;;converts a list of statexelement pairs to a list of statexstack pairs
(definecd es->stks (rs :t-range stk :stack w :word) :res2
  (match rs
    (() '())
    (((s nil) . tl) (cons (list s (cdr stk) w)
                          (es->stks tl stk w)))
    (((s e) . tl) (cons (list s (cons e (cdr stk)) w)
                        (es->stks tl stk w)))))

(defthm app-res2
  (=> (and (res2p r) (res2p s))
      (res2p (append r s))))

(definecd pdastep (trans :transition-fun in :res2) :res2
  :timeout 600
  (match in
    (() '())
    (((s stk w) . tl) (append (es->stks (lookup trans `(,s ,(car w) ,(car stk)))
                                        stk
                                        (cdr w)) ;; one letter was used up
                              ;;stack epsilon transition
                              (es->stks (lookup trans `(,s ,(car w) ,nil))
                                        (cons nil stk)
                                        (cdr w))
                              ;;word epsilon transition
                              (es->stks (lookup trans `(,s nil ,(car stk)))
                                        stk
                                        w) ;;word remains unchanged
                              ;;stack and word eps transition
                              (es->stks (lookup trans `(,s nil ,(car stk)))
                                        (cons nil stk)
                                        w)
                              (pdastep trans tl)))))


(definecd accepted (res :res2 accept-states :states) :boolean
  (if (endp res)
      nil
    (or (and (endp (third (car res))) ;;no remaining word
             (in (first (car res)) accept-states)) ;;accept state reached
        (accepted (cdr res) accept-states))))
                 

(definecd run-steps (n :nat pda :pda in :res2) :boolean
  (cond
   ((== n 0) nil)
   ((accepted in (pda-accept pda)) t)
   (t (run-steps (1- n) pda (pdastep (pda-trans pda) in)))))

(skip-proofs
(definecd run-pda (pda :pda w :word) :boolean
  (run-steps 20 pda `(,(list (pda-start pda) nil w)))))


(check= (run-pda *pda-test* '( #\( #\) )) t)
(check= (run-pda *pda-test* '( #\( #\) #\( #\( #\) #\) #\( #\( #\( #\) #\) #\) )) t)
(check= (run-pda *pda-test* '( #\( #\( )) nil)     
(check= (run-pda *pda-test* '( #\( #\) #\( )) nil)     

;; utility functions
(definec subset (a :tl b :tl) :bool
  (cond ((endp a) t)
	((in (car a) b) (subset (cdr a) b))
	(t nil)))

(check= (subset '(1 1 3) '(1 2 3)) t)


;; generates defdata events while also checking if input is actually a PDA
(defun mk-pda-events (name states alphabet stack-alphabet
			   start-state accept-states transition-fun)
  (let* ((p-state (gen-symb "~a-state" name))
	 (p-states (gen-symb "~a-states" name))
	 (p-elem (gen-symb "~a-element" name))
	 (p-word (gen-symb "~a-word" name))
	 (p-ab (gen-symb "~a-alphabet" name))
	 (p-stk-elem (gen-symb "~a-stk-element" name))
	 (p-stk-word (gen-symb "~a-stk-word" name))
	 (p-stk-ab (gen-symb "~a-stk-alphabet" name))
	 (p-tdom (gen-symb "~a-t-domain" name))
	 (p-trange (gen-symb "~a-t-range" name))
	 (p-f (gen-symb "~a-transition-function" name))
	 (p-fp (gen-sym-pred p-f))
         (pda-name (gen-symb-const name)))
    (acl2s-event `acl2s::(defdata ,p-state  (enum (quote ,states))))
    (unless (statesp `acl2s::,states) (error-and-reset "incorrect states" p-state))
    (acl2s-event `acl2s::(defdata ,p-states (listof ,p-state)))
    (acl2s-event `acl2s::(defdata ,p-elem  (enum (quote ,(cons nil alphabet)))))
    (acl2s-event `acl2s::(defdata ,p-word (listof ,p-elem)))
    (acl2s-event `acl2s::(defdata ,p-ab ,p-word))
    (acl2s-event `acl2s::(defdata ,p-stk-elem  (enum (quote ,(cons nil stack-alphabet)))))
    (acl2s-event `acl2s::(defdata ,p-stk-word (listof ,p-stk-elem)))
    (acl2s-event `acl2s::(defdata ,p-stk-ab ,p-stk-word))
    (unless (in start-state `acl2s::,states) (error-and-reset (format t "incorrect start state ~a" start-state) p-state))
    (unless (subset `acl2s::,accept-states `acl2s::,states)
      (error-and-reset "incorrect accept states" p-state))
    (acl2s-event `acl2s::(defdata ,p-tdom (list ,p-state ,p-elem ,p-stk-elem)))
    (acl2s-event `acl2s::(defdata ,p-trange (listof (list ,p-state ,p-stk-elem))))
    (acl2s-event `acl2s::(defdata ,p-f (alistof ,p-tdom ,p-trange)))
    (unless (second (acl2s-compute `acl2s::(,p-fp (quote ,transition-fun))))
       (error-and-reset "incorrect transition function" p-state))
    (acl2s-event `acl2s::(defdata ,name (list ,p-states ,p-ab ,p-stk-ab ,p-f
                                              ,p-state ,p-stk-elem ,p-states)))
    (acl2s-event `acl2s::(defconst ,pda-name (list ',states ',alphabet
    ',stack-alphabet ',transition-fun ',start-state ',accept-states)))
    (cons t (format nil "Legal PDA : ~a" `acl2s::(,states ,alphabet
    ,stack-alphabet ,transition-fun ,start-state ,accept-states)))))




(defun gen-pda-fn (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (let* ((df `acl2s::(,states ,alphabet ,stack-alphabet ,transition-fun ,start-state ,accept-states)))
    (mk-pda-events name states alphabet stack-alphabet start-state accept-states transition-fun)
    (cons name df)))

(defmacro gen-pda (&key name states alphabet stack-alphabet start-state accept-states transition-fun)
  (unless name (error "name missing"))
  (unless states (error "states missing"))
  (unless alphabet (error "alphabet missing"))
  (unless stack-alphabet (error "stack alphabet missing"))
  (unless start-state (error "start state missing"))
  (unless accept-states (error "accept states missing"))
  (unless transition-fun (error "transition-fun missing"))
  (let ((up-ab (cons nil alphabet)))
  `(gen-pda-fn :name ',name
	       :states ',states
	       :alphabet ',up-ab
	       :stack-alphabet ',stack-alphabet
	       :start-state ',start-state
	       :accept-states ',accept-states
	       :transition-fun ',transition-fun)))


(gen-pda
 :name zn1n
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 b)
 :start-state q0
 :accept-states (q0 q3)
 :transition-fun (((q0 nil nil) . ((q1 b)))
                  ((q1 0   nil) . ((q1 0)))
                  ((q1 1   0)   . ((q2 nil)))
                  ((q2 1   0)   . ((q2 nil)))
                  ((q2 nil b)   . ((q3 nil)))))


(run-pda *ZN1N* '(0 0 1 1))
(run-pda *ZN1N* '(0 0 1 1 1))
(run-pda *ZN1N* '())











(save-exec "pda_run_exec" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
           :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::main (cdr sb-ext:*posix-argv*))' --disable-debugger")



