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
       `acl2s::(=> (and (,es element=) (,ss state=))
		   (in (list state= element=) ',domain)))))

(defun query-function-distinctdom (txf)
  (let ((domain (strip-cars txf)))
    (not (== (len domain)
             (len (remove-duplicates domain :test 'equal))))))

(defun possible-domains (txf)
  (if (endp txf) nil
    (cons (second (caar txf))
          (extract-fun-elems (cdr txf)))))

(defun query-extra-functiondom (elem-def state-def txf)
  (let ((es (gen-sym-pred elem-def))
	(ss (gen-sym-pred state-def))
        (doma (strip-cars txf)))
    (itest?-query
     `acl2s::(=> (in state-element-pair= (quote ,doma))
                 (and  (,ss (first state-element-pair=))
                       (,es (second state-element-pair=)))))))
                     

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
                         (let ((res (query-function-distinctdom transition-fun)))
                           (if res (error-and-reset "transition function domain is not distinct" d-state)
                             (let ((res (query-extra-functiondom d-elem d-state transition-fun)))
                               (if (car res)
                                   (error-and-reset (format nil "Domain of transition function is not of type : states x alphabet

~a" (cdr res)) d-state)
                                 ;;(if (not (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun)))))
                                 ;; with all the other checks we added for functions, we do not really need to enforce it as a map
                                   ;;  (error-and-reset "incorrect transition function" d-state)
                                   (progn (acl2s-event `acl2s::(defconst ,dfa-name (list ',states ',alphabet ',transition-fun ',start ',accept)))
                                          (cons t (format nil "Legal DFA : ~a" `acl2s::(,states ,alphabet ,transition-fun ,start ,accept))))))))))))))))))



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
