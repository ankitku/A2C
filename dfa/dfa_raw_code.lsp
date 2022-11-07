(include-book "dfa/dfa")
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)

:q
(in-package "ACL2S")
(import 'acl2s-interface::(acl2s-event acl2s-query acl2s-compute itest?-query))

(declaim (optimize (safety 3) (speed 0) (space 0) (debug 3)))
(declaim (sb-ext:muffle-conditions style-warning))

;;------------------------------------------------------------------------
;; Symbol name manipulation
;;------------------------------------------------------------------------

(defun gen-symb (x n)
  (read-from-string (format nil x n)))

(defun gen-sym-pred (x)
  (gen-symb "~ap" x))

(defun gen-symb-const (x)
  (gen-symb "*~a*" x))

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
    (acl2s-event `acl2s::(defdata ,d-f (alistof ,d-tdom ,d-state)))
    (unless (second (acl2s-compute `acl2s::(,d-fp (quote ,transition-fun))))
       (error-and-reset "incorrect transition function" d-state))
    (acl2s-event `acl2s::(defdata ,name (list ,d-states ,d-ab ,d-f ,d-state ,d-states)))
    (unless (dfap `acl2s::(,states ,alphabet ,transition-fun ,start ,accept))
      (error-and-reset "incorrect dfa" d-state))
    (acl2s-event `acl2s::(defconst ,dfa-name (list ',states ',alphabet ',transition-fun ',start ',accept)))
    (cons t (format nil "Legal DFA : ~a" `acl2s::(,states ,alphabet ,transition-fun ,start ,accept)))))

(defun gen-dfa-fn (&key name states alphabet start accept transition-fun)
 (let* ((df `acl2s::(,states ,alphabet ,transition-fun ,start ,accept)))
    (mk-dfa-events name states alphabet start accept transition-fun)))

(defmacro gen-dfa (&key name states alphabet start accept transition-fun)
  (unless name (error "name missing"))
  (unless states (error "states missing"))
  (unless alphabet (error "alphabet missing"))
  (unless start (error "start missing"))
  (unless accept (error "accept missing"))
  (unless transition-fun (error "transition-fun missing"))
  `(gen-dfa-fn :name ',name
	       :states ',states
	       :alphabet ',alphabet
	       :start ',start
	       :accept ',accept
	       :transition-fun ',transition-fun))
  

;;------------------------------------------------------------------------
;; DFA query equivalence
;;------------------------------------------------------------------------

(defun query-alphabet-equal (dfa1-name dfa2-name)
  (let ((da1 (gen-symb "~a-alphabet" dfa1-name))
	(da2 (gen-symb "~a-alphabet" dfa2-name)))
    (acl2s-event
     `acl2s::(defdata-equal-strict ,da1 ,da2))))


;; f1 is instructor file (this is the spec of a correct DFA)
;; f2 is student file (may be buggy)
(defun query-equivalence (dfa1-name dfa2-name)
  (b* ((res (query-alphabet-equal dfa1-name dfa2-name))
       ((when (car res))
        (cons nil "Incorrect alphabet provided."))
       (dn (gen-symb "~a-wordp" dfa1-name))
       (dfa1 (gen-symb-const dfa1-name))
       (dfa2 (gen-symb-const dfa2-name))
       ((unless (boundp dfa1))
        (reset-and-exit :msg (format nil "Undefined DFA ~a" dfa1-name)
                        :func query-equivalence))
       ((unless (boundp dfa2)
          (reset-and-exit :msg (format nil "Undefined DFA ~a" dfa2-name)
                          :func query-equivalence)))
       (res (itest?-query
             `acl2s::(=> (,dn w)
                         (equal (run-dfa ,dfa1 w)
                                (run-dfa ,dfa2 w)))))
       ((when (car res))
        (cons nil (format nil "Transition function error. The following words
  were misclassified :~% ~a" (mapcar #'cadar (cadadr res))
  (gen-symb "~a-state" dfa2-name)))))
    (cons t (format nil "~a is correct." dfa2-name))))



#|

(gen-dfa
 :name instructor-dfa
 :states (even odd)
 :alphabet (0 1)
 :start even
 :accept (odd)
 :transition-fun (((even 0) . even)
                  ((even 1) . odd)
                  ((odd 0) . odd)
                  ((odd 1) . even)))


(gen-dfa
 :name student-dfa
 :states (e1 e2 o1 o2)
 :alphabet (0 1)
 :start e1
 :accept (o1 o2)
 :transition-fun (((e1 0) . e1)
                  ((e1 1) . o1)
                  ((e2 0) . e2)
                  ((e2 1) . e2)
                  ((o1 0) . o2)
                  ((o1 1) . e2)
                  ((o2 0) . o1)
                  ((o2 1) . e1)))

(query-equivalence 'instructor-dfa 'student-dfa)

|#
