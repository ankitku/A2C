(in-package "ACL2S")

(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(include-book "tm/tm")
:q

(in-package "ACL2S")

;; load tm grading library and instructor's solution
(load "tm/tm_raw_code.lsp")

(gen-tm
 :name instructor-tm
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :tape-alphabet (0 1 nil)
 :start-state q0
 :accept-state q1
 :reject-state q2
 :transition-fun (((q0 1) . (q0 0 R))
                  ((q0 0) . (q0 1 R))
                  ((q0 nil) . (q3 nil R))
                  ((q3 nil) . (q1 nil L))))

;; (property involution (w :instructor-tm-word)
;;           :proofs? nil
;;           :check-contracts? nil
;;           (== (remove-beginnils (second (runtm-100
;;                                          (remove-beginnils (second (runtm-100 w *instructor-tm*)))
;;                                          *instructor-tm*)))
;;               w))

;; load acl2s grading infrastructure
(load "gradescope-acl2s/autograder_raw_code.lsp")

(defun run-tests ()
  (initialize)
  ;;checking if file was submitted
  (b* ((files (uiop:directory-files "submission/"))
       (hwk-file-name (car files))
       ;; searches for hwk file by string
       (res (check-file-submission hwk-file-name))
       (-   (grade "check file submission" 0 res))
       ((unless (car res)) nil)
       ;; Load the student submission
       (res (eval (load-lisp-file hwk-file-name))))
    (grade "test-legal-tm"
	   10
	   res))

  ;; Grade form to grade student submission
  (grade "test-equivalence-output"          ;; test case name
	 10                          ;; points allocated to this test
	 (query-equivalence-output 'instructor-tm 'student-tm))  ;; should return (bool . string)
  (finish-grading))


;; the following command is necessary to create an executable
;; named run_autograder according to gradescope specification
(save-exec "run_autograder" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
          :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::run-tests)' --disable-debugger")


