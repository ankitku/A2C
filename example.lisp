(in-package "ACL2S")

(include-book "gradescope-acl2s/interface/top")
(include-book "dfa/dfa")

:q

;; load acl2s grading infrastructure
(load "gradescope-acl2s/autograder_raw_code.lsp")

;; load dfa grading library and instructor's solution
(load "dfa/dfa_raw_code.lsp")

(in-package "ACL2S")


(defun run-tests ()
  ;; Load the student submission
  (let ((submittedform (load-lisp-file "submission/student.lisp")))
    (grade "test-legal-dfa"
	   10
	   (eval submittedform)))

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


