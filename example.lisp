(in-package "ACL2S")

(include-book "interface/top")
(include-book "dfa/dfa")

:q

;; load acl2s grading infrastructure
(load "autograder_raw_code.lsp")


;; load dfa grading library and instructor's solution
(load "dfa/dfa_raw_code.lsp")

(defun run-tests ()
  ;; Load the student submission
  (let ((rr (with-open-file (s "submission/student.lisp")
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


