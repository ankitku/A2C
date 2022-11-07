(in-package "ACL2S")

(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(include-book "dfa/dfa")

:q

;; load dfa grading library and instructor's solution
(load "dfa/dfa_raw_code.lsp")

;; load acl2s grading infrastructure
(load "gradescope-acl2s/autograder_raw_code.lsp")

;; instructor version of DFA to test against
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
       (submittedform (load-lisp-file hwk-file-name)))
    (grade "test-legal-dfa"
           10
           (eval submittedform))
    
    ;; Grade form to grade student submission
    (grade "test-equivalence"          ;; test case name
           10                          ;; points allocated to this test
           (query-equivalence 'instructor-dfa 'student-dfa))
    ;; should return (bool . string)
    )
(finish-grading))

    
;; the following command is necessary to create an executable
;; named run_autograder according to gradescope specification
(save-exec "run_autograder" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
          :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::run-tests)' --disable-debugger")


