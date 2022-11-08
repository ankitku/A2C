(in-package "ACL2S")

(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(include-book "pda/pda")

:q

(in-package "ACL2S")

;; load pda grading library and instructor's solution
(load "pda/pda_raw_code.lsp")

;; instructor version of PDA to test against
(gen-pda
 :name instructor-pda
 :states (q0 q1 q2 q3)
 :alphabet (0 1)
 :stack-alphabet (0 z)
 :start-state q0
 :accept-states (q0 q3)
 :transition-fun (((q0 :e :e) . ((q1 z)))
                  ((q1 0 :e)  . ((q1 0)))
                  ((q1 1  0)  . ((q2 :e)))
                  ((q2 1  0)  . ((q2 :e)))
                  ((q2 :e z)  . ((q3 :e)))))

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

    (grade "test-legal-pda"
           10
           res)
    
    ;; Grade form to grade student submission
    (grade "test-equivalence"          ;; test case name
           10                          ;; points allocated to this test
           (query-equivalence 'instructor-pda 'student-pda))
    ;; should return (bool . string)
    )
(finish-grading))

    
;; the following command is necessary to create an executable
;; named run_autograder according to gradescope specification
(save-exec "run_autograder" nil
           :init-forms '((set-gag-mode nil)
                         (value :q))
          :toplevel-args "--eval '(declaim (sb-ext:muffle-conditions style-warning))' --eval '(acl2s::run-tests)' --disable-debugger")


