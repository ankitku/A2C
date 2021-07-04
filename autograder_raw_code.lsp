;;----------------------------------------------------------------------------------
;; Author : Ankit Kumar
;; The following code can be loaded after instructor's and student's versions
;; of solutions are loaded into ACL2s. Wrapping up tests in grade function will
;; record grades and finish-grading will generate an output result.json file.
;;----------------------------------------------------------------------------------

:q
(load "~/quicklisp/setup.lisp")
(ql:quickload :jsown)
(in-package "ACL2S")

(defun load-acl2s-file (filename)
  (progn (defparameter *j* (open filename))
         (loop
          (setq sexp
                (ignore-errors
                  (let ((*readtable* acl2::*acl2-readtable*))
                    (read *j*))))
          (when (endp sexp) (return))
          (ignore-errors (acl2s-event sexp)))))


(setf *test-score-jsons* nil)
(setf *total-score* 0)

(defun grade (name points test)
  :ic (and (boolp (car test)) (natp points))
  (b* ((iscorrect (car test))
       (output    (cdr test))
       (score     (if iscorrect points 0)))
    (setf *total-score* (+ *total-score* score))
    (setf *test-score-jsons* (cons (jsown:new-js
				    ("name" name)
				    ("score" score)
				    ("max_score" points)
				    ("output" output))
				   *test-score-jsons*))))
  

(defun finish-grading ()
  (with-open-file (str "results/results.json"
		       :direction :output
		       :if-exists :supersede
		       :if-does-not-exist :create)
    (format str (jsown:to-json
		 (jsown:new-js
		  ("tests" *test-score-jsons*)
		  ("score" *total-score*)))))
  (sb-ext:exit))


;; Usage
#|

(grade "test1" 10 (t . "correct"))
(grade "test2" 10 (nil . "incorrect, here are counterexamples : ((a 1) (b 2))"))

(finish-grading)

|#

