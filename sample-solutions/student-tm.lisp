(gen-tm
 :name student-tm
 :states (q0 q1 q2 q3)
 :alphabet (#\0 #\1)
 :tape-alphabet (#\0 #\1 nil)
 :start-state q0
 :accept-state q1
 :reject-state q2
 :transition-fun (((q0 #\1) . (q0 #\0 R))
                  ((q0 #\0) . (q0 #\1 R))
                  ((q0 nil) . (q3 nil R))
                  ((q3 nil) . (q1 nil L))))

