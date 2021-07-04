(gen-dfa
 :name            student-dfa
 :states          (e1 e2 o1 o2)
 :alphabet        (0 1)
 :start           e1   
 :accept          (o1 o2)
 :transition-fun  ((e1 0 e1)
		   (e1 1 o1)
		   (e2 0 e2)
		   (e2 1 o2)
		   (o1 0 o2)
		   (o1 1 e2)
		   (o2 0 o1)
		   (o2 1 o1)))
