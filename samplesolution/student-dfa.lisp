(gen-dfa
 :name            student-dfa1
 :states          (e1 e2 o1 o2)
 :alphabet        (0)
 :start           e1   
 :accept          (o1 o2)
 :transition-fun  ((e1 0 e1)
		   (e1 2 o1)
		   (e2 0 e2)
		   (e2 2 o2)
		   (o1 0 o2)
		   (o1 2 e2)
		   (o2 0 o1)
		   (o2 2 o1)))
