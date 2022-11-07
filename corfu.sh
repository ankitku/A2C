docker pull atwalter/acl2s_gradescope_autograder:cs2800fa22 
docker build -t hwk05 .
docker tag hwk05 ankitku88/hwk05
docker push ankitku88/hwk05
