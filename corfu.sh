docker pull atwalter/acl2s_gradescope_autograder:cs2800fa22 
docker build -t dfa_test .
docker tag dfa_test ankitku88/dfa_test
docker push ankitku88/dfa_test
