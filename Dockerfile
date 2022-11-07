
FROM atwalter/acl2s_gradescope_autograder:cs2800fa22 

RUN apt-get update && apt-get install -y git curl unzip dos2unix && apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

RUN curl -O https://beta.quicklisp.org/quicklisp.lisp
RUN sbcl --load quicklisp.lisp --eval '(quicklisp-quickstart:install)'

RUN mkdir -p /autograder 

COPY . /autograder/

ENV HOME=/

WORKDIR /autograder

RUN mkdir -p results

RUN acl2s < example_dfa.lisp
