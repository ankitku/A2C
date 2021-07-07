FROM atwalter/acl2s_gradescope_autograder

RUN apt-get update && apt-get install -y git curl unzip dos2unix && apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

RUN mkdir -p /autograder 
COPY . /autograder/

RUN apt-get update && apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

ENV HOME=/

RUN curl -O https://beta.quicklisp.org/quicklisp.lisp
RUN sbcl --load quicklisp.lisp --eval '(quicklisp-quickstart:install)'

WORKDIR /autograder

RUN git submodule update --init --recursive
RUN cd gradescope-acl2s/interface && make && cd ../..
RUN cd dfa && ./make.sh && cd ..

RUN mkdir results
RUN acl2s < example.lisp
