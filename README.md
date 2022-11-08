
### Introduction
Automatic Automata Checker (A2C) is a library based on the ACL2S
Theorem Prover (http://acl2s.ccs.neu.edu/acl2s/doc/) that enables
construction of executable automata using forms faithful to their
textbook (Sipser's Automata book) definitions. Such constructions are
easy to reason about using semantic equivalence checks, properties and
test cases. Currently, it supports 3 models of computations: DFA, PDA
and TM, but can be easily extended to support more.

### Try it out!
If you want to try out sample Theory of Computation homeworks on
Gradescope, signup for Course TOC101 (Course ID: 464626) at
**Northeastern University** using code **BB82DP**.

### Setting it up
If you want to setup a homework for your Theory of Computation course,
take a look at one of example_dfa.lisp, example_pda.lisp or
example_tm.lisp files. If you want to generate an executable to
check/grade forms locally, execute

```
acl2s < example_dfa.lisp
```

If you want to setup a homework on Gradescope using a custom Docker
image, checkout Dockerfile and corfu.sh script file. Setting up a
Gradescope homework utilizes the [gradescope-acl2s](https://github.com/ankitku/gradescope-acl2s)
library to interact with ACL2S lisp files and to generate JSON files
that can be read by Gradescope.


