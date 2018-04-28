# Fulcrum implementation and proof in SPARK

This small example shows the implementation and proof of the so-called Fulcrum in SPARK, to
answer the third problem of this [challenge](https://hillelwayne.com/post/theorem-prover-showdown/).

You can verify the proof using [SPARK](https://www.adacore.com/sparkpro) as
follows:

```bash

$ gnatprove -P fulcrum --report=all --prover=z3,cvc4

```

and compile and run the simple test case as follows using [GNAT
Pro](https://www.adacore.com/gnatpro):


```bash

$ gprbuild -p -P fulcrum
$ ./obj/test_fulcrum

```
