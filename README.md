# Fulcrum implementation and proof in SPARK

This small example shows the implementation and proof of the so-called Fulcrum in SPARK, to
answer the third problem of this [challenge](https://hillelwayne.com/post/theorem-prover-showdown/).

This code is referenced in an [AdaCore blog
post](https://blog.adacore.com/taking-on-a-challenge-in-spark). However, the
repository has changed since the appearance of the article. Please use the
[article tag](https://github.com/kanigsson/fulcrum/tree/article) to see the
code that corresponds to the article.

You can verify the proof using [SPARK](https://www.adacore.com/sparkpro) as
follows:

```bash

$ gnatprove -P fulcrum --report=all --level=2

```

and compile and run the simple test case as follows using [GNAT
Pro](https://www.adacore.com/gnatpro):


```bash

$ gprbuild -p -P fulcrum
$ ./obj/test_fulcrum

```
