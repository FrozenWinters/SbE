# Stepping by Evaluation

### Project Summary

Normalisation by Evaluation is considered a *reduction-free* approach to normalisation and is to be thought
of as antithetical to the operational semantics approach of repeatedly reducing a term until it normalises.
This project extends NbE to produce correctness proofs that `ιNf (norm t)` is related to `t` by way
of a **computational trace** in terms of β and ε laws.

For example, here is the trace that eta expands the identity function:
```
(λ. ⟪ 0 ⟫)
    η
(λλ. (1 0))
```
*(Typically, such traces will be much less direct and will involve a lot more going around in circles.)*

### Reading Order

1. [`lists`](lists.agda) – Sets up all the useful structures for working with general non-dependent type theory
2. [`syn`](syn.agda) – Constructs syntax and proves several of its properties
3. [`normal`](normal.agda) – Defines normals and neutrals and some of their structure
4. [`trace`](trace.agda) – Defines computational traces and the operations that can be performed on them
5. [`norm`](norm.agda) – This is the *Main Argument* and is responsible for NbE and trace construction
6. [`print`](print.agda) – Pretty printing utilities
7. [`tests`](tests.agda) – Contains several examples of syntactic terms
8. [`compile`](compile.agda) – This is the file to be compiled in order to properly display pretty printed traces

### Motivation

My [stlc project](https://github.com/FrozenWinters/stlc/blob/main/README.md) formalised a categorical
glueing argument for simply typed lambda calculus in Cubical Agda. This was written in a very mathematical
manner and spared no theoretical expenses.

Unfortunately, while the normalisation part of the resulting computation ran quickly, computing equality
proofs was prohibitive; I was not able to find the normal form of a proof that *"2+2=4"*, and eta expanding
the identity function took 50s of computation time. Further, looking at the proofs that I could compute
was entirely unenlightening and did not explain *"what was really going on with NbE"*.

Technically, a proof that `ιNf (norm t) ≡ t` should reduce to cubical operations and the reduction laws
built into the term HIT. Since the *"cubical laws"* part of this was obscuring any output intelligibility,
one could hope to instead replace equality with a type of *Computational Traces* which, by definition,
present the convertibility of `ιNf (norm t)` to `t` exclusively in terms of reduction laws.

Since these computational traces are *"more discrete"* than terms, we would not have that computationally
related terms give rise to equal traces. For this reason, we abandon the HIT model of syntax and instead
bake all computation laws into the type of traces themselves.

A main goal of this project was, in contrast to `stlc`, to write as little code as necessary to produce
these traces using as few fancy structures as possible.
