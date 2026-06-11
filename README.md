# Master Thesis Nested Hilbert Scheme Verification

This repository contains the Macaulay2 verification code accompanying my master thesis:

**Deformation Theory and Torus-Fixed Geometry of the Nested Hilbert Scheme of Points**

## Contents

- `code/verify_weights.m2`: Macaulay2 script verifying the tangent-weight formula for monomial fixed points of the nested Hilbert scheme `Hilb^{n,n+1}(A^2)`.
- `docs/young-diagram-playground.html`: interactive Young diagram playground for fixed-point monomial data and the row-and-column shortening rule.

## What The Script Checks

The script computes the torus-weight multiset from the compatibility kernel

```text
ker( Hom(I,R/I) direct_sum Hom(J,R/J) -> Hom(I,R/J) )
```

for nested monomial ideals `I subset J`. It then compares the computed weights with the Young-diagram row-and-column shortening rule.

The current bound is all partitions of size at most `16`.

## Running The Verification

Install Macaulay2, then run:

```bash
M2 --script code/verify_weights.m2
```

The expected final output is:

```text
All tests passed for |lambda| <= 16.
Checked 2455 nested fixed points.
```

## Interactive Playground

Play online here:

https://felixzhao.com/young-diagram-playground.html

The repository also keeps a standalone copy at `docs/young-diagram-playground.html` for reference. The playground lets you explore:

- partitions and their monomial quotient bases,
- removable corners of `lambda` as socle directions,
- addable boxes of `mu=lambda\c` as local-generator directions,
- the nested tangent-weight shortening rule.
