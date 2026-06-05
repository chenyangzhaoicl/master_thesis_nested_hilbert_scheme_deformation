# Master Thesis Nested Hilbert Scheme Verification

This repository contains the Macaulay2 verification code used in my master thesis,
*Deformation Theory and Torus-Fixed Geometry of the Nested Hilbert Scheme of Points*.

The script computes the tangent-weight multiset from the compatibility kernel
\[
\ker\!\left(\operatorname{Hom}(I,R/I)\oplus\operatorname{Hom}(J,R/J)
\to \operatorname{Hom}(I,R/J)\right)
\]
at monomial fixed points of the nested Hilbert scheme
\(\operatorname{Hilb}^{n,n+1}(\mathbb A^2)\), and compares it with the
Young-diagram row-and-column shortening rule.

To run the verification:

```bash
M2 --script code/verify_weights.m2
```

The current script checks all partitions of size at most `16`.
