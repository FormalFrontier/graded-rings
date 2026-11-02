# Polynomial coordinates with module regularity

Let \(R\) be a commutative ring, let \(M\) be an \(R\)-module, and let
\(a\in R\). The types of \(R\) and \(M\) need not belong to the same universe.
Put
\[
 I=(a),\qquad A=R/I,\qquad Q=M/IM.
\]
Here \(IM\) denotes the submodule \(I\mathbin{\bullet}\top\), not an
additional scalar structure on \(M\). Module regularity of \(a\) means that
\(m\mapsto a\cdot m\) is injective on \(M\), as expressed by
`IsSMulRegular M a`. It does not mean that multiplication by \(a\) is
injective on \(R\).

The example below has module regularity but not ring regularity. It gives
explicit polynomial coordinates, an inverse, and nonzero classes in every
natural degree for the polynomial quotient-Rees associated graded module.

## The fixed quotient and the comparison map

Write \(\mathcal R_I(M)\) for the Rees-module submodule of
`PolynomialModule R M`. Its elements are finite-support coefficient families
\(P=(p_n)_{n\geq 0}\) satisfying
\[
 p_n\in I^nM\quad\text{for every }n.
\]
In particular, \(I^0M=M\). Throughout, the target is
\[
 N=\texttt{Ideal.AssociatedGradedModule}\ I\ M
   =\mathcal R_I(M)/(I\mathcal R_I(M))
\]
in its polynomial quotient-Rees realization. The notation
\(\operatorname{mk}(P)\) means the existing quotient constructor, with
\(P\)'s Rees-membership proof understood. This notation does not replace
\(N\) by a coefficientwise quotient or a direct sum.

The denominator \(I\mathcal R_I(M)\) is the submodule of finite sums of
\(i\cdot P\), for \(i\in I\) and \(P\in\mathcal R_I(M)\). Scalars here act
as **constant coefficients**. In particular, this is not the submodule
obtained by multiplying by \(aT\).

Let
\[
 C=\mathcal R_I(R)/(I\mathcal R_I(R)).
\]
The module \(N\) retains its given \(C\)-action. Its \(A\)-action is the
coefficient restriction along \(\operatorname{algebraMap}:A\to C\).
Consequently, if \(\alpha\in A\) is represented by \(r\in R\), then
\[
 \alpha\cdot\operatorname{mk}(P)=\operatorname{mk}(r\cdot P).       \tag{1}
\]
This is a formula for the restricted existing action, not a definition of
a replacement action. Similarly, \(Q\) has its canonical quotient
\(A\)-action, with \(\alpha\cdot[m]=[r\cdot m]\).

For every natural \(q\) and \(m\in M\), the original polynomial singleton
\[
 \operatorname{single}_R(q,a^q\cdot m)
\]
belongs to \(\mathcal R_I(M)\): its coefficient in degree \(q\) lies in
\(I^qM\), and its other coefficients are zero. The canonical comparison
\[
 F:\operatorname{PolynomialModule} A\ Q\longrightarrow N
\]
is \(A\)-linear and has the characteristic value
\[
 F\bigl(\operatorname{single}_A(q,[m])\bigr)
   =\operatorname{mk}\bigl(\operatorname{single}_R(q,a^q\cdot m)\bigr).
                                                               \tag{2}
\]
There is no regularity hypothesis in this construction. Indeed,
\(IM=aM\), and replacing \(m\) by \(m+a\cdot u\) changes the polynomial
on the right by
\[
 a\cdot\operatorname{single}_R(q,a^q\cdot u)
       \in I\mathcal R_I(M).
\]
Additivity and (1) give the quotient-coefficient \(A\)-linear map in each
degree; finite sums give \(F\). Only \(A\)-linearity is being asserted:
no \(C\)-action on `PolynomialModule A Q` is introduced.

The distinction between unconditional surjectivity and invertibility under
module regularity can be tested without assuming that \(M\) is faithful,
flat, finitely generated, or free. We now compute such an example directly
inside this fixed quotient.

## A zero divisor on the ring, an injective scalar on the module

Take
\[
 R=\mathbb Z\times\mathbb Z,\qquad a=(2,0),\qquad M=\mathbb Z,
 \qquad (r,s)\cdot m=rm.
\]
Thus \(a\cdot m=2m\), which is injective on \(\mathbb Z\). Hence \(a\)
is \(M\)-regular. But \(e=(0,1)\) is a nonzero element of \(R\), and
\(ae=0\), so \(a\) is not \(R\)-regular.

The ideal and quotient ring are
\[
 I=2\mathbb Z\times\{0\},\qquad
 A\simeq(\mathbb Z/2\mathbb Z)\times\mathbb Z,
 \qquad [(r,s)]\longmapsto(\bar r,s).
\]
For positive \(q\),
\[
 I^q=2^q\mathbb Z\times\{0\}.
\]
For \(q=0\), however, \(I^0=R=\mathbb Z\times\mathbb Z\), not
\(\mathbb Z\times\{0\}\). With the specified action on \(M\), the uniform
formula for all natural \(q\) is
\[
 I^qM=2^q\mathbb Z.
\]
It follows that
\[
 Q=\mathbb Z/2\mathbb Z\ne 0.
\]
Under these identifications the canonical \(A\)-action on \(Q\) is
\[
 (\bar r,s)\cdot\bar m=\overline{rm}.                         \tag{3}
\]
No \(A\)-action on \(M\) compatible with its original \(R\)-action is
being used: such an action would force \(a\) to act as zero, whereas it
acts on \(M\) by multiplication by two.

## Normalizing polynomials in the original Rees module

In this example \(\mathcal R_I(M)\) consists precisely of the finite-support
integer coefficient families satisfying
\[
 p_n\in 2^n\mathbb Z.
\]
Every such family has a unique normalization
\[
 p_n=2^n c_n,\qquad c_n\in\mathbb Z.                          \tag{4}
\]
Existence is the coefficient-membership condition. Uniqueness follows
from injectivity of multiplication by \(2^n\) on \(\mathbb Z\). In
particular, \(p_n=0\) if and only if \(c_n=0\); the family \((c_n)\) has
finite support. Thus normalization does not introduce an infinite series.

The quotient denominator is exactly
\[
 I\mathcal R_I(M)=2\mathcal R_I(M).                           \tag{5}
\]
For one inclusion, an element \((2r,0)\in I\) acts on a Rees polynomial
as twice the Rees polynomial obtained by multiplying its integer
coefficients by \(r\); the same holds for finite sums. For the reverse
inclusion, multiplication by two on this module is the action of
\(a\in I\). Equivalently, for a polynomial \(P\) normalized as in (4),
\[
 \begin{aligned}
 P\in I\mathcal R_I(M)
 &\iff \text{every }c_n\text{ is even}\\
 &\iff \text{every }p_n\in 2^{n+1}\mathbb Z.                 \tag{6}
 \end{aligned}
\]
For the converse implication in (6), write \(c_n=2d_n\). The finite-support
polynomial with coefficients \(2^n d_n\) is in \(\mathcal R_I(M)\), and
twice that polynomial is \(P\). This establishes membership in the
submodule denominator, not just separate divisibility statements.

Normalization followed by reduction modulo two gives
\[
 \nu(P)=\sum_n\operatorname{single}_A(n,[c_n])
       \in\operatorname{PolynomialModule} A\ Q.             \tag{7}
\]
The sum is finite. Normalization is additive, and (6) says precisely that
\(\ker\nu=I\mathcal R_I(M)\). More explicitly, if \(P\) is changed by
\(2H\), with \(h_n=2^n d_n\), then its normalized coefficients change by
\(2d_n\), leaving (7) unchanged. Hence (7) defines an inverse candidate on
the **original quotient**:
\[
 \Psi:N\longrightarrow\operatorname{PolynomialModule} A\ Q,
 \qquad \Psi(\operatorname{mk}(P))=\sum_n
                 \operatorname{single}_A(n,[p_n/2^n]).       \tag{8}
\]
The division in (8) denotes the unique integer in (4), not division in
\(R\), \(A\), or \(Q\).

## The forward map and both composites

Let \(f\in\operatorname{PolynomialModule} A\ Q\). Choose a finite-support
integer family \((t_n)\) lifting its coefficients; for example, take
\(t_n=0\) outside the support of \(f\). Define \(P_f\) in the original
polynomial module by
\[
 (P_f)_n=2^n t_n.
\]
It has finite support and lies in \(\mathcal R_I(M)\). Changing the lifts
by \(t'_n-t_n=2u_n\) changes \(P_f\) by twice the Rees polynomial with
coefficients \(2^n u_n\). Thus
\[
 F(f)=\operatorname{mk}(P_f)                                 \tag{9}
\]
is independent of the lifts. This is exactly (2), not merely some
isomorphism with the same source and target: for every \(q,m\),
\[
 F(\operatorname{single}_A(q,[m]))
   =\operatorname{mk}(\operatorname{single}_R(q,2^q m))
   =\operatorname{mk}(\operatorname{single}_R(q,a^q\cdot m)).
\]
The last equality also holds at \(q=0\), since \(a^0=(1,1)\) acts as the
identity on \(M\).

For each coefficient of \(f\), normalizing \(2^n t_n\) and reducing
modulo two returns \([t_n]\). Therefore
\[
 \Psi(F(f))=f.                                               \tag{10}
\]
Conversely, let \(P\in\mathcal R_I(M)\) have normalization \(p_n=2^n c_n\).
In applying (9) to \(\Psi(\operatorname{mk}(P))\), one may choose the
\(c_n\) themselves as coefficient lifts. The resulting Rees polynomial
is \(P\) coefficient by coefficient, so
\[
 F(\Psi(\operatorname{mk}(P)))=\operatorname{mk}(P).           \tag{11}
\]
If instead the lifts are chosen to be zero or one, their differences
from the \(c_n\) are even, and (5) gives the same equality in the original
quotient. Thus (10) and (11) prove surjectivity and injectivity of the
specified forward map, with a pointwise inverse on quotient classes.

There is also a direct-sum description: (6) and finite support identify
\(N\), additively, with
\(\bigoplus_{n\geq0}2^n\mathbb Z/2^{n+1}\mathbb Z\), and normalization
identifies each summand with \(Q\). Equations (8)--(11) are the explicit
maps realizing that description on the polynomial quotient; the direct
sum is not substituted for the target.

## Scalar compatibility and nonfaithfulness

It remains important to check the specified scalars, not just an
isomorphism of abelian groups. Let
\(\alpha=(\bar r,s)\in A\), and choose its lift \((r,s)\in R\). By the
restriction of the given \(C\)-action, formula (1) represents
\(\alpha\cdot\operatorname{mk}(P)\) by the polynomial with coefficients
\(rp_n\). If \(p_n=2^n c_n\), its normalized coefficients are \(rc_n\).
Using (3), we obtain
\[
 \Psi(\alpha\cdot\operatorname{mk}(P))
   =\sum_n\operatorname{single}_A(n,[rc_n])
   =\alpha\cdot\Psi(\operatorname{mk}(P)).                   \tag{12}
\]
The residues do not depend on the lift \(r\); the second coordinate
\(s\) has no effect. The same calculation with (9) proves \(A\)-linearity
of \(F\). Thus these mutually inverse maps form an \(A\)-linear
equivalence for the canonical quotient action on \(Q\) and the restricted
existing action on \(N\). No action of \(C\) on the polynomial source is
needed for this calculation.

The nonzero idempotent \((\bar0,1)\in A\) kills both \(Q\) and \(N\).
Consequently \(Q\) is not faithful over \(A\). In particular, it is not
free of rank one over \(A\): a rank-one free \(A\)-module is isomorphic
to \(A\), and a scalar killing that module must kill \(1\), hence be
zero. The polynomial coordinates here are copies of this nonfaithful
quotient module, not copies of a rank-one free coefficient module.

## Nonzero classes in every degree and the ring distinction

For every natural \(q\), consider the class in the original target
\[
 \eta_q=\operatorname{mk}(\operatorname{single}_R(q,2^q)).
\]
Its normalized coefficient in degree \(q\) is one. Thus
\(\Psi(\eta_q)=\operatorname{single}_A(q,[1])\ne0\). Equivalently, (6)
would make \(\eta_q=0\) imply \(2^q\in2^{q+1}\mathbb Z\), which is
impossible. This includes degree zero. The example therefore has a
nonzero quotient coefficient module and nonzero target classes in every
natural degree, rather than a zero target making the comparison trivial.

The principal *ring* polynomial equivalence under ring regularity cannot
be used here. Indeed, in the canonical ring polynomial cover
\(A[T]\to C\), the nonzero polynomial \((\bar0,1)T\) maps to zero:
its representative coefficient multiplies \(a\) to
\((0,1)(2,0)=0\). The ring cover is not injective. In the module
comparison, however, \((\bar0,1)\) already annihilates \(Q\), so it does
not produce a nonzero coefficient in `PolynomialModule A Q`. This is
exactly why regularity on \(M\), rather than regularity on \(R\), is the
relevant condition. Adding ring regularity would exclude this example.

## Unit and zero-module boundaries

The nonzero objects in the example are a mathematical check, not an
extra hypothesis in the general comparison. If \(a\) is a unit, then
\(I=R\), \(Q=0\), and
\(I\mathcal R_I(M)=\mathcal R_I(M)\), so \(N=0\). The forward map is
then the unique map between zero modules. If \(M=0\), the Rees module,
\(Q\), and \(N\) are all zero for every \(a\), and scalar multiplication
is injective on the zero module. Both boundaries are consistent with
module regularity being the sole regularity condition for invertibility;
no nontriviality assumption is needed.
