README
======

Supplementary verification program for

    Takayuki Kuriyama,
    "Additive Representations by Primitive Dyck Numbers:
     Exceptional Sets and Optimal Orders"


1. Files
--------

This supplementary material consists of

    verify_certificates_for_paper.py
    README.txt

The Python program reproduces the finite computations used in the paper and
performs independent finite-range checks of the recurring obstruction and the
two explicit families requiring five and six summands.


2. Requirements
---------------

Python 3.9 or later is recommended.

The program uses only the Python standard library. No external packages,
computer-algebra systems, network access, or data files are required.


3. Basic usage
--------------

Place README.txt and verify_certificates_for_paper.py in the same directory
and run

    python3 verify_certificates_for_paper.py

On systems where the Python 3 executable is named "python", use

    python verify_certificates_for_paper.py

The default command performs the independent dynamic-programming and
recurring-family checks through

    N = 50000.

A different upper bound can be specified with the --bound option. For example,

    python3 verify_certificates_for_paper.py --bound 20000

checks r(N) for every even N up to 20000 and checks every recurring-family
instance whose relevant values lie in that range.

The bound must be at least 848.


4. What the program verifies
----------------------------

The program checks the following finite statements and finite-range
cross-checks associated with the paper.


(A) Primitive-Dyck membership of the finite certificate sets

The program uses

    L = {3, 13, 14, 53, 54, 57, 58, 60}

and

    H = {213, 214, 217, 218, 220, 229, 230, 233, 234, 236,
         241, 242, 244, 248}.

Here

    P = {v/4 : v is a primitive Dyck number and v >= 12}.

It verifies

    L is contained in P,
    H is contained in P,
    P intersect [0,211] equals L.


(B) The five interval inclusions in the finite interval certificate

The program constructs all relevant finite sumsets exhaustively, with
repetition allowed, and verifies

    [215,254]  is contained in 5L,
    [245,486]  is contained in H + 4L,
    [439,674]  is contained in 2H + 3L,
    [645,862]  is contained in 3H + 2L,
    [855,1046] is contained in 4H + L.

It also verifies that the union of these five finite sumsets covers

    [215,1046].


(C) The low-end checks for the five-summand proposition

The program verifies

    212, 213, and 214 belong to F_5(P),

where

    F_k(X) = union_{j=0}^k jX,

and also verifies

    209, 210, and 211 do not belong to F_5(P).


(D) The finite exceptional-set certificate on [0,211]

The program verifies exactly the interval description of F_5(L) stated in the
paper. It then verifies the criterion

    F_5(L) union (1 + F_3(L)) union (2 + F_1(L))

on [0,211], and confirms that its complement is exactly

    {8, 11, 24, 38, 49, 50, 51, 209, 210, 211}.

For N = 4m + 2, these m-values correspond to

    {34, 46, 98, 154, 198, 202, 206, 838, 842, 846}.

This list concerns only the residue class N congruent to 2 modulo 4.
Therefore 44 does not occur in this particular list. The exceptional value
44 lies in the residue class 0 modulo 4 and is detected separately by the
direct dynamic-programming check described below.


(E) Independent finite-range cross-check of r(N)

For every N in the selected finite range, the program independently generates
all positive primitive Dyck numbers not exceeding the bound and computes r(N)
by unbounded coin-change dynamic programming.

For the default bound 50000, it verifies

    r(46) = 8;

    the values with r(N) = 7 are exactly
    {34, 44, 98, 154, 198, 202, 206, 838, 842, 846};

    46 is the only checked value with r(N) = 8;

    no checked even N has r(N) > 8;

    every checked even N in [848,50000] has r(N) <= 6.

It also checks explicitly that the primitive-number generator includes the
summand 2.


(F) Finite-range checks of the recurring obstruction

For

    x_k = 10 * 4^k - 2,

the paper proves, for every k >= 2,

    x_k not in F_4(P),
    x_k - 1 not in F_2(P).

The program checks every instance for which the relevant values lie within the
selected finite bound.

For the default bound 50000, it checks k = 2, 3, 4, 5, namely

    x_2 = 158,
    x_3 = 638,
    x_4 = 2558,
    x_5 = 10238.


(G) Finite-range checks of the explicit six-summand family

The paper proves

    r(10 * 4^(k+1) - 6) = 6       for every k >= 2.

For the default bound 50000, the program verifies

    r(634)   = 6,   corresponding to k = 2,
    r(2554)  = 6,   corresponding to k = 3,
    r(10234) = 6,   corresponding to k = 4,
    r(40954) = 6,   corresponding to k = 5.


(H) Finite-range checks of the explicit five-summand family

The paper proves

    r(10 * 4^(k+1) - 8) = 5       for every k >= 3.

For the default bound 50000, the program verifies

    r(2552)  = 5,   corresponding to k = 3,
    r(10232) = 5,   corresponding to k = 4,
    r(40952) = 5,   corresponding to k = 5.


5. Conventions used by the program
----------------------------------

For a finite set X of nonnegative integers,

    kX = {x_1 + ... + x_k : x_i in X},

where repetition is allowed, and

    0X = {0}.

Also,

    F_k(X) = union_{j=0}^k jX.

All intervals [a,b] are integer intervals

    {a, a+1, ..., b}.

All finite sumsets are constructed exhaustively as Python sets.


6. Expected output for the default command
------------------------------------------

Running

    python3 verify_certificates_for_paper.py

should produce the following output.

=== Finite interval certificates ===
PASS: L is contained in P
PASS: H is contained in P
PASS: P intersect [0,211] equals L
PASS: [215,254] is contained in 5L
PASS: [245,486] is contained in H+4L
PASS: [439,674] is contained in 2H+3L
PASS: [645,862] is contained in 3H+2L
PASS: [855,1046] is contained in 4H+L
PASS: [215,1046] is covered by the five finite sumsets
PASS: 212, 213, and 214 belong to F_5(P)
PASS: 209, 210, and 211 do not belong to F_5(P)
PASS: F_5(L) matches the interval certificate in the paper

=== Finite exceptional-set certificate ===
PASS: the six-summand criterion matches the paper
PASS: the complement is the stated ten-element set
PASS: exceptional m-values are
      [8, 11, 24, 38, 49, 50, 51, 209, 210, 211]
PASS: corresponding N=4m+2 values are
      [34, 46, 98, 154, 198, 202, 206, 838, 842, 846]

=== Dynamic-programming check through 50000 ===
PASS: r(46)=8
PASS: the r=7 values in the checked range are exactly the stated ten
PASS: 46 is the only r=8 value in the checked range
PASS: no checked even N has r(N)>8
PASS: every checked even N in [848,50000] has r(N)<=6
PASS: the primitive-number generator includes 2
PASS: finite-range r(N) cross-check gives
      r(N)=7 at [34, 44, 98, 154, 198, 202, 206, 838, 842, 846]
      r(N)=8 at [46]

=== Recurring obstruction and explicit families ===
PASS: at least one recurring-obstruction instance is in range
PASS: x_2=158 is not in F_4(P)
PASS: x_2-1=157 is not in F_2(P)
PASS: r(10*4^(2+1)-6)=r(634)=6
PASS: x_3=638 is not in F_4(P)
PASS: x_3-1=637 is not in F_2(P)
PASS: r(10*4^(3+1)-6)=r(2554)=6
PASS: r(10*4^(3+1)-8)=r(2552)=5
PASS: x_4=2558 is not in F_4(P)
PASS: x_4-1=2557 is not in F_2(P)
PASS: r(10*4^(4+1)-6)=r(10234)=6
PASS: r(10*4^(4+1)-8)=r(10232)=5
PASS: x_5=10238 is not in F_4(P)
PASS: x_5-1=10237 is not in F_2(P)
PASS: r(10*4^(5+1)-6)=r(40954)=6
PASS: r(10*4^(5+1)-8)=r(40952)=5
PASS: recurring-family finite cross-checks give
      six-summand family: [(2, 634), (3, 2554), (4, 10234), (5, 40954)]
      five-summand family: [(3, 2552), (4, 10232), (5, 40952)]

PASS: all certificates and finite cross-checks verified

7. Effect of changing --bound
-----------------------------

Changing --bound affects

    * the upper endpoint of the independent r(N) calculation;
    * the line checking all even N in [848,bound];
    * the recurring-obstruction instances included in the run;
    * the listed instances of the explicit five- and six-summand families.

The finite L/H certificates and the exact exceptional-set computation on
[0,211] do not depend on --bound.

For example,

    python3 verify_certificates_for_paper.py --bound 848

still checks all finite certificates and includes the first recurring
obstruction and the value r(634)=6, whereas larger bounds include more members
of the two explicit families.


8. Failure behavior
-------------------

Every verified statement is reported with a line beginning with "PASS:".

If a check fails, the program prints a line beginning with "FAIL:" and raises
an AssertionError immediately. Thus a complete run ending with

    PASS: all certificates and finite cross-checks verified

means that every finite certificate and every finite-range check requested in
that run has passed.

Invalid negative arguments and bounds below 848 raise ValueError.


9. Scope of the computation
---------------------------

The program reproduces the finite certificates used in the paper and provides
independent finite-range cross-checks of r(N), the recurring obstruction, and
the explicit five- and six-summand families.

The dynamic-programming and finite-sumset calculations do not replace the
paper's proofs of statements for all integers or all k. The infinite assertions
are established theoretically in the paper by interval propagation,
self-similarity, base-4 generation bounds, and the recurring-obstruction
argument. The program checks the finite base certificates and supplies
independent computational evidence over the selected finite range.


10. Reproducibility
-------------------

The version archived with the paper should be identical to the version at the
commit cited in the paper. To preserve reproducibility, do not replace the
archived script by a later version without also updating

    * the commit cited in the paper;
    * the archived README;
    * the expected output in Section 6; and
    * any numerical ranges stated in the paper.

The archived README and script should always be kept together.
