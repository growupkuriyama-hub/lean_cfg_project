README
======

Supplementary verification program for

    Takayuki Kuriyama,
    "Additive Representations by Primitive Dyck Numbers"


1. Files
--------

This supplementary material consists of

    verify_certificates_for_paper.py
    README.txt

The Python program reproduces the finite computations used in the paper.


2. Requirements
---------------

Python 3.9 or later is recommended.

The program uses only the Python standard library.  No external packages,
computer-algebra systems, or data files are required.


3. Basic usage
--------------

Place README.txt and verify_certificates_for_paper.py in the same directory and
run

    python3 verify_certificates_for_paper.py

On systems where the Python 3 executable is named "python", use

    python verify_certificates_for_paper.py

The default command performs the independent dynamic-programming check through

    N = 2000.

A different upper bound can be specified with the --bound option.  For example,

    python3 verify_certificates_for_paper.py --bound 20000

checks r(N) for every even N up to 20000.  The bound must be at least 848.


4. What the program verifies
----------------------------

The program checks the following finite statements appearing in the paper.

(A) Primitive-Dyck membership of the finite certificate sets

    L = {3, 13, 14, 53, 54, 57, 58, 60},

and

    H = {213, 214, 217, 218, 220, 229, 230, 233, 234, 236,
         241, 242, 244, 248}.

Here

    P = {v/4 : v is a primitive Dyck number and v >= 12}.

The program verifies

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
paper.  It then verifies the criterion

    F_5(L) union (1 + F_3(L)) union (2 + F_1(L))

on [0,211], and confirms that its complement is exactly

    {8, 11, 24, 38, 49, 50, 51, 209, 210, 211}.

For N = 4m + 2, these m-values correspond to

    {34, 46, 98, 154, 198, 202, 206, 838, 842, 846}.

This list concerns only the residue class N congruent to 2 modulo 4.  Therefore
44 does not occur in this particular list.  The exceptional value 44 lies in
the residue class 0 modulo 4 and is detected separately by the direct
dynamic-programming check described below.


(E) Independent finite-range cross-check of r(N)

For every N in the selected finite range, the program independently generates
all positive primitive Dyck numbers not exceeding the bound and computes r(N)
by unbounded coin-change dynamic programming.

For the default bound 2000, it verifies

    r(46) = 8;

    the values with r(N) = 7 are exactly
    {34, 44, 98, 154, 198, 202, 206, 838, 842, 846};

    46 is the only checked value with r(N) = 8;

    no checked even N has r(N) > 8;

    every checked even N in [848,2000] has r(N) <= 6.

Changing --bound changes only the upper endpoint of this independent
finite-range cross-check.


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
    PASS: the six-summand criterion matches the paper
    PASS: the complement is the stated ten-element set
    PASS: exceptional m-values are
          [8, 11, 24, 38, 49, 50, 51, 209, 210, 211]
    PASS: corresponding N=4m+2 values are
          [34, 46, 98, 154, 198, 202, 206, 838, 842, 846]
    PASS: r(46)=8
    PASS: the r=7 values in the checked range are exactly the stated ten
    PASS: 46 is the only r=8 value in the checked range
    PASS: no checked even N has r(N)>8
    PASS: every checked even N in [848,2000] has r(N)<=6
    PASS: finite-range r(N) cross-check gives
          r(N)=7 at [34, 44, 98, 154, 198, 202, 206, 838, 842, 846]
          r(N)=8 at [46]
    PASS: all certificates verified

If --bound is changed, the line containing [848,2000] will display the selected
upper bound instead.


7. Failure behavior
-------------------

Every verified statement is reported with a line beginning with "PASS:".

If a check fails, the program prints a line beginning with "FAIL:" and raises an
AssertionError immediately.  Thus a complete run ending with

    PASS: all certificates verified

means that every finite certificate and every finite-range check requested in
that run has passed.


8. Scope of the computation
---------------------------

The program reproduces the finite certificates used in the paper and provides
an independent finite-range cross-check of r(N).  The dynamic-programming
calculation by itself is not intended to replace the paper's proofs for all
integers.  The infinite assertions are established in the paper by the
interval-propagation and self-similarity arguments; the program verifies the
finite base certificates and supplies an additional finite computational
cross-check.


9. Reproducibility
------------------

The version archived with the paper should be identical to the version at the
commit cited in the paper.  To preserve reproducibility, do not replace the
archived script by a later version without also updating the cited commit and
this README.
