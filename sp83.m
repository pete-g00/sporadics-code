pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(8,3);
M := MaximalSubgroups(G);
V := GModule(G);
M := [A`subgroup : A in M];

// ---------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_8(3)$ of interest are -- $3^{8+3} : (\GL_2(3) \times \Sp_4(3))$, 
// $2^{1+6}_- \ldotp \PSU_4(2)$ and $\SL_2(27) \ldotp 3$.
// ---------------------------------------------------------------------------------------------------

// not the 3-locals
M0 := [A : A in M | #pCore(A,3) eq 1 and #A mod 3^4 eq 0];
R0 := [Restriction(V,Sylow(A,3)) : A in M0];
I := [i : i in [1..#R0] | Dimension(Fix(R0[i])) eq 1];

#I; // should equal 2

// these are (in some order): $2^{1+6}_- \ldotp \PSU_4(2)$ and $\SL_2(27) \ldotp 3$
ChiefFactors(M0[I[1]]); 
ChiefFactors(M0[I[2]]);

// the 3-locals
M1 := [A : A in M | #pCore(A,3) ne 1];
S := [Sylow(A,3) : A in M1];
P := [pCore(A,3) : A in M1];
F := [PermutationRepresentation(A) : A in S];
C := [Complements((F[i])(S[i]), (F[i])(P[i])) : i in [1..#P]];
C := [[(F[i]^-1)(X) : X in C[i]] : i in [1..#C]];

R1 := [[Restriction(V,A) : A in T] : T in C];
I := [i : i in [1..#R1] | 1 in {Dimension(Fix(T)) : T in R1[i]}];

#I; // should equal 2

// these are (in some order): $2^{1+6}_- \ldotp \PSU_4(2)$ and $\SL_2(27) \ldotp 3$
ChiefFactors(M1[I[1]]);
ChiefFactors(M1[I[2]]);


// the 3-locals
M1 := [A : A in M | #pCore(A,3) ne 1];
S := [Sylow(A,3) : A in M1];
P := [pCore(A,3) : A in M1];
F := [PermutationRepresentation(A) : A in S];
C := [Complements((F[i])(S[i]), (F[i])(P[i])) : i in [1..#P]];
C := [[(F[i]^-1)(X) : X in C[i]] : i in [1..#C]];

R1 := [[Restriction(V,A) : A in T] : T in C];
I := [i : i in [1..#R1] | 1 in {Dimension(Fix(T)) : T in R1[i]}];

#I; // should equal 1

// these are (in some order): 3^6 : $3^{8+3} : (\GL_2(3) \times \Sp_4(3))$
ChiefFactors(M1[I[1]]);


// ruling out SL_2(27) : 3

Type ? for help.  Type <Ctrl>-D to quit.
> G := Sp(8,3);
> M := MaximalSubgroups(G);
> M := [A`subgroup : A in M];
> #M;
13
>
> [FactoredOrder(A) : A in M];
[
    [ <2, 3>, <3, 4>, <7, 1>, <13, 1> ],
    [ <2, 8>, <3, 3>, <5, 1> ],
    [ <2, 13>, <3, 4>, <5, 1> ],
    [ <2, 10>, <3, 6>, <5, 1>, <13, 1> ],
    [ <2, 15>, <3, 5> ],
    [ <2, 12>, <3, 6>, <5, 1>, <7, 1> ],
    [ <2, 10>, <3, 8>, <5, 2>, <41, 1> ],
    [ <2, 15>, <3, 8>, <5, 2> ],
    [ <2, 8>, <3, 16>, <13, 1> ],
    [ <2, 13>, <3, 10>, <5, 1>, <7, 1>, <13, 1> ],
    [ <2, 9>, <3, 16>, <5, 1>, <13, 1> ],
    [ <2, 11>, <3, 16>, <5, 1> ],
    [ <2, 11>, <3, 16>, <5, 1>, <7, 1>, <13, 1> ]
]
> [FactoredOrder(pCore(A,2)) : A in M];
[
    [ <2, 1> ],
    [ <2, 3> ],
    [ <2, 7> ],
    [ <2, 1> ],
    [ <2, 12> ],
    [ <2, 2> ],
    [ <2, 1> ],
    [ <2, 2> ],
    [ <2, 1> ],
    [ <2, 4> ],
    [ <2, 1> ],
    [ <2, 1> ],
    [ <2, 1> ]
]
> C := Subgroups(M[6] : OrderEqual := 2^7);
^C
[Interrupted]
> C := Subgroups(M[6] : OrderEqual := 2^7*3^4);
^C
[Interrupted]
> C := Subgroups(M[6] : OrderMultipleOf := 2^7*3^4);
> #C;
142
> C := [A`subgroup : A in C];
> C := [A : A in C | <3,4> in FactoredOrder(A)];
> #C;
18
> C := [A : A in C | #pCore(A,3) eq 1];
> #C;
8
> [GroupName(A) : A in C];
^C
[Interrupted]
> ChiefFactors(C[1]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[2]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[3]);
    G
    |  Cyclic(2)
    *
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[4]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[5]);
    G
    |  Cyclic(2)
    *
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[6]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[7]);
    G
    |  Cyclic(2)
    *
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[8]);
    G
    |  Cyclic(2)
    *
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
>
> ChiefFactors(M[6]);
    G
    |  Cyclic(2)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    *
    |  2A(3, 3)                   = U(4, 3)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2)
    1
> ChiefFactors(M[5]);
    G
    |  Cyclic(2)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(2) (2 copies)
    *
    |  Cyclic(3) (3 copies)
    *
    |  Cyclic(2) (8 copies)
    *
    |  Cyclic(2)
    *
    |  Cyclic(2) (2 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(M[4]);
    G
    |  Cyclic(2)
    *
    |  Cyclic(2)
    *
    |  A(3, 3)                    = L(4, 3)
    *
    |  Cyclic(2)
    1
> ChiefFactors(M[3]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(PSU(4,2));
    G
    |  C(2, 3)                    = S(4, 3)
    1
>
> C := Subgroups(M[3] : OrderMultipleOf := 2^7*3^4);
> #C;
6
> C := [A`subgroup : A in C];
> C := [A : A in C | <3,4> in FactoredOrder(A)];
> #C;
6
> C := [A : A in C | #pCore(A,3) eq 1];
> #C;
6
> [GroupName(A) : A in C];
[ C2.C2^6.He3.C3, C2.C2^6.He3.C6, C2.C2^6.C3^3.A4, C2.C2^6.C3^3.S4,
C2.C2^6.He3.Q8.C3, C2.C2^6.C(2,3) ]
> ChiefFactors(C[1]);
    G
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[2]);
    G
    |  Cyclic(2)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(3)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[3]);
    G
    |  Cyclic(3)
    *
    |  Cyclic(2) (2 copies)
    *
    |  Cyclic(3) (3 copies)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[4]);
    G
    |  Cyclic(2)
    *
    |  Cyclic(3)
    *
    |  Cyclic(2) (2 copies)
    *
    |  Cyclic(3) (3 copies)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[5]);
    G
    |  Cyclic(3)
    *
    |  Cyclic(2) (2 copies)
    *
    |  Cyclic(2)
    *
    |  Cyclic(3) (2 copies)
    *
    |  Cyclic(3)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> ChiefFactors(C[6]);
    G
    |  C(2, 3)                    = S(4, 3)
    *
    |  Cyclic(2) (6 copies)
    *
    |  Cyclic(2)
    1
> V := GModule(G);
>
> S := Sylow(C[6],3);
> L := CyclicSubgroups(S : OrderEqual := 3);
> L := [A`subgroup : A in S];

>> L := [A`subgroup : A in S];
          ^
Runtime error in `: Invalid attribute 'subgroup' for this object

> L := [A`subgroup : A in L];
>
> {Dimension(Fix(Restriction(V,T))) : T in L};
{ 3, 4 }
>
> ChiefFactors(M[1]);
    G
    |  Cyclic(3)
    *
    |  A(1, 27)                   = L(2, 27)
    *
    |  Cyclic(2)
    1
> S := Sylow(M[1],3);
> L := CyclicSubgroups(S : OrderEqual := 3);
> L := [A`subgroup : A in S];

>> L := [A`subgroup : A in S];
          ^
Runtime error in `: Invalid attribute 'subgroup' for this object

> L := [A`subgroup : A in L];
> {Dimension(Fix(Restriction(V,T))) : T in L};
{ 3, 4 }
> IsConjugate(G, Sylow(M[1],3), Sylow(C[6],3));
false
> N := Normalizer(G, Sylow(M[1],3));
> #N;
486
> N := Normalizer(G, Sylow(C[6],3));
> #N;
972
> GroupName(N);
(C3*C3wrC3):C2^2
> N := Normalizer(G, Sylow(M[1],3));
> GroupName(N);
C6*C3wrC3
> Sylow(M[1],3) meet Sylow(C[6],3);
MatrixGroup(8, GF(3)) of order 1
>
> L := CyclicSubgroups(S : OrderEqual := 9);
> L := [A`subgroup : A in L];
> {Dimension(Fix(Restriction(V,T))) : T in L};
{ 1 }
>
> S := Sylow(C[6],3);
> L := CyclicSubgroups(S : OrderEqual := 9);
> L := [A`subgroup : A in L];
> {Dimension(Fix(Restriction(V,T))) : T in L};
{ 1 }
>
> #L;
2
>
> S := Sylow(M[1],3);
> L := CyclicSubgroups(S : OrderEqual := 3);
> #L;
6
> L := CyclicSubgroups(S : OrderEqual := 9);
> #L;
2
>
> #S;
81
> GroupName(S);
C3wrC3
>
> L := CyclicSubgroups(S : OrderEqual := 3);
> #L;
6
> [Dimension(Fix(Restriction(V,T))) : T in L];

>> [Dimension(Fix(Restriction(V,T))) : T in L];
                             ^
Runtime error in 'Restriction': Bad argument types
Argument types given: ModGrp, Rec

> L := [A`subgroup : A in L];
> [Dimension(Fix(Restriction(V,T))) : T in L];
[ 3, 3, 3, 3, 3, 4 ]
>
> S := Sylow(C[6],3);
> L := CyclicSubgroups(S : OrderEqual := 9);
> L := CyclicSubgroups(S : OrderEqual := 3);
> [Dimension(Fix(Restriction(V,T))) : T in L];

>> [Dimension(Fix(Restriction(V,T))) : T in L];
                             ^
Runtime error in 'Restriction': Bad argument types
Argument types given: ModGrp, Rec

> L := [A`subgroup : A in L];
> [Dimension(Fix(Restriction(V,T))) : T in L];
[ 3, 3, 4, 4, 4, 4 ]
> L[1] in Center(C[6]);

>> L[1] in Center(C[6]);
        ^
Runtime error in 'in': Bad argument types

> L[1].1 in Center(C[6]);
false
> L[1].2 in Center(C[6]);

>> L[1].2 in Center(C[6]);
       ^
Runtime error in '.': Generator out of range

> L[2].1 in Center(C[6]);
false
> L[2].1 in Center(C[6]);
false
> L[3].1 in Center(C[6]);
false
> L[4].1 in Center(C[6]);
false
> L[5].1 in Center(C[6]);
false
> L[6].1 in Center(C[6]);
false
> #L;
6
> L[1];
MatrixGroup(8, GF(3)) of order 3
Generators:
    [2 0 0 2 2 2 1 0]
    [0 0 1 2 2 0 2 1]
    [2 1 0 1 0 0 0 0]
    [0 2 0 0 1 2 2 0]
    [2 2 0 0 0 0 1 1]
    [2 0 1 2 1 1 2 2]
    [0 1 0 2 1 2 2 0]
    [0 0 2 2 0 1 0 0]
> Center(C[6]);
MatrixGroup(8, GF(3)) of order 2
Generators:
    [2 0 0 0 0 0 0 0]
    [0 2 0 0 0 0 0 0]
    [0 0 2 0 0 0 0 0]
    [0 0 0 2 0 0 0 0]
    [0 0 0 0 2 0 0 0]
    [0 0 0 0 0 2 0 0]
    [0 0 0 0 0 0 2 0]
    [0 0 0 0 0 0 0 2]
> Center(S);
MatrixGroup(8, GF(3)) of order 3
Generators:
    [2 0 0 2 2 2 1 0]
    [0 0 1 2 2 0 2 1]
    [2 1 0 1 0 0 0 0]
    [0 2 0 0 1 2 2 0]
    [2 2 0 0 0 0 1 1]
    [2 0 1 2 1 1 2 2]
    [0 1 0 2 1 2 2 0]
    [0 0 2 2 0 1 0 0]
>
> L[1].1 in Center(S);
true
> L[2].1 in Center(S);
false
> L[3].1 in Center(S);
false
>
>
> S := Sylow(M[1],3);
> L := CyclicSubgroups(S : OrderEqual := 3);
> #L;
6
> [Dimension(Fix(Restriction(V,T))) : T in L];

>> [Dimension(Fix(Restriction(V,T))) : T in L];
                             ^
Runtime error in 'Restriction': Bad argument types
Argument types given: ModGrp, Rec

> L := [A`subgroup : A in L];
> [Dimension(Fix(Restriction(V,T))) : T in L];
[ 3, 3, 3, 3, 3, 4 ]
> L[1].1 in Center(S);
true
>
> A := MaximalSubgroups(S);
> A := [X`subgroup : X in A];
> [Dimension(Fix(Restriction(V,T))) : T in A];
[ 1, 1, 1, 2 ]
>
> GroupName(A[4]);
He3
>
> S := Sylow(M[2],3);
> A := MaximalSubgroups(S);
> A := [X`subgroup : X in A];
> [Dimension(Fix(Restriction(V,T))) : T in A];
[ 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ]
> #S;
27
>
> S := Sylow(C[6],3);
> A := MaximalSubgroups(S);
> A := [X`subgroup : X in A];
> [Dimension(Fix(Restriction(V,T))) : T in A];
[ 2, 1, 1, 1 ]
> GroupName(A[1]);
He3
>
> GroupName(A[2]);
C3^3
> Co := Complements(S, A[2]);

>> Co := Complements(S, A[2]);
                    ^
Runtime error in 'Complements': Bad argument types
Argument types given: GrpMat[FldFin], GrpMat[FldFin]

> f := PermutationRepresentation(S);
> Co := Complements(f(S), f(A[2]));
> #Co;
1
> [Dimension(Fix(Restriction(V,(f^-1)(T)))) : T in Co];
[ 4 ]
>
> S := Sylow(M[1],3);
> f := PermutationRepresentation(S);
> A := MaximalSubgroups(S);
> A := [X`subgroup : X in A];
> [Dimension(Fix(Restriction(V,T))) : T in A];
[ 1, 1, 1, 2 ]
> GroupName(A[1]);
C3^3
> Co := Complements(f(S), f(A[1]));
> #Co;
1
> [Dimension(Fix(Restriction(V,(f^-1)(T)))) : T in Co];
[ 4 ]
>
> GroupName(A[2]);
C9:C3
> GroupName(A[3]);
C9:C3
> GroupName(A[4]);
He3
>
> Co := Complements(f(S), f(A[4]));
> #Co;
3
> [Dimension(Fix(Restriction(V,(f^-1)(T)))) : T in Co];
[ 3, 3, 3 ]
>
> S := Sylow(C[6],3);
> A := MaximalSubgroups(S);
> A := [X`subgroup : X in A];
> [Dimension(Fix(Restriction(V,T))) : T in A];
[ 2, 1, 1, 1 ]
> GroupName(A[1]);
He3
>
> f := PermutationRepresentation(S);
> Co := Complements(f(S), f(A[1]));
> #Co;
3
> [Dimension(Fix(Restriction(V,(f^-1)(T)))) : T in Co];
[ 4, 3, 4 ]
>

// ruling out the 3-local sub
> S := Sylow(M[12],3);
> P := pCore(M[12],3);
>
> f := PermutationRepresentation(S);
> Co := Complements(f(S), f(P));
> #Co;
297
>
> Co := [(f^-1)(A) : A in Co];
> [Dimension(Fix(Restriction(V,T))) : T in Co];
[ 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2,
2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2,
2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3,
3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2,
2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3,
1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2 ]
> Co := [T : T in Co | Dimension(Fix(Restriction(V,T))) eq 1];
> #Co;
36
> A := [MaximalSubgroups(T) : T in Co];
> Co[1];
MatrixGroup(8, GF(3)) of order 3^5
Generators:
    [2 0 1 2 1 2 0 1]
    [0 1 2 0 2 2 0 2]
    [2 1 1 2 1 2 0 1]
    [1 0 2 0 2 0 0 2]
    [2 0 2 2 1 0 0 0]
    [0 1 2 2 2 2 1 0]
    [0 1 0 1 0 0 0 2]
    [0 2 2 0 1 1 2 1]

    [1 0 2 1 1 2 0 2]
    [1 2 0 0 2 0 2 0]
    [2 1 1 0 2 1 0 2]
    [2 0 0 1 0 2 2 1]
    [1 2 1 2 1 0 0 2]
    [2 1 2 1 0 1 0 1]
    [0 2 1 2 0 2 0 0]
    [2 0 2 1 1 1 2 1]

    [1 0 2 1 1 2 0 2]
    [0 1 0 0 0 0 0 0]
    [1 2 2 2 0 0 0 2]
    [2 1 2 2 0 0 0 1]
    [2 1 0 0 0 1 0 2]
    [1 2 0 0 1 0 0 1]
    [1 2 2 1 2 1 1 0]
    [2 1 1 2 1 2 0 1]

    [1 1 2 1 0 1 1 0]
    [0 0 2 1 2 0 2 1]
    [0 0 2 2 2 1 0 1]
    [0 2 1 0 0 2 2 0]
    [0 2 0 0 2 1 2 2]
    [0 1 0 0 2 0 1 1]
    [0 1 1 2 1 0 2 2]
    [0 0 0 0 0 0 0 1]

    [1 1 0 0 0 1 0 1]
    [1 2 2 1 0 2 2 1]
    [1 1 1 2 2 0 1 1]
    [2 1 0 1 0 0 2 0]
    [0 1 1 0 1 1 0 1]
    [2 2 0 0 1 1 1 1]
    [0 1 0 2 1 0 2 1]
    [0 0 0 2 0 0 2 2]
> #Co[1];
243
> GroupName(Co[1]);
C3*C3wrC3
>
> A := [[X`subgroup : X in T] : T in A];
> A := [[X : X in T | IdentifyGroup(X) eq <3^4, 7>] : T in A];
> #A;
36
> [#A : A in A];

>> [#A : A in A];
              ^
Runtime error: Variable 'A' has not been initialized

> [#T : T in A];
[ 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9 ]
>
> {{Dimension(Fix(Restriction(V,T))) : T in X} : X in A};
{
    { 1, 2 }
}
> A := [[T : T in X | Dimension(Fix(Restriction(V,T))) eq 1] : X in A];
> [#T : T in A];
[ 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6 ]
>
> Co := [X : X in T, T in A];
> #Co;
216
>
> A := [MaximalSubgroups(T) : T in Co];
> [#T : T in A];
[ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ]
>
>
> F := [PermutationRepresentation(X) : X in Co];
> A := [[X`subgroup : X in T] : T in A];
> A := [[X : X in T | IdentifyGroup(X) eq <3^3,3>] : T in A];
> [#T : T in A];
[ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ]
> A := [T[1] : T in A];
>
> Cm := [Complements(F[i](Co[i]), F[i](A[i])) : i in [1..#F]];
> [#A : A in Cm];
[ 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3 ]
>
> Cm := [[(F[i]^-1)(V) : V in Cm[i]] : i in [1..#F]];
>
> {{Dimension(Fix(Restriction(V,T))) : T in X} : X in Cm};
{
    { 3 }
}


// Cohomological Dimension
> V := GModule(G);
> {CohomologicalDimension(Restriction(V,A),1) : A in C};
{0}
