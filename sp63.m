pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(6,3);
M := MaximalSubgroups(G);
V := GModule(G);
M := [A`subgroup : A in M];

// ---------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_6(3)$ satisfying $|C_V(S)| = 3$ are: 
// $\SL_2(27) : 3$, $\SL_2(3) \wr \Sym(3)$, $3^6 : \GL_3(3)$ and $3^{1+4}_+ : (2 \times \Sp_4(3))$.
// ---------------------------------------------------------------------------------------------------

// not the 3-locals
M0 := [A : A in M | #pCore(A,3) eq 1];
R0 := [Restriction(V,Sylow(A,3)) : A in M0];
I := [i : i in [1..#R0] | Dimension(Fix(R0[i])) eq 1];

#I; // should equal 2

// these are (in some order): \SL_2(27) : 3, \SL_2(3) \wr \Sym(3)
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

// these are (in some order): 3^6 : \SL_3(3), 3^{1+4} : (2 \times \Sp_4(3))
ChiefFactors(M1[I[1]]);
ChiefFactors(M1[I[2]]);


// ---------------------------------------------------------------------------------------------------
// no subgroup $G$ of $\SL_2(27) : 3$ with a Sylow $3$-subgroup that 
// is elementary abelian of order $9$ satisfies $O_3(G) = 1$.
// ---------------------------------------------------------------------------------------------------
H := [A : A in M0 | #A eq #SL(2,27)*3][1];
C := Subgroups(H : OrderMultipleOf := 3^2);
C := [A`subgroup : A in C];
C := [A : A in C | <3,2> in FactoredOrder(A) and #pCore(A,3) eq 1];
#C; // should be 0

// ---------------------------------------------------------------------------------------------------
// the subgroups of $\SL_2(3) \wr \Sym(3)$ that satisfy the hypothesis.
// ---------------------------------------------------------------------------------------------------

H := [A : A in M0 | #A eq #SL(2,3)^3 * #Sym(3)][1];
C := Subgroups(H : OrderMultipleOf := 3^2);
C := [A`subgroup : A in C];
C := [A : A in C | <3,2> in FactoredOrder(A) and #pCore(A,3) eq 1 pResidue(A,3) eq A];
R := [Restriction(V, Sylow(A,3)) : A in C];
I := [i : i in [1..#R] | Dimension(Fix(R[i])) eq 1];
#I; // should be 4
C := [A[i] : i in I];
C3 := [CyclicSubgroups(A : OrderEqual := 3) : A in C];
C3 := [[A`subgroup : A in T] : T in C3];

R := [[Restriction(V,T) : T in A] : A in C3];
[{Dimension(Fix(T)) : T in R} : i in I]; // only one of these is a singleton

// Cohomolgical dimension valid
> [CohomologicalDimension(Restriction(V,A), 1) : A in C];
[ 0, 0, 0, 0 ]