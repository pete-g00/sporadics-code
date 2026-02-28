pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(8,3);
M := MaximalSubgroups(G);
V := GModule(G);
M := [A`subgroup : A in M];

M := [A : A in M | Dimension(Fix(Restriction(V, Sylow(A,3)))) eq 1];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^4 eq 0];

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_8(3)$ of interest are $M_i$ for $1 \leq i \leq 6$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

M1 := [A : A in M | #A eq 2^11*3^16*5*7*13][1]; // $M_1 := 2 \times 3^{1+6}_+ : \Sp_6(3)$
M2 := [A : A in M | #A eq 2^11*3^16*5][1]; // $M_2 := 3^{8+3} : (\GL_2(3) \times \Sp_4(3))$
M3 := [A : A in M | #A eq 2^8*3^16*13][1]; // $M_3 := 3^{6+6} : (\GL_3(3) \times \SL_2(3))$
M4 := [A : A in M | #A eq 2^9*3^16*5*13][1]; // $M_4 := 3^{10} : \GL_4(3)$
M5 := [A : A in M | #A eq 2^13*3^4*5][1]; // $M_5 := 2^{1+6}_- \ldotp \PSU_4(2)$
M6 := [A : A in M | #A eq 2^3*3^4*7*13][1]; // $M_6 := \SL_2(3^3) \ldotp 3$


// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_1)$, then no involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := pResidue(M1, 3);
A := ConjugacyClasses(L);
A := [a[3] : a in A | a[1] eq 2]; // involutions only
T := [Centralizer(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,Sylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $T := O^{3'}(M_2)'$, then $|C_V(S_0)| > 3$ for $S_0 \in \Syl_3(T)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
T := DerivedSubgroup(pResidue(M2,3));
Dimension(Fix(Restriction(V, Sylow(T,3)))); // should be 2

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// No subgroup $T$ of $M_4$ isomorphic to $\Sp_4(3)$ satisfies $|C_V(S_0)| > 3$ for $S_0 \in \Syl_3(T)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
T := PerfectSubgroups(M4 : OrderEqual := #Sp(4,3));
T := [A`subgroup : A in T];
T := [A : A in T | Dimension(Fix(Restriction(V, Sylow(A,3)))) eq 1];
#T; // should be 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $S_0 \in \Syl_3(M_6)$ and $E \leq S_0$ is isomorphic to $3^{1+2}_+$, then $|C_V(E)| = 3$
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
S6 := Sylow(M6, 3);
A6 := MaximalSubgroups(S6);
A6 := [A`subgroup : A in A6 | IsElementaryAbelian(A`subgroup)][1];
C6 := Subgroups(A6 : OrderEqual := 3);
C6 := [A`subgroup : A in C6];
4 in [Dimension(Fix(Restriction(V,A))) : A in C6]; // should be false

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// A Sylow $3$-subgroup of $M_5$ satisfies all the hypotheses, and the subgroups $G$ of interest are the intermediate
// subgroups of $2^{1+6}_- : (3 \wr 3)$ and $2^{1+6}_- \ldotp \PSU_4(2)$, and $G$ acts irreducibly on $V$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
S5 := Sylow(M5, 3);
A5 := MaximalSubgroups(S5);
A5 := [A`subgroup : A in A5 | IsElementaryAbelian(A`subgroup)][1];
C5 := Subgroups(A5 : OrderEqual := 3);
C5 := [A`subgroup : A in C5];
4 in [Dimension(Fix(Restriction(V,A))) : A in C5]; // should be true

C := Subgroups(M5 : OrderMultipleOf := 3^4);
C := [A`subgroup : A in C];
C := [A : A in C | #pCore(A,3) eq 1];
#C; // should be 6

#pCore(C[1], 2); // 2^7
#pCore(M5, 2); // 2^7

false in [IsIrreducible(Restriction(V,A)) : A in C]; // should be false, i.e. every restriction is irreducible. 
