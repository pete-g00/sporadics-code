// Computes $O^{p'}(G)$
pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := SL(5,3);
V := GModule(G);

M := MaximalSubgroups(G);
M := [A`subgroup : A in M];

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_6(3)$ satisfying $|C_V(S)| = 3$ are $M_i$ for $1 \leq i \leq 5$, including modulo $O_3(M)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

M := [A : A in M | Index(A, pCore(A,3)) mod 3^4 eq 0];
M := [A : A in M | Index(A, pCore(A,3)) mod 3^5 eq 0 or IdentifyGroup(Sylow(A/pCore(A,3),3)) eq <3^4, 7>];
#M; // should be equal to 3

M0 := [A : A in M | #pCore(A,3) ne 1];
M1 := M0[1]; // $M_1 := 3^4 : \GL_4(3)$
M2 := M0[2]; // $M_2 := 3^4 : \GL_4(3)$
M3 := [A : A in M | #pCore(A,3) ne 1][1]; // $M_3 := \PSp_4(3) : 2$

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
// If $L := O^{3')(M_2)$, then no involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := pResidue(M2, 3);
A := ConjugacyClasses(L);
A := [a[3] : a in A | a[1] eq 2]; // involutions only
T := [Centralizer(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,Sylow(A,3)))) eq 1];
#T; // should equal 0
