// Computes $O^{p'}(G)$
pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

G := Sp(6,3);
V := GModule(G);

M := MaximalSubgroups(G);
M := [A`subgroup : A in M];

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_6(3)$ satisfying $|C_V(S)| = 3$ are $M_i$ for $1 \leq i \leq 5$
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

M := [A : A in M | Dimension(Fix(Restriction(V, Sylow(A,3)))) eq 1];
#M; // should equal 5

M1 := [A : A in M | #A eq 2^8*3^9*5][1]; // $M_1 := 2 \times 3^{1+4}_+ : \Sp_4(3)$
M2 := [A : A in M | #A eq 2^7*3^9][1]; // $M_2 := 3^{3+4} : (\GL_2(3) \times \SL_2(3))$, 
M3 := [A : A in M | #A eq 2^5*3^9*13][1]; // $M_3 := 3^6 : \GL_3(3)$
M4 := [A : A in M | #A eq 2^10*3^4][1]; // $M_4 := \SL_2(3) \wr \Sym(3)$
M5 := [A : A in M | #A eq 2^3*3^4*7*13][1]; // $M_5 := \SL_2(27) : 3$. 

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
// If $L := O^{3')(M_2)$, then no central involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := pResidue(M2, 3);
A := ConjugacyClasses(L);
A := [a[3] : a in A | a[1] eq 2 and not a[3] in Center(L)]; 
T := [Centralizer(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,Sylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// No maximal subgroup $N$ of $M_5$ satisfies both $O_3(N) = 1$ and $|C_V(S_0)| = 1$ for $S_0 \in \Syl_3(N)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
N := MaximalSubgroups(M5);
N := [A`subgroup : A in N];
N := [A : A in N | #pCore(A,3) eq 1 and Dimension(Fix(Restriction(V,Sylow(A,3)))) eq 1];
#N; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// The subgroups of interest inside $M_4$ are precisely $U_i$ for $1 \leq i \leq 3$, and $U_i$ acts irreducibly on $V$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

U := Subgroups(M4 : OrderMultipleOf := 3^2);
U := [A`subgroup : A in U];
U := [A : A in U | <3,2> in FactoredOrder(A) and IsElementaryAbelian(Sylow(A,3))];
U := [A : A in U | #pCore(A,3) eq 1 and pResidue(A,3) eq A and Dimension(Fix(Restriction(V,Sylow(A,3)))) eq 1];
#U; // should equal 3

GroupName(U[1]); // SL(2,3) x A4
ChiefFactors(U[2]); // 2^{3+4} : 3^2
ChiefFactors(U[3]); // 2^{3+6} : 3^2

U := [A : A in U | IsIrreducible(Restriction(V,A))];
#U; // still equal to 3
