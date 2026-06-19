LMGpResidue := function(G,p)
    return LMGNormalClosure(G, LMGSylow(G,p));
end function;

M := ClassicalMaximals("S", 10, 3);
G := sub<GL(10,3) | M[1], M[2]>;

V := GModule(G);
M := [A : A in M | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Maximal subgroups $M$ of $\Sp_8(3)$ of interest are $M_i$ for $1 \leq i \leq 6$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
M1 := [A : A in M | #A eq 2 * 3^9 * #Sp(8,3)][1]; // $M_1 := 2 \times 3^{1+8}_+ : \Sp_8(3)$, 
M2 := [A : A in M | #A eq 3^15 * 48 * #Sp(6,3)][1]; // $M_2 := 3^{3+12} : (\GL_2(3) \times \Sp_6(3))$, 
M3 := [A : A in M | #A eq 3^15 * #GL(5,3)][1]; // $M_3 := 3^{15} : \GL_5(3)$, 
M4 := [A : A in M | #A eq 3^18 * #GL(4,3) * 24 and #Center(pCore(A,3)) eq 3^10][1]; // $M_4 := 3^{10+8} : (\GL_4(3) \times \Sp_2(3))$, 
M5 := [A : A in M | #A eq 3^18 * #GL(3,3) * #Sp(4,3) and #Center(pCore(A,3)) eq 3^6][1]; // $M_5 := 3^{6+12} : (\GL_3(3) \times \Sp_4(3))$, 
M6 := [A : A in M | #A eq 2 * #PSU(5,2)][1]; // $M_6 := 2 \times \PSU_5(2)$,
M7 := [A : A in M | #A eq #Sp(2,3) * #SO(5,3)][1]; // $M_7 := \Sp_2(3) \circ \GO_5(3)$

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_1)$, then no involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := LMGpResidue(M1,3);
#LMGCenter(L); // should equal 3
L2 := LMGSylow(L,2);
A := LMGConjugacyClasses(L2);
A := [a[3] : a in A | a[1] eq 2]; // involutions only
T := [CentraliserOfInvolution(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_2)$, then no non-central involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := LMGpResidue(M2,3);
#LMGCenter(L); // should equal 2
L2 := LMGSylow(L,2);
A := LMGConjugacyClasses(L2);
A := [a[3] : a in A | a[1] eq 2 and not a[3] in Center(L)]; // involutions only
T := [CentraliserOfInvolution(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_3)$, then no involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := LMGpResidue(M3,3);
#LMGCenter(L); // should equal 1
L2 := LMGSylow(L,2);
A := LMGConjugacyClasses(L2);
A := [a[3] : a in A | a[1] eq 2]; // involutions only
T := [CentraliserOfInvolution(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_4)$, then no non-central involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := LMGpResidue(M4,3);
#LMGCenter(L); // should equal 2
L2 := LMGSylow(L,2);
A := LMGConjugacyClasses(L2);
A := [a[3] : a in A | a[1] eq 2 and not a[3] in Center(L)]; // involutions only
T := [CentraliserOfInvolution(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// If $L := O^{3')(M_5)$, then no involution $t \in T$ is such that $S_0 \in \Syl_3(C_L(t))$ satisfies $|C_V(S_0)| = 3$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
L := LMGpResidue(M5,3);
#LMGCenter(L); // should equal 1
L2 := LMGSylow(L,2);
A := LMGConjugacyClasses(L2);
A := [a[3] : a in A | a[1] eq 2]; // involutions only
T := [CentraliserOfInvolution(L,a) : a in A];
T := [A : A in T | Dimension(Fix(Restriction(V,LMGSylow(A,3)))) eq 1];
#T; // should equal 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Inside $M_6$, $|C_V(A)| = 3^4$ for some complement $A$ of $N \cong 3^{1+2}_+$ inside $S \in \Syl_3(M_6)$.
// $O^{3'}(M_6)$ acts irreducibly on $V$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
S := LMGSylow(M6,3);
N := NormalSubgroups(S);
N := [A`subgroup : A in N];
N := [A : A in N | #A eq 3^3 and IdentifyGroup(A) eq <3^3, 3>];

f := PermutationRepresentation(S);
N := [f(A) : A in N];
A := [Complements(Image(f),A) :A  in N];
A := [(f^-1)(T) : T in X, X in A];
{Dimension(Fix(Restriction(V,X))) : X in A}; // equals 3 or 4

Dimension(Fix(Restriction(V, LMGpResidue(M6,3)))); // equals 0

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// Inside $M_7$, $|C_V(A)| = 3^3$ for every complement $A$ of $N \cong 3^{1+2}_+$ inside $S \in \Syl_3(M_6)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
S := LMGSylow(M7,3);
N := NormalSubgroups(S);
N := [A`subgroup : A in N];
N := [A : A in N | #A eq 3^3 and IdentifyGroup(A) eq <3^3, 3>];

f := PermutationRepresentation(S);
N := [f(A) : A in N];
A := [Complements(Image(f),A) :A  in N];
A := [(f^-1)(T) : T in X, X in A];
{Dimension(Fix(Restriction(V,X))) : X in A}; // equals 3
