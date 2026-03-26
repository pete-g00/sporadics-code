G0 := Sp(6,3);
G := Normalizer(GL(6,3), G0);

M := MaximalSubgroups(G : OrderEqual := 2^11*3^4); // $\SL_2(3) \wr \Sym(3)$
M := [A`subgroup : A in M][1];

C := Subgroups(M : OrderEqual := 2^9 * 3^3 * 2^2); // $2^{3+6} : 3^{1+2}_+ : 2^2$
C := [A`subgroup : A in C];
OutFW := [A : A in C | not IsAbelian(Sylow(A,3))][1]; 

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// $\Aut_F(S)$ determines $\Aut_F(W)$
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

OutSW := Sylow(OutFW, 3);
N1 := Normalizer(OutFW, OutSW);
N2 := Normalizer(G, N1);

Index(N2, N1); // 1
OutF0W := OutFW meet G0;

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// $\Aut_F(S)$ determines $N_F(W)$
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
f := PermutationRepresentation(OutFW);

OutFW := f(OutFW);
OutF0W := f(OutF0W);
NOutSW := f(N1);

T := IrreducibleModules(OutFW, GF(3));

// the module we're looking for is s.t. $\Out_{F_0}(W) = \Sp_6(3) \cap \Out_F(W)$ acts trivially on $Z(S)$
T := [A : A in T | Dimension(A) eq 1 and Dimension(Fix(A)) eq 0 and Dimension(Fix(Restriction(A, OutF0W))) eq 1];
#T; // 1

V := T[1];
CohomologicalDimension(Restriction(V, NOutSW), 1); // 0
