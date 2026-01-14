# Aut_F(W) determines N_F(W) (cohomology result)

F:=GF(3);

x:=CambridgeMatrix(1,F,12,[
"010000000000",
"200000000000",
"000100000000",
"002000000000",
"000001000000",
"000020000000",
"000000010000",
"000000200000",
"000000000010",
"000000000001",
"000000002000",
"000000000200"]);

y:=CambridgeMatrix(1,F,12,[
"001000000000",
"112000000000",
"202000000000",
"000010000000",
"121220000000",
"000000100000",
"000000001000",
"000000000100",
"000001000000",
"000001121200",
"011212110210",
"011210201001"]);

G := MatrixGroup<12,F|x,y>;

// L acts trivially on Z(S) = Z(W)
L := DerivedSubgroup(G);

S := LMGSylow(G, 3);
NGS := Normalizer(G, S);
NLS := Normalizer(L, S);

f := PermutationRepresentation(NGS);
NGS := Image(f);
NLS := f(NLS);

NGS, g := DegreeReduction(NGS);
NLS := g(NLS);

T := IrreducibleModules(NGS, GF(3));
T := [A : A in T | Dimension(A) eq 1 and Dimension(Fix(Restriction(A, NLS))) ne 0 and Dimension(Fix(A)) eq 0];
{CohomologicalDimension(A, 1) : A in T}; // {0}
