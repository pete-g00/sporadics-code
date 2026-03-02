G := SimpleGroup("O(+1,8,3)");
S := SylowSubgroup(G, 3);

f := IsomorphismPcGroup(S);;
S := Image(f);

M := MaximalSubgroups(S);;
M := List(M, A -> PreImage(f,A));;

NGM := List([1..Length(M)], i -> Normalizer(G, M[i]));

I := Filtered([1..Length(M)], i -> Size(Center(M[i])) = 3 and PCore(NGM[i],3) = M[i]);

Ex := M{I};

Ex := List(Ex, A -> Image(f, A));

UX := List(Ex, UpperCentralSeries);
Z2X := List(UX, A -> A[2]);

T := List(Z2X, A -> Centralizer(S, A));

U := UpperCentralSeries(S);
Z3S := U[3];

Z3S = ClosureGroup(Center(T[1]), ClosureGroup(Center(T[2]), Center(T[3]))); # should be true

Centralizer(S, Z3S) = Z3S; # $C_S(Z_3(S)) = Z_3(S)$

List(T, A -> Index(Center(A), CommutatorSubgroup(Z3S, A))); # index 3^3 in each case
