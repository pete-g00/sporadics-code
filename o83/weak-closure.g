# action of OnImage (on the image of a nice monomorphism for $\Aut(S)$)
OnImageNM := function(n)
    return function(x, phi)
        return Image(PreImagesRepresentative(n,phi), x);
    end;
end;

G := SimpleGroup("O(+1,8,3)");
S := SylowSubgroup(G, 3);

M := MaximalSubgroups(S);;

NGM := List(M, A -> Normalizer(G,A));;

I := Filtered([1..Length(M)], i -> PCore(NGM[i],3) = M[i]);

M := M{I};;
NGM := NGM{I};;

i := PositionProperty(M, A -> Center(A) <> Center(S));

R := M[i];
NGR := NGM[i];

I := PositionsProperty(M, A -> Center(A) = Center(S));

Ex := M{I};
NGX := NGM{I};

NGT := List(NGX, A -> ClosureGroup(A, NGR));
T := List(NGT, A -> PCore(A,3));

NGU := List([1..2], i -> ClosureGroup(NGX[i], NGX[i+1]));
Add(NGU, ClosureGroup(NGX[3], NGX[1]));
U := List(NGU, X -> PCore(X,3));

V := List(NGU, A -> ClosureGroup(NGR,A));
NGV := List(NGU, A -> ClosureGroup(NGR,A));
V := List(NGV, A -> PCore(A,3));

NGW := ClosureGroup(NGX[1], ClosureGroup(NGX[2], NGX[3]));
W := PCore(NGW,3);

f := IsomorphismPcGroup(S);;
S := Image(f);

R := Image(f, R);
Ex := List(Ex, X -> Image(f,X));

T := List(T, A -> Image(f,A));
U := List(U, A -> Image(f,A));
V := List(V, A -> Image(f,A));

W := Image(f,W);

# -------------------------------------------------------------------------------------------------
# $T_i$ weak closure argument
# -------------------------------------------------------------------------------------------------

UX := List(Ex, UpperCentralSeries);
Z2X := List(UX, A -> A[3]);
T = List([1..3], i -> Centralizer(Ex[i], Z2X[i])); # should be true

AutS := AutomorphismGroup(S);
n := NiceMonomorphism(AutS);
AutS := Image(n);

NT := List(T, A -> Stabilizer(AutS, A, OnImageNM(n)));

List(NT, A -> Index(AutS, A)); # index 3 in each case

List(T, A -> Centralizer(R, Center(A))) = T; # should be true

UR := UpperCentralSeries(R);
Z2R := UR[2];

US := UpperCentralSeries(S);
Z3S := US[3];
Z2S := US[4];

Z2R = Z3S; # should be true
Center(R) = Z2S; # should be true

ForAll(T, A -> IsSubset(Center(A), Center(R))); # should be true
ForAll(T, A -> IsSubset(Z2R, Center(A))); # should be true

# -------------------------------------------------------------------------------------------------
# $V_i$ weak closure argument
# -------------------------------------------------------------------------------------------------

Index(Intersection(T[1], T[2]), V[1]); # should be 3
Index(Intersection(T[2], T[3]), V[2]); # should be 3
Index(Intersection(T[3], T[1]), V[3]); # should be 3

# $T_i \cap T_{i+1}$ is nonabelian, meaning that $J(T_i \cap T_{i+1})$ must be contained in a maximal subgroup.
# But a maximal subgroup is maximal elementary abelian, so $J(T_i \cap T_{i+1}) = V_i$.
IsAbelian(Intersection(T[1], T[2])); # should be false
IsAbelian(Intersection(T[2], T[3])); # should be false
IsAbelian(Intersection(T[1], T[3])); # should be false

NV := List(V, A -> Stabilizer(AutS, A, OnImageNM(n)));

List(NV, A -> Index(AutS, A)); # index 3 in each case

# -------------------------------------------------------------------------------------------------
# $U_i$ weak closure argument
# -------------------------------------------------------------------------------------------------

ForAll(Ex, A -> IsSubset(W,CommutatorSubgroup(S, A))); # should be true

NU := List(U, A -> Stabilizer(AutS, A, OnImageNM(n)));

List(NU, A -> Index(AutS, A)); # index 3 in each case
