S := PcGroupCode(
13741491938431806455657762112574406588684703498867453558824558564013195548929578751329924342130079075234146575466397002123106897939463680, 3^10);

C := CharacteristicSubgroups(S);;

V := First(C, A -> IsElementaryAbelian(A) and Size(A) = 3^6);
W := First(C, A -> Exponent(A) = 3 and Size(A) = 3^7 and Rank(A) = 6);

U := UpperCentralSeries(S);;
Z2S := U[5];

R := Centralizer(S, Z2S);
Q := ClosureGroup(V,W);

q := NaturalHomomorphismByNormalSubgroup(S,W);;
C := SubgroupsSolvableGroup(Image(q));
C := Filtered(C, A -> Size(A) = 3 and A <> Center(Image(q)));
C := List(C, A -> PreImage(q, A));

Y := First(C, A -> Normalizer(S,A) = Q);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(Y)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------

UY := UpperCentralSeries(Y);
Z2Y := UY[2];

Index(Y,W); # should be 3
Index(W, Z2Y); # should be 3^2
Index(Z2Y, FrattiniSubgroup(Y)); # should be 3^2

CommutatorSubgroup(FrattiniSubgroup(Y), Normalizer(S,Y)) = Center(Y); # should be true

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(Q)) \cong \Alt(4)$
# -------------------------------------------------------------------------------------------------

V0 := CommutatorSubgroup(S,V);

Index(V, V0); # should be 3;
Index(V0, FrattiniSubgroup(Q)); # should be 3

Index(Q, V); # should be $3^3$

Centralizer(Q, FrattiniSubgroup(Q)) = V; # should be true

CommutatorSubgroup(FrattiniSubgroup(Q), Q) = Center(S); # should be true
Center(S) = Center(Q); # should be true

Intersection(V,W) = FrattiniSubgroup(Q); # should be true

AutQ := AutomorphismGroupPGroup(Q);;
AutQ.size mod 13; # non-zero

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------

UR := UpperCentralSeries(R);
Z2R := UR[3];
Z3S := U[4];

CR := Centralizer(R, Z2R);

Index(CR, FrattiniSubgroup(R)); # index 3
Index(R, CR); # index 3^2

Z2R = Z3S; # should be true
Center(R) = Z2S; # should be true
