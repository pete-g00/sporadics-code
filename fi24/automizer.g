OnQuotient := function(q)
    return function(t, x)
        return Image(q, PreImagesRepresentative(q,t)^x);
    end;
end;

# Computes C_G(A/U)
StepCentralizer := function(G, A, U)
    local q;
    q := NaturalHomomorphismByNormalSubgroup(G,U);
    return Kernel(ActionHomomorphism(G, Image(q,A), OnQuotient(q)));
end;

S := PcGroupCode(309006671086643171365690013478419223422146419245621383014393275579900089503571985049825827274917877880413672117829626994604814968815355115731625550330860924855700989042210232916254354107938195029060626374894949041217664136296342589730787701682021618677117195758162844063606096434038369504373899240344126522246355899558729671013315570791817251132593244445345256634484919025000728822888627478848123717501587299377424814778726064133279372383948353751027594400191396612743909292104407825863383758706429271968629216195707374558638997536,
    3^16
);

M := MaximalSubgroups(S);;
M := Filtered(M, A -> Exponent(A) = 9);;
W := First(CharacteristicSubgroups(S), A -> Rank(A) = 10 and Exponent(A) = 3 and Size(A) = 3^11);

P := First(M, A -> Intersection(A,W) = W and not IsAbelian(A/W));
Q := First(M, A -> Intersection(A,W) = W and IsAbelian(A/W));
R := First(M, A -> Size(Center(A)) = 9);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(P)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------
W0 := StepCentralizer(P, P, W);
UP := UpperCentralSeries(P);

Z5P := UP[2];
Z4P := UP[3];
Z2P := UP[5];

IsSubset(Z4P, DerivedSubgroup(W0)); # should be true
Index(CommutatorSubgroup(P, W0), Intersection(Z4P, CommutatorSubgroup(P, W0))); # should be 3
Index(Z5P, FrattiniSubgroup(P)); # should be 3

LP := LowerCentralSeries(P);

L4P := LP[4];
CL4P := Centralizer(P, L4P);
Index(L4P, Z2P); # should be 3
Index(CL4P, Intersection(CL4P, FrattiniSubgroup(P))); # should be 3

LS := LowerCentralSeries(S);
T := Centralizer(S, LS[7]);

CommutatorSubgroup(P, Center(T)) = Center(P); # should be true

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R)) \cong \SL_2(3)$
# -------------------------------------------------------------------------------------------------

UR := UpperCentralSeries(R);

Z6R := UR[2];
Z5R := UR[3];
Z4R := UR[4];
Z3R := UR[5];
Z2R := UR[6];

Index(T, Z6R); # should be 3
ClosureGroup(FrattiniSubgroup(R), Z5R) = Z6R; # should be true

B2 := Intersection(Z2R, FrattiniSubgroup(R));
B3 := Intersection(Z3R, FrattiniSubgroup(R));
B4 := Intersection(Z4R, FrattiniSubgroup(R));

Index(B4, B3); # should be 3
Index(B3, B2); # should be 3

B2 = Z2R; # should be true

