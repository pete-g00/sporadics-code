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
R := First(M, A -> Size(Center(A)) = 9);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(P))$ normalizes both $\bfV_i$
# -------------------------------------------------------------------------------------------------
W0 := StepCentralizer(P, P, W);
I := IntermediateSubgroups(W0, W);;
I := I.subgroups;;

I := Filtered(I, A -> NilpotencyClassOfGroup(A) = 3);;
Z2I := List(I, A -> UpperCentralSeries(A)[2]);
V := List(Z2I, A -> Centralizer(P, A));;

ForAll(V, A -> IsElementaryAbelian(A) and Size(A) = 3^7); # should be true
V[1] = V[2]; # should be false

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R))$ normalizes both $\bfV_i$
# -------------------------------------------------------------------------------------------------
FR := FrattiniSubgroup(R);
LR := LowerCentralSeries(R);;
UFR := UpperCentralSeries(FR);;

Index(UFR[2], FrattiniSubgroup(FR)); # should be 3
Index(FrattiniSubgroup(FR), LR[5]); # should be 3

I := IntermediateSubgroups(UFR[2], LR[5]);;
I := I.subgroups;;
CI := List(I, A -> Centralizer(R,A));;
ForAll(CI, A -> Size(A) = 3^8); # should be true

J := PositionsProperty(CI, A -> ForAny(MaximalSubgroups(A), IsElementaryAbelian)); # should have 2 Values
Size(Intersection(CI{J})); # should be 3^6, i.e. the two eab subgroups of order 3^7 are distinct
