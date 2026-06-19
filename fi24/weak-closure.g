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
# $U = C_Q(Z_2(Q))$
# -------------------------------------------------------------------------------------------------
U := Intersection(Q, R);
UQ := UpperCentralSeries(Q);;
U = Centralizer(Q, UQ[4]); # true

# -------------------------------------------------------------------------------------------------
# $U = C_R(Z_4(R)/Z_2(R))$
# -------------------------------------------------------------------------------------------------

UR := UpperCentralSeries(R);;
U = StepCentralizer(R, UR[4], UR[6]); # true

# -------------------------------------------------------------------------------------------------
# $\gamma_7(S) = \gamma_6(R) = \gamma_5(P)$
# -------------------------------------------------------------------------------------------------
L := LowerCentralSeries(S);;
LP := LowerCentralSeries(P);;
LR := LowerCentralSeries(R);

L[7] = LR[6];
L[7] = LP[5];
