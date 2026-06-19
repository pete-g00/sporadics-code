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

# -------------------------------------------------------------------------------------------------
# If $A := 13 : 3$ is contained inside $G := \GL_3(3)$, then $N_G(A) = \langle A, Z(G) \rangle$.
# -------------------------------------------------------------------------------------------------
G := GL(IsPermGroup, 3, 3);
C := ConjugacyClassesSubgroups(G);;
C := List(C, Representative);;
C := Filtered(C, A -> Size(A) = 13 * 3);
Length(C); # should be 1

A := C[1];
NGA := Normalizer(G, A);
NGA = ClosureGroup(A, Center(G)); # should be true

# -------------------------------------------------------------------------------------------------
# We have $[Q : \langle A, C_Q(Z_2(A)) \rangle] = 3$ for $A \in \{A_3, A_4\}$.
# -------------------------------------------------------------------------------------------------
S := PcGroupCode(309006671086643171365690013478419223422146419245621383014393275579900089503571985049825827274917877880413672117829626994604814968815355115731625550330860924855700989042210232916254354107938195029060626374894949041217664136296342589730787701682021618677117195758162844063606096434038369504373899240344126522246355899558729671013315570791817251132593244445345256634484919025000728822888627478848123717501587299377424814778726064133279372383948353751027594400191396612743909292104407825863383758706429271968629216195707374558638997536,
    3^16
);

W := First(CharacteristicSubgroups(S), A -> Rank(A) = 10 and Size(A) = 3^11 and Exponent(A) = 3 and NilpotencyClassOfGroup(A) = 2);
W0 := StepCentralizer(S, S, W);

q := NaturalHomomorphismByNormalSubgroup(S, W);;
C := SubgroupsSolvableGroup(Image(q));;
Q := First(C, A -> IsElementaryAbelian(A) and Size(A) = 3^4);
Q := PreImage(q, Q);

I := IntermediateSubgroups(W0, W);;
I := I.subgroups;;

K := PositionsProperty(I, A -> NilpotencyClassOfGroup(A) <> 3);
LK := List(I{K}, A -> LowerCentralSeries(A)[3]);
CLK := List([1..Length(K)], i -> ClosureGroup(I[K[i]], Centralizer(Q, LK[i])));
ForAll(CLK, A -> Index(Q, A) = 3); # should be true

# -------------------------------------------------------------------------------------------------
# $C_A(Z_2(A))$ is elementary abelian of order $3^7$ for $A \in \{A_3, A_4\}$.
# -------------------------------------------------------------------------------------------------

J := PositionsProperty(I, A -> NilpotencyClassOfGroup(A) = 3);
LJ := List(I{J}, A -> LowerCentralSeries(A)[2]);
CLJ := List([1..Length(J)], i -> Centralizer(I[J[i]], LJ[i]));
ForAll(CLJ, A -> IsElementaryAbelian(A) and Size(A) = 3^7); # should be true
