Automizer := function(G, H)
    local NGH, L, AutGH;
    NGH := Normalizer(G, H);
    if IsTrivial(NGH) then
        return Group(IdentityMapping(H));
    fi;
    L := List(SmallGeneratingSet(NGH), a -> ConjugatorAutomorphismNC(H, a));
    if IsEmpty(L) then
        return Group(IdentityMapping(H));
    fi;
    AutGH := Group(L);
    SetIsGroupOfAutomorphisms(AutGH, true);
    return AutGH;
end;

PcSubAutPGroup := function(AutPC, A)
    local Exp, A_m;
    
    Exp := List(GeneratorsOfGroup(A), x -> ExponentsAutPGroup(AutPC!.autrec, x));
    
    if fail in Exp then 
        return fail;
    fi;
    
    A_m := List(Exp, a -> MappedVector(a, GeneratorsOfGroup(AutPC)));
    return Subgroup(AutPC, A_m);
end;

G := SimpleGroup("Fi23");
S := SylowSubgroup(G,3);

f := IsomorphismPcGroup(S);;
S := Image(f);

U := UpperCentralSeries(S);

Z5S := U[5];

M := MaximalSubgroups(S);;

Q := First(M, A -> Agemo(A,3) = Z5S);
P := First(M, A -> A <> Q and Center(A) = Center(S));

W := First(CharacteristicSubgroups(S), A -> Rank(A) = 8 and Size(A) = 3^9 and Exponent(A) = 3);
q := NaturalHomomorphismByNormalSubgroup(S, W);;

Ex := Filtered(SubgroupsSolvableGroup(Image(q)), A -> Size(A) = 3^2 and Normalizer(Image(q),A) = Image(q,Q));
Ex := List(Ex, A -> PreImage(q, A));
Ex := First(Ex, A -> NilpotencyClassOfGroup(A) = 4);

P := PreImage(f,P);
Q := PreImage(f,Q);
Ex := PreImage(f, Ex);
S := PreImage(f, S);

# -------------------------------------------------------------------------------------------------
# There is a unique class for $\Out_F(P)$, and $\Aut_F(S)$ determines $\Out_F(P)$
# -------------------------------------------------------------------------------------------------
NGP := Normalizer(G, P);
f := IsomorphismPcGroup(NGP);;

NGP := Image(f, NGP);
S := Image(f, S);
P := Image(f, P);

AutGP := Automizer(NGP,P);
AutSP := Automizer(S,P);
InnP := Automizer(P,P);

AutP := AutomorphismGroupPGroup(P);;
AutP := PcGroupAutPGroup(AutP);

AutGP := PcSubAutPGroup(AutP, AutGP);
AutSP := PcSubAutPGroup(AutP, AutSP);
InnP := PcSubAutPGroup(AutP, InnP);

q := NaturalHomomorphismByNormalSubgroup(AutP, InnP);

OutP := Image(q);
OutGP := Image(q, AutGP);
OutSP := Image(q, AutSP);

CoP := ComplementClassesRepresentatives(OutP, PCore(OutP,3));;
Length(CoP); # should be 1
StructureDescription(CoP[1]); # should be $2 \times \GL_2(3)$

N1 := Normalizer(OutGP, OutSP);
N2 := Normalizer(OutP, N1);
N := Normalizer(OutP, OutSP);

IsSubset(N, N2); # $N2 \leq N$

# -------------------------------------------------------------------------------------------------
# There is a unique class for $\Out_F(X)$, and $\Aut_F(S)$ determines $\Out_F(X)$
# -------------------------------------------------------------------------------------------------
NGX := Normalizer(G, Ex);
f := IsomorphismPcGroup(NGX);;
Q := Image(f,Q);

NGX := Image(f, NGX);
Ex := Image(f, Ex);

AutGX := Automizer(NGX,Ex);
AutSX := Automizer(Q,Ex);
InnX := Automizer(Ex,Ex);

AutX := AutomorphismGroupPGroup(Ex);;
AutX := PcGroupAutPGroup(AutX);

AutGX := PcSubAutPGroup(AutX, AutGX);
AutSX := PcSubAutPGroup(AutX, AutSX);
InnX := PcSubAutPGroup(AutX, InnX);

q := NaturalHomomorphismByNormalSubgroup(AutX, InnX);

OutX := Image(q);
OutGX := Image(q, AutGX);
OutSX := Image(q, AutSX);

CoX := ComplementClassesRepresentatives(OutX, PCore(OutX,3));;
Length(CoX); # should be 1
StructureDescription(CoX[1]); # should be $\Dih(8) \times \GL_2(3)$

N1 := Normalizer(OutGX, OutSX);
N2 := Normalizer(OutX, N1);
N := Normalizer(OutX, OutSX);

IsSubset(N, N2); # $N2 \leq N$
