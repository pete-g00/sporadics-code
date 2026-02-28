# Aut_F(P) is determined by Aut_F(S)

PcSubAutPGroup := function(AutPC, A)
    local Exp, A_m;
    Exp := List(GeneratorsOfGroup(A), x -> ExponentsAutPGroup(AutPC!.autrec, x));
    if fail in Exp then
        return fail;
    fi;
    A_m := List(Exp, a -> MappedVector(a, GeneratorsOfGroup(AutPC)));
    return Subgroup(AutPC, A_m);
end;

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

G := SimpleGroup("Fi23");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

M := MaximalSubgroups(S);;

W := First(CharacteristicSubgroups(S), A -> Rank(A) = 8 and Exponent(A) = 3 and NilpotencyClassOfGroup(A) = 2 and Size(A) = 3^9);
P := First(M, A -> Intersection(A,W) = W and not IsElementaryAbelian(A/W)); # P is the unique subgroup of index 3 containing W such that P/W is not elementary abelian
P := PreImage(f, P);

NGP := Normalizer(G,P);
f := IsomorphismPcGroup(NGP);;
NGP := Image(f);
P := Image(f, P);

AutP := AutomorphismGroupPGroup(P);;
AutP := PcGroupAutPGroup(AutP);;

AutGP := Automizer(NGP, P);
AutGP := PcSubAutPGroup(AutP, AutGP);
AutSP := SylowSubgroup(AutGP, 3);

N1 := Normalizer(AutGP, AutSP);
N2 := Normalizer(AutP, N1);

N1 = N2; # true
