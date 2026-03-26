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
    SetAutomorphismDomain(AutGH, H);

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

# -------------------------------------------------------------------------------------------------
# $\Aut_F(S)$ determines $\Aut_F(R)$
# -------------------------------------------------------------------------------------------------

S := PcGroupCode(
13741491938431806455657762112574406588684703498867453558824558564013195548929578751329924342130079075234146575466397002123106897939463680, 3^10);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);

t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;

G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);
G2 := SylowSubgroup(G,2);

AutFS := ClosureGroup(S, G2);

U := UpperCentralSeries(S);
R := Centralizer(S, U[5]);

AutNR := Automizer(AutFS, R);

AutR := AutomorphismGroupPGroup(R);;
AutR := PcGroupAutPGroup(AutR);
InnR := InnerAutGroupPGroup(AutR);
AutNR := PcSubAutPGroup(AutR, AutNR);

q := NaturalHomomorphismByNormalSubgroup(AutR, InnR);;

OutR := Image(q);
OutNR := Image(q, AutNR);

OutFR := ComplementClassesRepresentatives(OutR, PCore(OutR, 3));
Length(OutFR); # 1
OutFR := OutFR[1];
StructureDescription(OutFR); # C2 x GL(2,3)

OutSR := SylowSubgroup(OutFR, 3);
N1 := Normalizer(OutFR, OutSR);

a := RepresentativeAction(OutR, N1, OutNR);

OutFR := OutFR^a;
N1 := N1^a;
Intersection(OutFR, N1) = N1;

N2 := Normalizer(OutR, N1);

Index(N2, N1); # 1
