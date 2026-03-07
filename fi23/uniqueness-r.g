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

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);

t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;

G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

# -------------------------------------------------------------------------------------------------
# $|\Aut(S)|_{3'} = 2^3$
# -------------------------------------------------------------------------------------------------
Index(G, PCore(G,3)); # index 8

# -------------------------------------------------------------------------------------------------
# All choices of $\Out_F(R)$ are $\Aut(S)$-conjugate
# -------------------------------------------------------------------------------------------------

U := UpperCentralSeries(S);
Z2S := U[8];
R := Centralizer(S, Z2S);

AutR := AutomorphismGroupPGroup(R);;
AutGR := Automizer(G, R);
AutSR := Automizer(S,R);
InnR := Automizer(R,R);

AutR := PcGroupAutPGroup(AutR);
AutGR := PcSubAutPGroup(AutR, AutGR);
AutSR := PcSubAutPGroup(AutR, AutSR);
InnR := PcSubAutPGroup(AutR, InnR);
AutFR := ClosureGroup(AutSR, SylowSubgroup(AutGR,2));

q := NaturalHomomorphismByNormalSubgroup(AutR, InnR);;

OutR := Image(q);
OutGR := Image(q, AutGR);
OutSR := Image(q, AutSR);
OutFR := Image(q, AutFR);

I := IntermediateSubgroups(OutR, OutFR);;
I := Filtered(I.subgroups, A -> Size(PCore(A,3)) = 1);;
Length(I); # should be 3

ForAll(I, A -> IsConjugate(OutGR, I[1], A)); # should be true

