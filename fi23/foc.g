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
# $[S, Q \cap R] \nleq \Phi(R)$
# -------------------------------------------------------------------------------------------------

G := SimpleGroup("Fi23");
S := SylowSubgroup(G, 3);
f := IsomorphismPcGroup(S);;
S := Image(f);

AutS := AutomorphismGroupPGroup(S);;
AutS_PC := PcGroupAutPGroup(AutS);
AutS := ConvertHybridAutGroup(AutS);

t := GroupHomomorphismByImagesNC(AutS_PC, AutS);;
G := SplitExtension(AutS_PC, t, S);
S := ModuleOfExtension(G);

U := UpperCentralSeries(S);;
R := Centralizer(S, U[8]);

W := First(CharacteristicSubgroups(S), A -> Exponent(A) = 3 and Rank(A) = 8);

q := NaturalHomomorphismByNormalSubgroup(S, W);;

Q := First(MaximalSubgroups(Image(q)), IsElementaryAbelian);
Q := PreImage(q, Q);

C := CommutatorSubgroup(S, Intersection(Q,R));

IsSubset(FrattiniSubgroup(R), C); # false

# -------------------------------------------------------------------------------------------------
# If $B \in \Syl_2(\Aut(S))$, then $C := C_B(S/Q)$ has order $2^2$ and satisfies $[S, C] = Q$.
# -------------------------------------------------------------------------------------------------
B := SylowSubgroup(G, 2);
B := ClosureGroup(S, B);

C := StepCentralizer(B, S, Q);
PValuation(Size(C),2); # 2
CommutatorSubgroup(S, C) = Q; # true
