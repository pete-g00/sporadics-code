Im := function(phi, A)
    D := Codomain(phi);
    return sub<D | [phi(x) : x in Generators(A)]>;
end function;

G0 := Sp(8,3);
G := Normalizer(GL(8,3), G0);

M  := MaximalSubgroups(G0 : OrderEqual := 3317760);
M := [A`subgroup : A in M][1];

OutFW := Subgroups(M : OrderMultipleOf := 3^4);
OutFW := [A`subgroup : A in OutFW];
OutFW := [A : A in OutFW | #pCore(A,3) eq 1 and pResidue(A,3) eq A];
#OutFW; // should be 4
OutFW := [Normalizer(G,A) : A in OutFW];

OutSW := [Sylow(A,3) : A in OutFW];
N1 := [Normalizer(OutFW[i], OutSW[i]) : i in [1..#OutFW]];
N2 := [Normalizer(G, N1[i]) : i in [1..#OutFW]];

N1 eq N2; // true

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// $N_F(Q)$ determines $N_F(W)$
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
OutF0W := [A meet G0 : A in OutFW];
OutQW := [ElementaryAbelianSubgroups(A : OrderEqual := 3^3) : A in OutSW];
OutQW := [A[1]`subgroup : A in OutQW];
NOutQW := [Normalizer(OutFW[i], OutQW[i]) : i in [1..#OutFW]];

F := [PermutationRepresentation(A) : A in OutFW];
OutFW := [Image(F[i]) : i in [1..#F]];
OutF0W := [F[i](OutF0W[i]) : i in [1..#F]];
NOutQW := [F[i](NOutQW[i]) : i in [1..#F]];

T := [IrreducibleModules(A, GF(3)) : A in OutFW];
T := [[A : A in T[i] | Dimension(A) eq 1 and Dimension(Fix(A)) eq 0 and Dimension(Fix(Restriction(A, OutF0W[i]))) eq 1] : i in [1..#F]];

[#A : A in T]; // [1,1,1,1]
T := [A[1] : A in T];

CV := [CohomologyModule(OutFW[i], T[i]) : i in [1..#T]];
CQ := [Restriction(CV[i], NOutQW[i]) : i in [1..#T]];

CHQ1 := [CohomologyGroup(CQ[i], 1) : i in [1..#T]];
CH1 := [CohomologyGroup(CV[i], 1) : i in [1..#T]];

res := [hom<CH1[i] -> CHQ1[i] | x :-> IdentifyOneCocycle(CQ[i],OneCocycle(CV[i],x))> : i in [1..#T]];

[Im(res[i], CH1[i]) eq CHQ1[i] : i in [1..#T]]; // all true, i.e. the H^1 maps are surjective
