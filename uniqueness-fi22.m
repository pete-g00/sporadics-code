pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

Im := function(phi, A)
    D := Codomain(phi);
    return sub<D | [phi(x) : x in Generators(A)]>;
end function;

// (1) N_F(Q) determines Aut_F(W)
G := Sp(6,3);
M := MaximalSubgroups(G);
M := [A`subgroup : A in M];
M := [A : A in M | #A eq 2^10 * 3^4][1];
C := Subgroups(M : OrderMultipleOf := 3^2);
C := [A`subgroup : A in C];

V := GModule(G);
C := [A : A in C | <3,2> in FactoredOrder(A)];
C := [A : A in C | #pCore(A,3) eq 1];

C := [A : A in C | Dimension(Fix(Restriction(V, Sylow(A,3)))) eq 1];

C := [A : A in C | pResidue(A,3) ne A];
[#A : A in C];

Q := [Subgroups(A : OrderEqual := 3) : A in C];
Q := [[X`subgroup : X in A] : A in Q];
// Out_F(Q) contains an $\Alt(4)$, not $\SL_2(3)$
Q := [[A : A in Q[i] | #pResidue(Normalizer(C[i],A)/A,3) eq 12][1] : i in [1..#C]];

// $Sp_6(3) : 2$
G := Normalizer(GL(6,3), G);

NFQ := [Normalizer(C[i],Q[i]) : i in [1..#C]];
NAut := [Normalizer(G,A) : A in NFQ]; // it will pick up a 2

// (2) cohomology part => N_F(Q) and Aut_F(W) determine N_F(W)

// 2E6(3)
OutFW3 := PermutationGroup<24 |
(2,6,14,10,3,8,5,15,13,4,9,18)(7,11,17,21)(12,20,23)(16,22,24), (1,9,4,12,2,6,19,3,10,22,5,15)(7,8,24,13,21,23,17,18,20,14,11,16)
>;

// Fi22
OutFW2 := sub<OutFW3 | (1,20,22)(2,15,3,18,7,21,5,6,9,8,17,11)(4,13,10,14)(12,19,24), 
(1,21,7)(2,24,10)(3,16,15)(4,5,20)(6,9,23)(8,14,12)(11,17,19)(13,22,18) >;

// \Omega_7(3)
OutFW1 := sub<OutFW3 | (2,6,14,10,3,8,5,15,13,4,9,18)(7,11,17,21)(12,20,23)(16,22,24), (1,18,17,12,21,13,19,8,7,22,11,14)(2,16,4,9,24,15,5,23,10,3,20,6) >;

// Q
Q := sub<OutFW3 | (2, 13, 3)(4, 8, 6)(5, 14, 9)(10, 18, 15)(12, 23, 20)(16, 24, 22)>;

OutFW := [OutFW1, OutFW2, OutFW3];
OutWQ := [Normalizer(A,Q) : A in OutFW];

T := [IrreducibleModules(A, GF(3)) : A in OutFW];
V := [[A : A in R | Dimension(A) eq 1 and Dimension(Fix(A)) eq 0][1] : R in T];

CV := [CohomologyModule(OutFW[i], V[i]) : i in [1..#V]];
CQ := [Restriction(CV[i], OutWQ[i]) : i in [1..#V]];

CHQ1 := [CohomologyGroup(CQ[i], 1) : i in [1..#V]];
CH1 := [CohomologyGroup(CV[i], 1) : i in [1..#V]];

res := [hom<CH1[i] -> CHQ1[i] | x :-> IdentifyOneCocycle(CQ[i],OneCocycle(CV[i],x))> : i in [1..#V]];

[Im(res[i], CH1[i]) eq CHQ1[i] : i in [1..#V]]; // all true, i.e. the H^1 maps are surjective
