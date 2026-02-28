pResidue := function(G,p)
    return NormalClosure(G, Sylow(G,p));
end function;

Im := function(phi, A)
    D := Codomain(phi);
    return sub<D | [phi(x) : x in Generators(A)]>;
end function;

G := Sp(6,3);
V := GModule(G);

M := MaximalSubgroups(G);
M := [A`subgroup : A in M | #pCore(A`subgroup, 2) eq 2^9][1];

U := Subgroups(M : OrderMultipleOf := 3^2);
U := [A`subgroup : A in U];
U := [A : A in U | <3,2> in FactoredOrder(A) and IsElementaryAbelian(Sylow(A,3)) and pResidue(A,3) eq A and IsIrreducible(Restriction(V, A)) and #pCore(A,2) eq 2^9][1]; // only the case in $^2 E_6(2)$ needed

C := Subgroups(U : OrderEqual := 3);
C := [A`subgroup : A in C];
N := [Normalizer(U,A) : A in C];

i := [i : i in [1..#C] | #pResidue(N[i]/C[i], 3) eq 12][1]; // $Q$ unique subgroup to pick up $\Alt(4)$ not $\SL_2(3)$

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// $O_3(C_{\Out(W)}(\Out_Q(W)))$ has order $3^6$, while the other three maximal subgroups do not  satisfy this property.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
3^6 in [#pCore(Centralizer(G, C[j]), 3) : j in [1..#C] | j ne i]; // false
3^6 eq #pCore(Centralizer(G, C[i]), 3); // true

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// $\Aut_{O^{3'}(N_F(W))}(Q))$ determines $O^{3'}(Aut_F(W))$ [$^2 E_6(2)$ case]
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
OutQW := C[i];
OutW := Normalizer(GL(6,3), G); // pick up the diagonal outer automorphism
OutGW := U;

Normalizer(OutW, Normalizer(OutGW, OutQW)) subset Normalizer(OutW, OutGW);

$H^1(\Out_\calH(\bfW); Z(\bfW)) \to H^1(\Out_{N_\calH(Q)}(\bfW); Z(\bfW))$

// -------------------------------------------------------------------------------------------------------------------------------------------------------------------
// The $1$-cocycle map $H^1(\Out_\calH(\bfW); Z(\bfW)) \to H^1(\Out_{N_\calH(Q)}(\bfW); Z(\bfW))$ is surjective, for both $\Fi_{22}$ and $^2 E_6(2)$.
// -------------------------------------------------------------------------------------------------------------------------------------------------------------------

// 2E6(3)
OutFW3 := PermutationGroup<24 |
(2,6,14,10,3,8,5,15,13,4,9,18)(7,11,17,21)(12,20,23)(16,22,24), (1,9,4,12,2,6,19,3,10,22,5,15)(7,8,24,13,21,23,17,18,20,14,11,16)
>;

// Fi22
OutFW2 := sub<OutFW3 | (1,20,22)(2,15,3,18,7,21,5,6,9,8,17,11)(4,13,10,14)(12,19,24), 
(1,21,7)(2,24,10)(3,16,15)(4,5,20)(6,9,23)(8,14,12)(11,17,19)(13,22,18) >;

// Q
Q := sub<OutFW3 | (2, 13, 3)(4, 8, 6)(5, 14, 9)(10, 18, 15)(12, 23, 20)(16, 24, 22)>;

OutFW := [OutFW2, OutFW3];
OutWQ := [Normalizer(A,Q) : A in OutFW];

T := [IrreducibleModules(A, GF(3)) : A in OutFW];
V := [[A : A in R | Dimension(A) eq 1 and Dimension(Fix(A)) eq 0][1] : R in T]; // checking every non-trivial 1-dimensional module

CV := [CohomologyModule(OutFW[i], V[i]) : i in [1..#V]];
CQ := [Restriction(CV[i], OutWQ[i]) : i in [1..#V]];

CHQ1 := [CohomologyGroup(CQ[i], 1) : i in [1..#V]];
CH1 := [CohomologyGroup(CV[i], 1) : i in [1..#V]];

res := [hom<CH1[i] -> CHQ1[i] | x :-> IdentifyOneCocycle(CQ[i],OneCocycle(CV[i],x))> : i in [1..#V]];

[Im(res[i], CH1[i]) eq CHQ1[i] : i in [1..#V]]; // all true, i.e. the H^1 maps are surjective
