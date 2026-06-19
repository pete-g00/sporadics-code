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

S := PcGroupCode(
7400854399531987446661804453421360490349586117992651245872868460231401376680736519225293135797778174312986244249140469495131619148911790486240691634368283183363459201197548444841386287609406050095667170138232997496759750025091095754478592088725011219395494042584869616373050212781276941623492777886495037101282551809840885294913559812197684592449554740203684762056077454134588125801924307765110856542260920439296594738090396526353356679374396021770933626914090167695998532129485869462615899329078630900066652747735551711611277752039271892984897878981067767040659970559858049201415523050855838793218317638306364589794660712124807305500273784592807615751024569607973468835240383976185564139138922792736043753752692776597923193421333935059980382015947188758263260677239821861985315988319113518268595620527124478485008453600985149181817070297522385026924174895523218485593433339988300756135588041861923304395761777157095073554546121152635507603926009810242444397878094859475805559542346463778336990873746048459387276510751009354076246330345502708105357704103078497710197622543393336458949460170899106828632578525891737870898553885373608606464571815825056239925631680640807003001559732107189648125177292370706155994957789291303406592, 3^20);

M := MaximalSubgroups(S);;
M := Filtered(M, A -> Exponent(A) = 9);;

P := First(M, A -> Center(A) = Center(S));
R := First(M, A -> Center(A) <> Center(S));

W := First(CharacteristicSubgroups(S), A -> Exponent(A) = 3 and Size(A) = 3^13 and Rank(A) = 12);

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(P))$ normalizes both $\bfV_i$
# -------------------------------------------------------------------------------------------------
W0 := StepCentralizer(P, P, W);
I := IntermediateSubgroups(W0, W);;
I := I.subgroups;;

I := Filtered(I, A -> NilpotencyClassOfGroup(A) = 3);;
Z2I := List(I, A -> UpperCentralSeries(A)[2]);
V := List(Z2I, A -> Centralizer(P, A));;

ForAll(V, A -> IsElementaryAbelian(A) and Size(A) = 3^8); # should be true
V[1] = V[2]; # should be false

# -------------------------------------------------------------------------------------------------
# $O^{3'}(\Out_F(R))$ normalizes both $\bfV_i$
# -------------------------------------------------------------------------------------------------
US := UpperCentralSeries(S);;
UR := UpperCentralSeries(R);;

UR[5] = US[6]; # Z_3(R) = Z_4(S)
UR[4] = US[5]; # Z_4(R) = Z_5(S)

I := IntermediateSubgroups(UR[4], UR[5]);;
I := I.subgroups;;
CI := List(I, A -> Centralizer(R,A));;
ForAll(CI, A -> Size(A) = 3^9); # should be true

J := PositionsProperty(CI, A -> ForAny(MaximalSubgroups(A), IsElementaryAbelian)); # should have 2 Values
Size(Intersection(CI{J})); # should be 3^7, i.e. the two eab subgroups of order 3^8 are distinct
