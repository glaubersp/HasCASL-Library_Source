%---------------------------------------------------------------------------
% Problem : hets_exported
% Name    : Prelude/Numbers_Int_inconsistent
% Author  : hets
% Status  : unknown
% Desc    : 
% Date    : Tue Jul 22 13:24:27 BRT 2008
% Option  : SPASS , [SPFlag "set_flag" ["TimeLimit","500"],SPFlag "set_flag" ["DocProof","1"]]
%---------------------------------------------------------------------------
fof(declaration0,axiom,
    ! [X1] : (int(X1) => nat(abs(X1)))).
fof(declaration1,axiom,
    nat(eight)).
fof(declaration2,axiom,
    int(eight_0)).
fof(declaration3,axiom,
    nat(five)).
fof(declaration4,axiom,
    int(five_0)).
fof(declaration5,axiom,
    nat(four)).
fof(declaration6,axiom,
    int(four_0)).
fof(declaration7,axiom,
    int(gn_bottom_Int)).
fof(declaration8,axiom,
    nat(gn_bottom_Nat)).
fof(declaration9,axiom,
    ! [X1] : (int(X1) => nat(intToNat__(X1)))).
fof(declaration10,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(max(X1, X2)))).
fof(declaration11,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(max_2(X1, X2)))).
fof(declaration12,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(min(X1, X2)))).
fof(declaration13,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(min_2(X1, X2)))).
fof(declaration14,axiom,
    ! [X1] : (int(X1) => int(minus__(X1)))).
fof(declaration15,axiom,
    ! [X1] : (nat(X1) => int(natToInt__(X1)))).
fof(declaration16,axiom,
    nat(nine)).
fof(declaration17,axiom,
    int(nine_0)).
fof(declaration18,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__AtAt__(X1, X2)))).
fof(declaration19,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__Caret__(X1, X2)))).
fof(declaration20,axiom,
    ! [X1, X2] : ((int(X1) & nat(X2)) => int(o__Caret___2(X1, X2)))).
fof(declaration21,axiom,
    ! [X1] : (nat(X1) => nat(o__Exclam(X1)))).
fof(declaration22,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__MinusExclam__(X1, X2)))).
fof(declaration23,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__MinusQuest__(X1, X2)))).
fof(declaration24,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => int(o__Minus__(X1, X2)))).
fof(declaration25,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__Minus___2(X1, X2)))).
fof(declaration26,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__Plus__(X1, X2)))).
fof(declaration27,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__Plus___2(X1, X2)))).
fof(declaration28,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__SlashQuest__(X1, X2)))).
fof(declaration29,axiom,
    ! [X1, X2] : ((int(X1) & int(X2))
                  => int(o__SlashQuest___2(X1, X2)))).
fof(declaration30,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__div__(X1, X2)))).
fof(declaration31,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__div___2(X1, X2)))).
fof(declaration32,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__mod__(X1, X2)))).
fof(declaration33,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => nat(o__mod___2(X1, X2)))).
fof(declaration34,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__quot__(X1, X2)))).
fof(declaration35,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__rem__(X1, X2)))).
fof(declaration36,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__x__(X1, X2)))).
fof(declaration37,axiom,
    ! [X1, X2] : ((int(X1) & int(X2)) => int(o__x___2(X1, X2)))).
fof(declaration38,axiom,
    nat(one)).
fof(declaration39,axiom,
    int(one_0)).
fof(declaration40,axiom,
    ! [X1] : (nat(X1) => nat(pre(X1)))).
fof(declaration41,axiom,
    nat(seven)).
fof(declaration42,axiom,
    int(seven_0)).
fof(declaration43,axiom,
    ! [X1] : (int(X1) => int(sign(X1)))).
fof(declaration44,axiom,
    nat(six)).
fof(declaration45,axiom,
    int(six_0)).
fof(declaration46,axiom,
    ! [X1] : (nat(X1) => nat(suc(X1)))).
fof(declaration47,axiom,
    nat(three)).
fof(declaration48,axiom,
    int(three_0)).
fof(declaration49,axiom,
    nat(two)).
fof(declaration50,axiom,
    int(two_0)).
fof(declaration51,axiom,
    nat(zero)).
fof(declaration52,axiom,
    int(zero_0)).
fof(disjoint_sorts_int_nat,axiom,
    ! [Y1, Y2] : ((int(Y1) & nat(Y2)) => ~ Y1 = Y2)).
fof(ga_non_empty_sort_int,axiom,
    ? [Y] : int(Y)).
fof(ga_non_empty_sort_nat,axiom,
    ? [Y] : nat(Y)).
fof(ga_nonEmpty,axiom,
    ? [X] : (int(X) & gn_defined_1(X))).
fof(ga_notDefBottom,axiom,
    ! [X] : (int(X) => (~ gn_defined_1(X) <=> X = gn_bottom_Int))).
fof(ga_nonEmpty_1,axiom,
    ? [X] : (nat(X) & gn_defined(X))).
fof(ga_notDefBottom_1,axiom,
    ! [X] : (nat(X) => (~ gn_defined(X) <=> X = gn_bottom_Nat))).
fof(ga_totality,axiom,
    ! [X_1] : (int(X_1)
               => (gn_defined_1(minus__(X_1)) <=> gn_defined_1(X_1)))).
fof(ga_totality_1,axiom,
    gn_defined_1(zero_0)).
fof(ga_totality_2,axiom,
    gn_defined(zero)).
fof(ga_totality_3,axiom,
    gn_defined_1(one_0)).
fof(ga_totality_4,axiom,
    gn_defined(one)).
fof(ga_totality_5,axiom,
    gn_defined_1(two_0)).
fof(ga_totality_6,axiom,
    gn_defined(two)).
fof(ga_totality_7,axiom,
    gn_defined_1(three_0)).
fof(ga_totality_8,axiom,
    gn_defined(three)).
fof(ga_totality_9,axiom,
    gn_defined_1(four_0)).
fof(ga_totality_10,axiom,
    gn_defined(four)).
fof(ga_totality_11,axiom,
    gn_defined_1(five_0)).
fof(ga_totality_12,axiom,
    gn_defined(five)).
fof(ga_totality_13,axiom,
    gn_defined_1(six_0)).
fof(ga_totality_14,axiom,
    gn_defined(six)).
fof(ga_totality_15,axiom,
    gn_defined_1(seven_0)).
fof(ga_totality_16,axiom,
    gn_defined(seven)).
fof(ga_totality_17,axiom,
    gn_defined_1(eight_0)).
fof(ga_totality_18,axiom,
    gn_defined(eight)).
fof(ga_totality_19,axiom,
    gn_defined_1(nine_0)).
fof(ga_totality_20,axiom,
    gn_defined(nine)).
fof(ga_totality_21,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined_1(natToInt__(X_1)) <=> gn_defined(X_1)))).
fof(ga_totality_22,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined(o__Exclam(X_1)) <=> gn_defined(X_1)))).
fof(ga_totality_23,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__x___2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_totality_24,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__x__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_25,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__Plus___2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_totality_26,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__Plus__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_27,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__Minus___2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_totality_28,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined_1(o__Minus__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_29,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__MinusExclam__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_30,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__AtAt__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_31,axiom,
    ! [X_1, X_2] : ((int(X_1) & nat(X_2))
                    => (gn_defined_1(o__Caret___2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined(X_2))))).
fof(ga_totality_32,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__Caret__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_33,axiom,
    ! [X_1] : (int(X_1)
               => (gn_defined(abs(X_1)) <=> gn_defined_1(X_1)))).
fof(ga_totality_34,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(max_2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_totality_35,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(max(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_36,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(min_2(X_1, X_2))
                        <=> (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_totality_37,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(min(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_38,axiom,
    ! [X_1] : (int(X_1)
               => (gn_defined_1(sign(X_1)) <=> gn_defined_1(X_1)))).
fof(ga_totality_39,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined(suc(X_1)) <=> gn_defined(X_1)))).
fof(ga_strictness,axiom,
    ! [X_1] : (int(X_1)
               => (gn_defined(intToNat__(X_1)) => gn_defined_1(X_1)))).
fof(ga_strictness_1,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__MinusQuest__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_2,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__SlashQuest___2(X_1, X_2))
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_strictness_3,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__SlashQuest__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_4,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__div___2(X_1, X_2))
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_strictness_5,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__div__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_6,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined(o__mod___2(X_1, X_2))
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_strictness_7,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__mod__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_8,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__quot__(X_1, X_2))
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_strictness_9,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (gn_defined_1(o__rem__(X_1, X_2))
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_strictness_10,axiom,
    ! [X_1] : (nat(X_1) => (gn_defined(pre(X_1)) => gn_defined(X_1)))).
fof(ga_predicate_strictness,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (p__Lt___2(X_1, X_2)
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_predicate_strictness_1,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__Lt__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_2,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (p__LtEq___2(X_1, X_2)
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_predicate_strictness_3,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__LtEq__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_4,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (p__Gt___2(X_1, X_2)
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_predicate_strictness_5,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__Gt__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_6,axiom,
    ! [X_1, X_2] : ((int(X_1) & int(X_2))
                    => (p__GtEq___2(X_1, X_2)
                        => (gn_defined_1(X_1) & gn_defined_1(X_2))))).
fof(ga_predicate_strictness_7,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__GtEq__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_8,axiom,
    ! [X_1] : (int(X_1) => (even_1(X_1) => gn_defined_1(X_1)))).
fof(ga_predicate_strictness_9,axiom,
    ! [X_1] : (nat(X_1) => (even(X_1) => gn_defined(X_1)))).
fof(ga_predicate_strictness_10,axiom,
    ! [X_1] : (int(X_1) => (odd_1(X_1) => gn_defined_1(X_1)))).
fof(ga_predicate_strictness_11,axiom,
    ! [X_1] : (nat(X_1) => (odd(X_1) => gn_defined(X_1)))).
fof(ga_selector_pre,axiom,
    ! [X1] : (nat(X1) => (gn_defined(X1) => pre(suc(X1)) = X1))).
fof(ga_injective_suc,axiom,
    ! [X1, Y1] : ((nat(X1) & nat(Y1))
                  => ((gn_defined(X1) & gn_defined(Y1))
                      => (suc(X1) = suc(Y1) <=> X1 = Y1)))).
fof(ga_disjoint_0_suc,axiom,
    ! [Y1] : (nat(Y1) => (gn_defined(Y1) => ~ zero = suc(Y1)))).
fof(ga_selector_undef_pre_0,axiom,
    ~ gn_defined(pre(zero))).
fof(one_def_Nat,axiom,
    one = suc(zero)).
fof(two_def_Nat,axiom,
    two = suc(one)).
fof(three_def_Nat,axiom,
    three = suc(two)).
fof(four_def_Nat,axiom,
    four = suc(three)).
fof(five_def_Nat,axiom,
    five = suc(four)).
fof(six_def_Nat,axiom,
    six = suc(five)).
fof(seven_def_Nat,axiom,
    seven = suc(six)).
fof(eight_def_Nat,axiom,
    eight = suc(seven)).
fof(nine_def_Nat,axiom,
    nine = suc(eight)).
fof(decimal_def,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => o__AtAt__(M, N) = o__Plus__(o__x__(M, suc(nine)), N)))).
fof(ga_comm___Plus__,axiom,
    ! [X, Y] : ((nat(X) & nat(Y))
                => ((gn_defined(X) & gn_defined(Y))
                    => o__Plus__(X, Y) = o__Plus__(Y, X)))).
fof(ga_assoc___Plus__,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => o__Plus__(o__Plus__(X, Y), Z)
                          = o__Plus__(X, o__Plus__(Y, Z))))).
fof(ga_right_unit___Plus__,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => o__Plus__(X, zero) = X))).
fof(ga_left_unit___Plus__,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => o__Plus__(zero, X) = X))).
fof(ga_left_comm___Plus__,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => o__Plus__(X, o__Plus__(Y, Z))
                          = o__Plus__(Y, o__Plus__(X, Z))))).
fof(ga_comm___x__,axiom,
    ! [X, Y] : ((nat(X) & nat(Y))
                => ((gn_defined(X) & gn_defined(Y))
                    => o__x__(X, Y) = o__x__(Y, X)))).
fof(ga_assoc___x__,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => o__x__(o__x__(X, Y), Z) = o__x__(X, o__x__(Y, Z))))).
fof(ga_right_unit___x__,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => o__x__(X, one) = X))).
fof(ga_left_unit___x__,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => o__x__(one, X) = X))).
fof(ga_left_comm___x__,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => o__x__(X, o__x__(Y, Z)) = o__x__(Y, o__x__(X, Z))))).
fof(ga_comm_min,axiom,
    ! [X, Y] : ((nat(X) & nat(Y))
                => ((gn_defined(X) & gn_defined(Y)) => min(X, Y) = min(Y, X)))).
fof(ga_assoc_min,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => min(min(X, Y), Z) = min(X, min(Y, Z))))).
fof(ga_left_comm_min,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => min(X, min(Y, Z)) = min(Y, min(X, Z))))).
fof(ga_comm_max,axiom,
    ! [X, Y] : ((nat(X) & nat(Y))
                => ((gn_defined(X) & gn_defined(Y)) => max(X, Y) = max(Y, X)))).
fof(ga_assoc_max,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => max(max(X, Y), Z) = max(X, max(Y, Z))))).
fof(ga_right_unit_max,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => max(X, zero) = X))).
fof(ga_left_unit_max,axiom,
    ! [X] : (nat(X) => (gn_defined(X) => max(zero, X) = X))).
fof(ga_left_comm_max,axiom,
    ! [X, Y, Z] : ((nat(X) & nat(Y) & nat(Z))
                   => (((gn_defined(X) & gn_defined(Y)) & gn_defined(Z))
                       => max(X, max(Y, Z)) = max(Y, max(X, Z))))).
fof(leq_def1_Nat,axiom,
    ! [N] : (nat(N) => (gn_defined(N) => p__LtEq__(zero, N)))).
fof(leq_def2_Nat,axiom,
    ! [N] : (nat(N) => (gn_defined(N) => ~ p__LtEq__(suc(N), zero)))).
fof(leq_def3_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__LtEq__(suc(M), suc(N)) <=> p__LtEq__(M, N))))).
fof(geq_def_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__GtEq__(M, N) <=> p__LtEq__(N, M))))).
fof(less_def_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__Lt__(M, N) <=> (p__LtEq__(M, N) & ~ M = N))))).
fof(greater_def_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__Gt__(M, N) <=> p__Lt__(N, M))))).
fof(even_0_Nat,axiom,
    even(zero)).
fof(even_suc_Nat,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => (even(suc(M)) <=> odd(M))))).
fof(odd_def_Nat,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => (odd(M) <=> ~ even(M))))).
fof(factorial_0,axiom,
    o__Exclam(zero) = one).
fof(factorial_suc,axiom,
    ! [N] : (nat(N)
             => (gn_defined(N)
                 => o__Exclam(suc(N)) = o__x__(suc(N), o__Exclam(N))))).
fof(add_0_Nat,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => o__Plus__(zero, M) = M))).
fof(add_suc_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => o__Plus__(suc(N), M) = suc(o__Plus__(N, M))))).
fof(mult_0_Nat,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => o__x__(zero, M) = zero))).
fof(mult_suc_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => o__x__(suc(N), M) = o__Plus__(o__x__(N, M), M)))).
fof(power_0_Nat,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => o__Caret__(M, zero) = one))).
fof(power_suc_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => o__Caret__(M, suc(N)) = o__x__(M, o__Caret__(M, N))))).
fof(min_def_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => ((p__LtEq__(M, N) => min(M, N) = M)
                        & (~ p__LtEq__(M, N) => min(M, N) = N))))).
fof(max_def_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => ((p__LtEq__(M, N) => max(M, N) = N)
                        & (~ p__LtEq__(M, N) => max(M, N) = M))))).
fof(subTotal_def1_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__Gt__(M, N) => o__MinusExclam__(N, M) = zero)))).
fof(subTotal_def2_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (p__LtEq__(M, N)
                        => o__MinusExclam__(N, M) = o__MinusQuest__(N, M))))).
fof(sub_dom_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (gn_defined(o__MinusQuest__(M, N))
                        <=> p__GtEq__(M, N))))).
fof(sub_def_Nat,axiom,
    ! [M, N, R] : ((nat(M) & nat(N) & nat(R))
                   => (((gn_defined(M) & gn_defined(N)) & gn_defined(R))
                       => (o__MinusQuest__(M, N) = R
                           <=> M = o__Plus__(R, N))))).
fof(divide_dom_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (gn_defined(o__SlashQuest__(M, N))
                        <=> (~ N = zero & o__mod__(M, N) = zero))))).
fof(divide_0_Nat,axiom,
    ! [M] : (nat(M)
             => (gn_defined(M) => ~ gn_defined(o__SlashQuest__(M, zero))))).
fof(divide_Pos_Nat,axiom,
    ! [M, N, R] : ((nat(M) & nat(N) & nat(R))
                   => (((gn_defined(M) & gn_defined(N)) & gn_defined(R))
                       => (p__Gt__(N, zero)
                           => (o__SlashQuest__(M, N) = R
                               <=> M = o__x__(R, N)))))).
fof(div_dom_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (gn_defined(o__div__(M, N)) <=> ~ N = zero)))).
fof(div_Nat,axiom,
    ! [M, N, R] : ((nat(M) & nat(N) & nat(R))
                   => (((gn_defined(M) & gn_defined(N)) & gn_defined(R))
                       => (o__div__(M, N) = R
                           <=> ? [S] : (nat(S)
                                        & (gn_defined(S)
                                           & (M = o__Plus__(o__x__(N, R), S)
                                              & p__Lt__(S, N)))))))).
fof(mod_dom_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (gn_defined(o__mod__(M, N)) <=> ~ N = zero)))).
fof(mod_Nat,axiom,
    ! [M, N, S] : ((nat(M) & nat(N) & nat(S))
                   => (((gn_defined(M) & gn_defined(N)) & gn_defined(S))
                       => (o__mod__(M, N) = S
                           <=> ? [R] : (nat(R)
                                        & (gn_defined(R)
                                           & (M = o__Plus__(o__x__(N, R), S)
                                              & p__Lt__(S, N)))))))).
fof(distr1_Nat,axiom,
    ! [R, S, T] : ((nat(R) & nat(S) & nat(T))
                   => (((gn_defined(R) & gn_defined(S)) & gn_defined(T))
                       => o__x__(o__Plus__(R, S), T)
                          = o__Plus__(o__x__(R, T), o__x__(S, T))))).
fof(distr2_Nat,axiom,
    ! [R, S, T] : ((nat(R) & nat(S) & nat(T))
                   => (((gn_defined(R) & gn_defined(S)) & gn_defined(T))
                       => o__x__(T, o__Plus__(R, S))
                          = o__Plus__(o__x__(T, R), o__x__(T, S))))).
fof(min_0,axiom,
    ! [M] : (nat(M) => (gn_defined(M) => min(M, zero) = zero))).
fof(div_mod_Nat,axiom,
    ! [M, N] : ((nat(M) & nat(N))
                => ((gn_defined(M) & gn_defined(N))
                    => (~ N = zero
                        => M
                           = o__Plus__(o__x__(o__div__(M, N), N),
                                       o__mod__(M, N)))))).
fof(power_Nat,axiom,
    ! [M, R, S] : ((nat(M) & nat(R) & nat(S))
                   => (((gn_defined(M) & gn_defined(R)) & gn_defined(S))
                       => o__Caret__(M, o__Plus__(R, S))
                          = o__x__(o__Caret__(M, R), o__Caret__(M, S))))).
fof(equality_Int,axiom,
    ! [A, B, C, D] : ((nat(A) & nat(B) & nat(C) & nat(D))
                      => ((((gn_defined(A) & gn_defined(B)) & gn_defined(C))
                           & gn_defined(D))
                          => (o__Minus__(A, B) = o__Minus__(C, D)
                              <=> o__Plus__(A, D) = o__Plus__(C, B))))).
fof(natToInt,axiom,
    ! [A] : (nat(A)
             => (gn_defined(A) => natToInt__(A) = o__Minus__(A, zero)))).
fof(intToNat,axiom,
    ! [A, B] : ((nat(A) & nat(B))
                => ((gn_defined(A) & gn_defined(B))
                    => intToNat__(o__Minus__(A, B)) = o__MinusExclam__(A, B)))).
fof(ga_comm___Plus___1,axiom,
    ! [X, Y] : ((int(X) & int(Y))
                => ((gn_defined_1(X) & gn_defined_1(Y))
                    => o__Plus___2(X, Y) = o__Plus___2(Y, X)))).
fof(ga_assoc___Plus___1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => o__Plus___2(o__Plus___2(X, Y), Z)
                          = o__Plus___2(X, o__Plus___2(Y, Z))))).
fof(ga_right_unit___Plus___1,axiom,
    ! [X] : (int(X)
             => (gn_defined_1(X) => o__Plus___2(X, zero_0) = X))).
fof(ga_left_unit___Plus___1,axiom,
    ! [X] : (int(X)
             => (gn_defined_1(X) => o__Plus___2(zero_0, X) = X))).
fof(ga_left_comm___Plus___1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => o__Plus___2(X, o__Plus___2(Y, Z))
                          = o__Plus___2(Y, o__Plus___2(X, Z))))).
fof(ga_comm___x___1,axiom,
    ! [X, Y] : ((int(X) & int(Y))
                => ((gn_defined_1(X) & gn_defined_1(Y))
                    => o__x___2(X, Y) = o__x___2(Y, X)))).
fof(ga_assoc___x___1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => o__x___2(o__x___2(X, Y), Z)
                          = o__x___2(X, o__x___2(Y, Z))))).
fof(ga_right_unit___x___1,axiom,
    ! [X] : (int(X) => (gn_defined_1(X) => o__x___2(X, one_0) = X))).
fof(ga_left_unit___x___1,axiom,
    ! [X] : (int(X) => (gn_defined_1(X) => o__x___2(one_0, X) = X))).
fof(ga_left_comm___x___1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => o__x___2(X, o__x___2(Y, Z))
                          = o__x___2(Y, o__x___2(X, Z))))).
fof(ga_comm_min_1,axiom,
    ! [X, Y] : ((int(X) & int(Y))
                => ((gn_defined_1(X) & gn_defined_1(Y))
                    => min_2(X, Y) = min_2(Y, X)))).
fof(ga_comm_max_1,axiom,
    ! [X, Y] : ((int(X) & int(Y))
                => ((gn_defined_1(X) & gn_defined_1(Y))
                    => max_2(X, Y) = max_2(Y, X)))).
fof(ga_assoc_min_1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => min_2(min_2(X, Y), Z) = min_2(X, min_2(Y, Z))))).
fof(ga_assoc_max_1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => max_2(max_2(X, Y), Z) = max_2(X, max_2(Y, Z))))).
fof(ga_left_comm_min_1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => min_2(X, min_2(Y, Z)) = min_2(Y, min_2(X, Z))))).
fof(ga_left_comm_max_1,axiom,
    ! [X, Y, Z] : ((int(X) & int(Y) & int(Z))
                   => (((gn_defined_1(X) & gn_defined_1(Y)) & gn_defined_1(Z))
                       => max_2(X, max_2(Y, Z)) = max_2(Y, max_2(X, Z))))).
fof(geq_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (p__GtEq___2(M, N) <=> p__LtEq___2(N, M))))).
fof(less_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (p__Lt___2(M, N) <=> (p__LtEq___2(M, N) & ~ M = N))))).
fof(greater_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (p__Gt___2(M, N) <=> p__Lt___2(N, M))))).
fof(even_def_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M) => (even_1(M) <=> even(abs(M)))))).
fof(odd_def_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M) => (odd_1(M) <=> ~ even_1(M))))).
fof(odd_alt_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M) => (odd_1(M) <=> odd(abs(M)))))).
fof(neg_def_Int,axiom,
    ! [A, B] : ((nat(A) & nat(B))
                => ((gn_defined(A) & gn_defined(B))
                    => minus__(o__Minus__(A, B)) = o__Minus__(B, A)))).
fof(sign_def_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M)
                 => ((M = zero_0 => sign(M) = zero_0)
                     & (~ M = zero_0
                        => ((p__Gt___2(M, zero_0) => sign(M) = one_0)
                            & (~ p__Gt___2(M, zero_0)
                               => sign(M) = minus__(one_0)))))))).
fof(abs_def_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M)
                 => ((p__Lt___2(M, zero_0) => abs(M) = intToNat__(minus__(M)))
                     & (~ p__Lt___2(M, zero_0) => abs(M) = intToNat__(M)))))).
fof(add_def_Int,axiom,
    ! [A, B, C, D] : ((nat(A) & nat(B) & nat(C) & nat(D))
                      => ((((gn_defined(A) & gn_defined(B)) & gn_defined(C))
                           & gn_defined(D))
                          => o__Plus___2(o__Minus__(A, B), o__Minus__(C, D))
                             = o__Minus__(o__Plus__(A, C), o__Plus__(B, D))))).
fof(mult_def_Int,axiom,
    ! [A, B, C, D] : ((nat(A) & nat(B) & nat(C) & nat(D))
                      => ((((gn_defined(A) & gn_defined(B)) & gn_defined(C))
                           & gn_defined(D))
                          => o__x___2(o__Minus__(A, B), o__Minus__(C, D))
                             = o__Minus__(o__Plus__(o__x__(A, C), o__x__(B, D)),
                                          o__Plus__(o__x__(B, C),
                                                    o__x__(A, D)))))).
fof(sub_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => o__Minus___2(M, N) = o__Plus___2(M, minus__(N))))).
fof(min_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => ((p__LtEq___2(M, N) => min_2(M, N) = M)
                        & (~ p__LtEq___2(M, N) => min_2(M, N) = N))))).
fof(max_def_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => ((p__LtEq___2(M, N) => max_2(M, N) = N)
                        & (~ p__LtEq___2(M, N) => max_2(M, N) = M))))).
fof(power_neg1_Int,axiom,
    ! [A] : (nat(A)
             => (gn_defined(A)
                 => ((even(A) => o__Caret___2(minus__(one_0), A) = one_0)
                     & (~ even(A)
                        => o__Caret___2(minus__(one_0), A)
                           = minus__(one_0)))))).
fof(power_others_Int,axiom,
    ! [M, A] : ((int(M) & nat(A))
                => ((gn_defined_1(M) & gn_defined(A))
                    => (~ M = minus__(one_0)
                        => o__Caret___2(M, A)
                           = o__x___2(o__Caret___2(sign(M), A),
                                      o__Caret___2(natToInt__(abs(M)), A)))))).
fof(divide_dom2_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (gn_defined_1(o__SlashQuest___2(M, N))
                        <=> o__mod___2(M, N) = zero)))).
fof(divide_alt_Int,axiom,
    ! [M, N, R] : ((int(M) & int(N) & int(R))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(R))
                       => (o__SlashQuest___2(M, N) = R
                           <=> (~ N = zero_0 & o__x___2(N, R) = M))))).
fof(divide_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => o__SlashQuest___2(M, N)
                       = o__x___2(o__x___2(sign(M), sign(N)),
                                  o__SlashQuest___2(natToInt__(abs(M)),
                                                    natToInt__(abs(N))))))).
fof(div_dom_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (gn_defined_1(o__div___2(M, N)) <=> ~ N = zero_0)))).
fof(div_Int,axiom,
    ! [M, N, R] : ((int(M) & int(N) & int(R))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(R))
                       => (o__div___2(M, N) = R
                           <=> ? [A] : (nat(A)
                                        & (gn_defined(A)
                                           & (M
                                              = o__Plus___2(o__x___2(N, R),
                                                            natToInt__(A))
                                              & p__Lt__(A, abs(N))))))))).
fof(quot_dom_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (gn_defined_1(o__quot__(M, N)) <=> ~ N = zero_0)))).
fof(quot_neg_Int,axiom,
    ! [M, N, R] : ((int(M) & int(N) & int(R))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(R))
                       => (p__Lt___2(M, zero_0)
                           => (o__quot__(M, N) = R
                               <=> ? [S] : (int(S)
                                            & (gn_defined_1(S)
                                               & ((M
                                                   = o__Plus___2(o__x___2(N, R),
                                                                 S)
                                                   & p__GtEq___2(zero_0, S))
                                                  & p__Gt___2(S,
                                                              minus__(natToInt__(abs(N)))))))))))).
fof(quot_nonneg_Int,axiom,
    ! [M, N, R] : ((int(M) & int(N) & int(R))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(R))
                       => (p__GtEq___2(M, zero_0)
                           => (o__quot__(M, N) = R
                               <=> ? [S] : (int(S)
                                            & (gn_defined_1(S)
                                               & ((M
                                                   = o__Plus___2(o__x___2(N, R),
                                                                 S)
                                                   & p__LtEq___2(zero_0, S))
                                                  & p__Lt___2(S,
                                                              natToInt__(abs(N))))))))))).
fof(rem_dom_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (gn_defined_1(o__rem__(M, N)) <=> ~ N = zero_0)))).
fof(quot_rem_Int,axiom,
    ! [M, N, S] : ((int(M) & int(N) & int(S))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(S))
                       => (p__Lt___2(M, zero_0)
                           => (o__rem__(M, N) = S
                               <=> ? [R] : (int(R)
                                            & (gn_defined_1(R)
                                               & ((M
                                                   = o__Plus___2(o__x___2(N, R),
                                                                 S)
                                                   & p__GtEq___2(zero_0, S))
                                                  & p__Gt___2(S,
                                                              minus__(natToInt__(abs(N)))))))))))).
fof(rem_nonneg_Int,axiom,
    ! [M, N, S] : ((int(M) & int(N) & int(S))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined_1(S))
                       => (p__GtEq___2(M, zero_0)
                           => (o__rem__(M, N) = S
                               <=> ? [R] : (int(R)
                                            & (gn_defined_1(R)
                                               & ((M
                                                   = o__Plus___2(o__x___2(N, R),
                                                                 S)
                                                   & p__LtEq___2(zero_0, S))
                                                  & p__Lt___2(S,
                                                              natToInt__(abs(N))))))))))).
fof(mod_dom_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (gn_defined(o__mod___2(M, N)) <=> ~ N = zero_0)))).
fof(mod_Int,axiom,
    ! [M, N, A] : ((int(M) & int(N) & nat(A))
                   => (((gn_defined_1(M) & gn_defined_1(N)) & gn_defined(A))
                       => (o__mod___2(M, N) = A
                           <=> ? [R] : (int(R)
                                        & (gn_defined_1(R)
                                           & (M
                                              = o__Plus___2(o__x___2(N, R),
                                                            natToInt__(A))
                                              & p__Lt__(A, abs(N))))))))).
fof(distr1_Int,axiom,
    ! [R, S, T] : ((int(R) & int(S) & int(T))
                   => (((gn_defined_1(R) & gn_defined_1(S)) & gn_defined_1(T))
                       => o__x___2(o__Plus___2(R, S), T)
                          = o__Plus___2(o__x___2(R, T), o__x___2(S, T))))).
fof(distr2_Int,axiom,
    ! [R, S, T] : ((int(R) & int(S) & int(T))
                   => (((gn_defined_1(R) & gn_defined_1(S)) & gn_defined_1(T))
                       => o__x___2(T, o__Plus___2(R, S))
                          = o__Plus___2(o__x___2(T, R), o__x___2(T, S))))).
fof(int_Nat_sub_compat,axiom,
    ! [A, B] : ((nat(A) & nat(B))
                => ((gn_defined(A) & gn_defined(B))
                    => (gn_defined(o__MinusQuest__(A, B))
                        => o__MinusQuest__(A, B)
                           = intToNat__(o__Minus__(A, B)))))).
fof(abs_decomp_Int,axiom,
    ! [M] : (int(M)
             => (gn_defined_1(M)
                 => M = o__x___2(sign(M), natToInt__(abs(M)))))).
fof(mod_abs_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => o__mod___2(M, N) = o__mod___2(M, natToInt__(abs(N)))))).
fof(div_mod_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (~ N = zero_0
                        => M
                           = o__Plus___2(o__x___2(o__div___2(M, N), N),
                                         natToInt__(o__mod___2(M, N))))))).
fof(quot_abs_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => natToInt__(abs(o__quot__(M, N)))
                       = o__quot__(natToInt__(abs(M)), natToInt__(abs(N)))))).
fof(rem_abs_Int,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => natToInt__(abs(o__rem__(M, N)))
                       = o__rem__(natToInt__(abs(M)), natToInt__(abs(N)))))).
fof(quot_rem_Int_1,axiom,
    ! [M, N] : ((int(M) & int(N))
                => ((gn_defined_1(M) & gn_defined_1(N))
                    => (~ N = zero_0
                        => M
                           = o__Plus___2(o__x___2(o__quot__(M, N), N),
                                         o__rem__(M, N)))))).
fof(power_Int,axiom,
    ! [M, A, B] : ((int(M) & nat(A) & nat(B))
                   => (((gn_defined_1(M) & gn_defined(A)) & gn_defined(B))
                       => o__Caret___2(M, o__Plus__(A, B))
                          = o__x___2(o__Caret___2(M, A), o__Caret___2(M, B))))).
fof(arg_restriction_p__Lt___2,axiom,
    ! [Y0, Y1] : (p__Lt___2(Y0, Y1) => (int(Y0) & int(Y1)))).
fof(arg_restriction_p__Lt__,axiom,
    ! [Y0, Y1] : (p__Lt__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__LtEq___2,axiom,
    ! [Y0, Y1] : (p__LtEq___2(Y0, Y1) => (int(Y0) & int(Y1)))).
fof(arg_restriction_p__LtEq__,axiom,
    ! [Y0, Y1] : (p__LtEq__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__Gt___2,axiom,
    ! [Y0, Y1] : (p__Gt___2(Y0, Y1) => (int(Y0) & int(Y1)))).
fof(arg_restriction_p__Gt__,axiom,
    ! [Y0, Y1] : (p__Gt__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__GtEq___2,axiom,
    ! [Y0, Y1] : (p__GtEq___2(Y0, Y1) => (int(Y0) & int(Y1)))).
fof(arg_restriction_p__GtEq__,axiom,
    ! [Y0, Y1] : (p__GtEq__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_odd_1,axiom,
    ! [Y0] : (odd_1(Y0) => int(Y0))).
fof(arg_restriction_odd,axiom,
    ! [Y0] : (odd(Y0) => nat(Y0))).
fof(arg_restriction_gn_defined_1,axiom,
    ! [Y0] : (gn_defined_1(Y0) => int(Y0))).
fof(arg_restriction_gn_defined,axiom,
    ! [Y0] : (gn_defined(Y0) => nat(Y0))).
fof(arg_restriction_even_1,axiom,
    ! [Y0] : (even_1(Y0) => int(Y0))).
fof(arg_restriction_even,axiom,
    ! [Y0] : (even(Y0) => nat(Y0))).
fof(inconsistent,conjecture,
    $false).
