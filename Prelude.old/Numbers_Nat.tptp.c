%---------------------------------------------------------------------------
% Problem : hets_exported
% Name    : Basic/Numbers_Nat_inconsistent
% Author  : hets
% Status  : unknown
% Desc    : 
% Date    : Fri Jun 20 17:09:42 BRT 2008
% Option  : SPASS , [SPFlag "set_flag" ["TimeLimit","500"],SPFlag "set_flag" ["DocProof","1"]]
%---------------------------------------------------------------------------
fof(declaration0,axiom,
    ! [Y0] : (pos(Y0) => nat(Y0))).
fof(declaration1,axiom,
    nat(eight)).
fof(declaration2,axiom,
    nat(five)).
fof(declaration3,axiom,
    nat(four)).
fof(declaration4,axiom,
    nat(gn_bottom_Nat)).
fof(declaration5,axiom,
    pos(gn_bottom_Pos)).
fof(declaration6,axiom,
    ! [X1] : (nat(X1) => pos(gn_proj_Nat_Pos(X1)))).
fof(declaration7,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(max(X1, X2)))).
fof(declaration8,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(min(X1, X2)))).
fof(declaration9,axiom,
    nat(nine)).
fof(declaration10,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__AtAt__(X1, X2)))).
fof(declaration11,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__Caret__(X1, X2)))).
fof(declaration12,axiom,
    ! [X1] : (nat(X1) => nat(o__Exclam(X1)))).
fof(declaration13,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__MinusExclam__(X1, X2)))).
fof(declaration14,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__MinusQuest__(X1, X2)))).
fof(declaration15,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__Plus__(X1, X2)))).
fof(declaration16,axiom,
    ! [X1, X2] : ((nat(X1) & pos(X2)) => pos(o__Plus__(X1, X2)))).
fof(declaration17,axiom,
    ! [X1, X2] : ((pos(X1) & nat(X2)) => pos(o__Plus__(X1, X2)))).
fof(declaration18,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2))
                  => nat(o__SlashQuest__(X1, X2)))).
fof(declaration19,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__div__(X1, X2)))).
fof(declaration20,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__mod__(X1, X2)))).
fof(declaration21,axiom,
    ! [X1, X2] : ((nat(X1) & nat(X2)) => nat(o__x__(X1, X2)))).
fof(declaration22,axiom,
    ! [X1, X2] : ((pos(X1) & pos(X2)) => pos(o__x__(X1, X2)))).
fof(declaration23,axiom,
    nat(one)).
fof(declaration24,axiom,
    pos(one)).
fof(declaration25,axiom,
    ! [X1] : (nat(X1) => nat(pre(X1)))).
fof(declaration26,axiom,
    nat(seven)).
fof(declaration27,axiom,
    nat(six)).
fof(declaration28,axiom,
    ! [X1] : (nat(X1) => nat(suc(X1)))).
fof(declaration29,axiom,
    ! [X1] : (nat(X1) => pos(suc(X1)))).
fof(declaration30,axiom,
    nat(three)).
fof(declaration31,axiom,
    nat(two)).
fof(declaration32,axiom,
    nat(zero)).
fof(ga_non_empty_sort_nat,axiom,
    ? [Y] : nat(Y)).
fof(ga_non_empty_sort_pos,axiom,
    ? [Y] : pos(Y)).
fof(ga_projection_injectivity,axiom,
    ! [X, Y] : ((nat(X) & nat(Y))
                => (((gn_defined(gn_proj_Nat_Pos(X))
                      & gn_defined(gn_proj_Nat_Pos(Y)))
                     & gn_proj_Nat_Pos(X) = gn_proj_Nat_Pos(Y))
                    => X = Y))).
fof(ga_projection,axiom,
    ! [X] : (pos(X) => (gn_defined(X) => gn_proj_Nat_Pos(X) = X))).
fof(ga_nonEmpty,axiom,
    ? [X] : (nat(X) & gn_defined(X))).
fof(ga_notDefBottom,axiom,
    ! [X] : (nat(X) => (~ gn_defined(X) <=> X = gn_bottom_Nat))).
fof(ga_nonEmpty_1,axiom,
    ? [X] : (pos(X) & gn_defined(X))).
fof(ga_notDefBottom_1,axiom,
    ! [X] : (pos(X) => (~ gn_defined(X) <=> X = gn_bottom_Pos))).
fof(ga_totality,axiom,
    gn_defined(zero)).
fof(ga_totality_1,axiom,
    gn_defined(one)).
fof(ga_totality_2,axiom,
    gn_defined(one)).
fof(ga_totality_3,axiom,
    gn_defined(two)).
fof(ga_totality_4,axiom,
    gn_defined(three)).
fof(ga_totality_5,axiom,
    gn_defined(four)).
fof(ga_totality_6,axiom,
    gn_defined(five)).
fof(ga_totality_7,axiom,
    gn_defined(six)).
fof(ga_totality_8,axiom,
    gn_defined(seven)).
fof(ga_totality_9,axiom,
    gn_defined(eight)).
fof(ga_totality_10,axiom,
    gn_defined(nine)).
fof(ga_totality_11,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined(o__Exclam(X_1)) <=> gn_defined(X_1)))).
fof(ga_totality_12,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__x__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_13,axiom,
    ! [X_1, X_2] : ((pos(X_1) & pos(X_2))
                    => (gn_defined(o__x__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_14,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__Plus__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_15,axiom,
    ! [X_1, X_2] : ((nat(X_1) & pos(X_2))
                    => (gn_defined(o__Plus__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_16,axiom,
    ! [X_1, X_2] : ((pos(X_1) & nat(X_2))
                    => (gn_defined(o__Plus__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_17,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__MinusExclam__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_18,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__AtAt__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_19,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__Caret__(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_20,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(max(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_21,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(min(X_1, X_2))
                        <=> (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_totality_22,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined(suc(X_1)) <=> gn_defined(X_1)))).
fof(ga_totality_23,axiom,
    ! [X_1] : (nat(X_1)
               => (gn_defined(suc(X_1)) <=> gn_defined(X_1)))).
fof(ga_strictness,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__MinusQuest__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_1,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__SlashQuest__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_2,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__div__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_3,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (gn_defined(o__mod__(X_1, X_2))
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_strictness_4,axiom,
    ! [X_1] : (nat(X_1) => (gn_defined(pre(X_1)) => gn_defined(X_1)))).
fof(ga_predicate_strictness,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__Lt__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_1,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__LtEq__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_2,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__Gt__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_3,axiom,
    ! [X_1, X_2] : ((nat(X_1) & nat(X_2))
                    => (p__GtEq__(X_1, X_2)
                        => (gn_defined(X_1) & gn_defined(X_2))))).
fof(ga_predicate_strictness_4,axiom,
    ! [X_1] : (nat(X_1) => (even(X_1) => gn_defined(X_1)))).
fof(ga_predicate_strictness_5,axiom,
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
fof(pos_def,axiom,
    ! [P] : (nat(P)
             => (gn_defined(P)
                 => (gn_defined(gn_proj_Nat_Pos(P)) <=> p__Gt__(P, zero))))).
fof(one_as_Pos_def,axiom,
    one = suc(zero)).
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
fof(arg_restriction_p__Lt__,axiom,
    ! [Y0, Y1] : (p__Lt__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__LtEq__,axiom,
    ! [Y0, Y1] : (p__LtEq__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__Gt__,axiom,
    ! [Y0, Y1] : (p__Gt__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_p__GtEq__,axiom,
    ! [Y0, Y1] : (p__GtEq__(Y0, Y1) => (nat(Y0) & nat(Y1)))).
fof(arg_restriction_odd,axiom,
    ! [Y0] : (odd(Y0) => nat(Y0))).
fof(arg_restriction_o_gn_defined,axiom,
    ! [Y0] : (gn_defined(Y0) => (pos(Y0) | nat(Y0)))).
fof(arg_restriction_even,axiom,
    ! [Y0] : (even(Y0) => nat(Y0))).
fof(inconsistent,conjecture,
    $false).
