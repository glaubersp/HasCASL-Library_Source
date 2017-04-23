theory Prelude_NumericClasses
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"ga_monotonicity\", \"ga_monotonicity_1\", \"ga_monotonicity_2\",
        \"ga_monotonicity_3\", \"ga_monotonicity_4\",
        \"ga_monotonicity_5\", \"ga_monotonicity_6\",
        \"ga_monotonicity_7\", \"ga_monotonicity_8\",
        \"ga_monotonicity_9\", \"ga_monotonicity_10\",
        \"ga_monotonicity_11\", \"ga_monotonicity_12\",
        \"ga_monotonicity_13\", \"ga_monotonicity_14\",
        \"ga_monotonicity_15\", \"ga_monotonicity_16\",
        \"ga_monotonicity_17\", \"ga_monotonicity_18\",
        \"ga_monotonicity_19\", \"ga_monotonicity_20\",
        \"ga_monotonicity_21\", \"ga_monotonicity_22\",
        \"ga_monotonicity_23\", \"ga_monotonicity_24\",
        \"ga_monotonicity_25\", \"ga_monotonicity_26\",
        \"ga_monotonicity_27\", \"ga_monotonicity_28\",
        \"ga_monotonicity_29\", \"ga_monotonicity_30\",
        \"ga_monotonicity_31\", \"ga_monotonicity_32\",
        \"ga_monotonicity_33\", \"ga_monotonicity_34\",
        \"ga_monotonicity_35\", \"ga_monotonicity_36\",
        \"ga_monotonicity_37\", \"ga_monotonicity_38\",
        \"ga_monotonicity_39\", \"ga_monotonicity_40\",
        \"ga_monotonicity_41\", \"ga_monotonicity_42\",
        \"ga_monotonicity_43\", \"ga_monotonicity_44\",
        \"ga_monotonicity_45\", \"ga_monotonicity_46\",
        \"ga_monotonicity_47\", \"ga_monotonicity_48\",
        \"ga_monotonicity_49\", \"ga_monotonicity_50\",
        \"ga_monotonicity_51\", \"ga_monotonicity_52\",
        \"ga_monotonicity_53\", \"ga_monotonicity_54\",
        \"ga_monotonicity_55\", \"ga_monotonicity_56\",
        \"ga_monotonicity_57\", \"ga_monotonicity_58\",
        \"ga_monotonicity_59\", \"ga_monotonicity_60\",
        \"ga_monotonicity_61\", \"ga_monotonicity_62\",
        \"ga_monotonicity_63\", \"ga_monotonicity_64\",
        \"ga_monotonicity_65\", \"ga_monotonicity_66\",
        \"ga_monotonicity_67\", \"ga_monotonicity_68\",
        \"ga_monotonicity_69\", \"ga_monotonicity_70\",
        \"ga_monotonicity_71\", \"ga_monotonicity_72\",
        \"ga_monotonicity_73\", \"ga_monotonicity_74\",
        \"ga_monotonicity_75\", \"ga_monotonicity_76\",
        \"ga_monotonicity_77\", \"ga_monotonicity_78\",
        \"ga_monotonicity_79\", \"ga_monotonicity_80\",
        \"ga_monotonicity_81\", \"ga_monotonicity_82\",
        \"ga_monotonicity_83\", \"ga_monotonicity_84\",
        \"ga_monotonicity_85\", \"ga_monotonicity_86\",
        \"ga_monotonicity_87\", \"ga_monotonicity_88\",
        \"ga_monotonicity_89\", \"ga_monotonicity_90\",
        \"ga_subt_reflexive\", \"ga_subt_transitive\",
        \"ga_subt_inj_proj\", \"ga_inj_transitive\",
        \"ga_subt_Int_XLt_Rat\", \"ga_subt_Nat_XLt_Int\",
        \"ga_subt_Pos_XLt_Nat\", \"NotFalse\", \"NotTrue\", \"AndFalse\",
        \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
        \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\",
        \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\", \"EqualTransT\",
        \"DiffDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\",
        \"TE2\", \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\",
        \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\",
        \"IOE01\", \"IOE02\", \"IOE03\", \"IOE04\", \"IOE05\", \"IOE06\",
        \"IOE07\", \"IOE08\", \"IOE09\", \"LeIrreflexivity\",
        \"LeTAsymmetry\", \"LeTTransitive\", \"LeTTotal\", \"GeDef\",
        \"GeIrreflexivity\", \"GeTAsymmetry\", \"GeTTransitive\",
        \"GeTTotal\", \"LeqDef\", \"LeqReflexivity\", \"LeqTTransitive\",
        \"LeqTTotal\", \"GeqDef\", \"GeqReflexivity\", \"GeqTTransitive\",
        \"GeqTTotal\", \"EqTSOrdRel\", \"EqFSOrdRel\", \"EqTOrdRel\",
        \"EqFOrdRel\", \"EqTOrdTSubstE\", \"EqTOrdFSubstE\",
        \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeFEqFRel\",
        \"LeFGeTEqTRel\", \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\",
        \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\",
        \"GeqFLeqFRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
        \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
        \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
        \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
        \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
        \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO3\",
        \"TO4\", \"TO5\", \"IOO13\", \"IOO14\", \"IOO15\", \"IOO16\",
        \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\",
        \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\",
        \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\", \"IOO33\", \"IBO5\",
        \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\", \"IBO10\", \"IBO11\",
        \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\",
        \"IUO06\", \"IUO07\", \"ga_selector_pre\", \"ga_injective_suc\",
        \"ga_disjoint_0_suc\", \"ga_selector_undef_pre_0\", \"X1_def_Nat\",
        \"X2_def_Nat\", \"X3_def_Nat\", \"X4_def_Nat\", \"X5_def_Nat\",
        \"X6_def_Nat\", \"X7_def_Nat\", \"X8_def_Nat\", \"X9_def_Nat\",
        \"decimal_def\", \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
        \"ga_right_unit___XPlus__\", \"ga_left_unit___XPlus__\",
        \"ga_left_comm___XPlus__\", \"ga_comm___Xx__\",
        \"ga_assoc___Xx__\", \"ga_right_unit___Xx__\",
        \"ga_left_unit___Xx__\", \"ga_left_comm___Xx__\", \"ga_comm_min\",
        \"ga_assoc_min\", \"ga_left_comm_min\", \"ga_comm_max\",
        \"ga_assoc_max\", \"ga_right_unit_max\", \"ga_left_unit_max\",
        \"ga_left_comm_max\", \"leq_def1_Nat\", \"dvd_def_Nat\",
        \"leq_def2_Nat\", \"leq_def3_Nat\", \"geq_def_Nat\",
        \"less_def_Nat\", \"greater_def_Nat\", \"even_0_Nat\",
        \"even_suc_Nat\", \"odd_def_Nat\", \"factorial_0\",
        \"factorial_suc\", \"add_0_Nat\", \"add_suc_Nat\", \"mult_0_Nat\",
        \"mult_suc_Nat\", \"power_0_Nat\", \"power_suc_Nat\",
        \"min_def_Nat\", \"max_def_Nat\", \"subTotal_def1_Nat\",
        \"subTotal_def2_Nat\", \"sub_dom_Nat\", \"sub_def_Nat\",
        \"divide_dom_Nat\", \"divide_0_Nat\", \"divide_Pos_Nat\",
        \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\", \"mod_Nat\",
        \"distr1_Nat\", \"distr2_Nat\", \"Pos_def\", \"X1_as_Pos_def\",
        \"min_0\", \"div_mod_Nat\", \"power_Nat\", \"ga_generated_Int\",
        \"equality_Int\", \"Nat2Int_embedding\", \"ga_comm___XPlus___80\",
        \"ga_assoc___XPlus___76\", \"ga_right_unit___XPlus___90\",
        \"ga_left_unit___XPlus___88\", \"ga_left_comm___XPlus___84\",
        \"ga_comm___Xx___79\", \"ga_assoc___Xx___75\",
        \"ga_right_unit___Xx___89\", \"ga_left_unit___Xx___87\",
        \"ga_left_comm___Xx___83\", \"ga_comm_min_82\", \"ga_comm_max_81\",
        \"ga_assoc_min_78\", \"ga_assoc_max_77\", \"ga_left_comm_min_86\",
        \"ga_left_comm_max_85\", \"leq_def_Int\", \"geq_def_Int\",
        \"less_def_Int\", \"greater_def_Int\", \"even_def_Int\",
        \"odd_def_Int\", \"odd_alt_Int\", \"neg_def_Int\",
        \"sign_def_Int\", \"abs_def_Int\", \"add_def_Int\",
        \"mult_def_Int\", \"sub_def_Int\", \"min_def_Int\",
        \"max_def_Int\", \"power_neg1_Int\", \"power_others_Int\",
        \"divide_dom2_Int\", \"divide_alt_Int\", \"divide_Int\",
        \"div_dom_Int\", \"div_Int\", \"quot_dom_Int\", \"quot_neg_Int\",
        \"quot_nonneg_Int\", \"rem_dom_Int\", \"rem_neg_Int\",
        \"rem_nonneg_Int\", \"mod_dom_Int\", \"mod_Int\", \"distr1_Int\",
        \"distr2_Int\", \"Int_Nat_sub_compat\", \"abs_decomp_Int\",
        \"mod_abs_Int\", \"div_mod_Int\", \"quot_abs_Int\",
        \"rem_abs_Int\", \"quot_rem_Int\", \"power_Int\",
        \"ga_generated_Rat\", \"equality_Rat\", \"Int2Rat_embedding\",
        \"ga_comm___XPlus___139\", \"ga_assoc___XPlus___135\",
        \"ga_right_unit___XPlus___149\", \"ga_left_unit___XPlus___147\",
        \"ga_left_comm___XPlus___143\", \"ga_comm___Xx___138\",
        \"ga_assoc___Xx___134\", \"ga_right_unit___Xx___148\",
        \"ga_left_unit___Xx___146\", \"ga_left_comm___Xx___142\",
        \"ga_comm_min_141\", \"ga_comm_max_140\", \"ga_assoc_min_137\",
        \"ga_assoc_max_136\", \"ga_left_comm_min_145\",
        \"ga_left_comm_max_144\", \"leq_def_Rat\", \"geq_def_Rat\",
        \"less_def_Rat\", \"greater_def_Rat\", \"minus_def_Rat\",
        \"abs_def_Rat\", \"add_def_Rat\", \"sub_def_Rat\",
        \"mult_def_Rat\", \"min_def_Rat\", \"max_def_Rat\",
        \"divide_def1_Rat\", \"divide_def2_Rat\", \"power_0_Rat\",
        \"power_suc_Rat\", \"power_neg_Rat\", \"distr1_Rat\",
        \"distr2_Rat\", \"sub_rule_Rat\", \"divide_dom_Rat\",
        \"divide_rule_Rat\", \"power_Rat\", \"IPN01\", \"IPN02\",
        \"IPN03\", \"IPN04\", \"IPN05\", \"IPN06\", \"IPN07\", \"INN01\",
        \"INN02\", \"INN03\", \"INN04\", \"INN05\", \"INN06\", \"INN07\",
        \"IIN01\", \"IIN02\", \"IIN03\", \"IIN04\", \"IIN05\", \"IIN06\",
        \"IIN07\", \"IIN07_1\", \"IIN08\", \"IIN09\", \"IRN01\", \"IRN02\",
        \"IRN03\", \"IRN04\", \"IRN05\", \"IRN06\", \"IRN07\", \"IRN07_2\",
        \"IRN08\", \"IRN09\", \"IRI01\", \"IRI02\", \"IRI03\", \"IRI04\",
        \"IRI05\", \"IRI06\", \"IRI01_3\", \"IRI02_4\", \"IRF01\",
        \"IRF02\", \"AbsSignumLaw\"]"

typedecl Pos
typedecl Rat
typedecl Unit
typedecl X_Int

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype X_Nat = X0X2 ("0''''") |
                 sucX1 "X_Nat" ("suc''/'(_')" [3] 999)

consts
X0X1 :: "X_Int" ("0''")
X0X3 :: "Rat" ("0'_3")
X1X1 :: "X_Int" ("1''")
X1X2 :: "X_Nat" ("1''''")
X1X3 :: "Pos" ("1'_3")
X1X4 :: "Rat" ("1'_4")
X2X1 :: "X_Int" ("2''")
X2X2 :: "X_Nat" ("2''''")
X2X3 :: "Rat" ("2'_3")
X3X1 :: "X_Int" ("3''")
X3X2 :: "X_Nat" ("3''''")
X3X3 :: "Rat" ("3'_3")
X4X1 :: "X_Int" ("4''")
X4X2 :: "X_Nat" ("4''''")
X4X3 :: "Rat" ("4'_3")
X5X1 :: "X_Int" ("5''")
X5X2 :: "X_Nat" ("5''''")
X5X3 :: "Rat" ("5'_3")
X6X1 :: "X_Int" ("6''")
X6X2 :: "X_Nat" ("6''''")
X6X3 :: "Rat" ("6'_3")
X7X1 :: "X_Int" ("7''")
X7X2 :: "X_Nat" ("7''''")
X7X3 :: "Rat" ("7'_3")
X8X1 :: "X_Int" ("8''")
X8X2 :: "X_Nat" ("8''''")
X8X3 :: "Rat" ("8'_3")
X9X1 :: "X_Int" ("9''")
X9X2 :: "X_Nat" ("9''''")
X9X3 :: "Rat" ("9'_3")
XMinus__XX1 :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Rat => Rat" ("(-''''/ _)" [56] 56)
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XCaret__XX3 :: "Rat => X_Int => Rat partial" ("(_/ ^'_3/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "Rat => Rat => bool" ("(_/ >='_3/ _)" [44,44] 42)
X__XGtXEq__XX4 :: "'a => 'a => Bool" ("(_/ >='_4/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "Rat => Rat => bool" ("(_/ >'_3/ _)" [44,44] 42)
X__XGt__XX4 :: "'a => 'a => Bool" ("(_/ >'_4/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Rat => Rat => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLtXEq__XX4 :: "'a => 'a => Bool" ("(_/ <='_4/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "Rat => Rat => bool" ("(_/ <'_3/ _)" [44,44] 42)
X__XLt__XX4 :: "'a => 'a => Bool" ("(_/ <'_4/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Rat => Rat => Rat" ("(_/ -'_3/ _)" [54,54] 52)
X__XMinus__XX4 :: "'a => 'a => 'a" ("(_/ -'_4/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Pos => X_Nat => Pos" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "Rat => Rat => Rat" ("(_/ +'_5/ _)" [54,54] 52)
X__XPlus__XX6 :: "'a => 'a => 'a" ("(_/ +'_6/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XSlash__XX1 :: "X_Int => Pos => Rat" ("(_/ '/''/ _)" [54,54] 52)
X__XSlash__XX2 :: "Rat => Rat => Rat partial" ("(_/ '/''''/ _)" [54,54] 52)
X__XSlash__XX3 :: "'a => 'a => 'a" ("(_/ '/'_3/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Pos => Pos => Pos" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Rat => Rat => Rat" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "'a => 'a => 'a" ("(_/ *'_5/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__div__XX3 :: "'a => 'a => 'a" ("(_/ div'_3/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__mod__XX3 :: "'a => 'a => 'a" ("(_/ mod'_3/ _)" [54,54] 52)
X__quot__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ quot''/ _)" [54,54] 52)
X__quot__XX2 :: "'a => 'a => 'a" ("(_/ quot''''/ _)" [54,54] 52)
X__rem__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ rem''/ _)" [54,54] 52)
X__rem__XX2 :: "'a => 'a => 'a" ("(_/ rem''''/ _)" [54,54] 52)
X_absX1 :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_absX2 :: "Rat => Rat" ("abs''''/'(_')" [3] 999)
X_absX3 :: "'a => 'a" ("abs'_3/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_fromInteger :: "X_Int => 'a" ("fromInteger/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "Rat => Rat => Rat" ("max'_3/'(_,/ _')" [3,3] 999)
X_maxX4 :: "'a => 'a => 'a"
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "Rat => Rat => Rat" ("min'_3/'(_,/ _')" [3,3] 999)
X_minX4 :: "'a => 'a => 'a"
X_negate :: "'a => 'a" ("negate/'(_')" [3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_recip :: "'a => 'a" ("recip/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_signum :: "'a => 'a" ("signum/'(_')" [3] 999)
X_toInteger :: "'a => X_Int" ("toInteger/'(_')" [3] 999)
compare :: "'a => 'a => Ordering"
divMod :: "'a => 'a => 'a * 'a"
notH__X :: "Bool => Bool" ("(notH/ _)" [56] 56)
otherwiseH :: "Bool"
quotRem :: "'a => 'a => 'a * 'a"
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)

axioms
ga_monotonicity [rule_format] :
"(X_gn_inj :: (X_Int => X_Int) => X_Int => Rat) XMinus__XX1 =
 (X_gn_inj :: (Rat => Rat) => X_Int => Rat) XMinus__XX2"

ga_monotonicity_1 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 0' =
 (X_gn_inj :: X_Nat => X_Int) 0''"

ga_monotonicity_2 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 0' = (X_gn_inj :: Rat => Rat) 0_3"

ga_monotonicity_3 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 0'' = (X_gn_inj :: Rat => Rat) 0_3"

ga_monotonicity_4 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 1' =
 (X_gn_inj :: X_Nat => X_Int) 1''"

ga_monotonicity_5 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 1' = (X_gn_inj :: Pos => X_Int) 1_3"

ga_monotonicity_6 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 1' = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_7 [rule_format] :
"(X_gn_inj :: X_Nat => X_Nat) 1'' = (X_gn_inj :: Pos => X_Nat) 1_3"

ga_monotonicity_8 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 1'' = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_9 [rule_format] :
"(X_gn_inj :: Pos => Rat) 1_3 = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_10 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 2' =
 (X_gn_inj :: X_Nat => X_Int) 2''"

ga_monotonicity_11 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 2' = (X_gn_inj :: Rat => Rat) 2_3"

ga_monotonicity_12 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 2'' = (X_gn_inj :: Rat => Rat) 2_3"

ga_monotonicity_13 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 3' =
 (X_gn_inj :: X_Nat => X_Int) 3''"

ga_monotonicity_14 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 3' = (X_gn_inj :: Rat => Rat) 3_3"

ga_monotonicity_15 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 3'' = (X_gn_inj :: Rat => Rat) 3_3"

ga_monotonicity_16 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 4' =
 (X_gn_inj :: X_Nat => X_Int) 4''"

ga_monotonicity_17 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 4' = (X_gn_inj :: Rat => Rat) 4_3"

ga_monotonicity_18 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 4'' = (X_gn_inj :: Rat => Rat) 4_3"

ga_monotonicity_19 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 5' =
 (X_gn_inj :: X_Nat => X_Int) 5''"

ga_monotonicity_20 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 5' = (X_gn_inj :: Rat => Rat) 5_3"

ga_monotonicity_21 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 5'' = (X_gn_inj :: Rat => Rat) 5_3"

ga_monotonicity_22 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 6' =
 (X_gn_inj :: X_Nat => X_Int) 6''"

ga_monotonicity_23 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 6' = (X_gn_inj :: Rat => Rat) 6_3"

ga_monotonicity_24 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 6'' = (X_gn_inj :: Rat => Rat) 6_3"

ga_monotonicity_25 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 7' =
 (X_gn_inj :: X_Nat => X_Int) 7''"

ga_monotonicity_26 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 7' = (X_gn_inj :: Rat => Rat) 7_3"

ga_monotonicity_27 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 7'' = (X_gn_inj :: Rat => Rat) 7_3"

ga_monotonicity_28 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 8' =
 (X_gn_inj :: X_Nat => X_Int) 8''"

ga_monotonicity_29 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 8' = (X_gn_inj :: Rat => Rat) 8_3"

ga_monotonicity_30 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 8'' = (X_gn_inj :: Rat => Rat) 8_3"

ga_monotonicity_31 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 9' =
 (X_gn_inj :: X_Nat => X_Int) 9''"

ga_monotonicity_32 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 9' = (X_gn_inj :: Rat => Rat) 9_3"

ga_monotonicity_33 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 9'' = (X_gn_inj :: Rat => Rat) 9_3"

ga_monotonicity_34 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__Xx__XX2)"

ga_monotonicity_35 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => Pos * Pos => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => X_Int)
 (uncurryOp X__Xx__XX3)"

ga_monotonicity_36 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_37 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_38 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => Pos * Pos => X_Nat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => X_Nat)
 (uncurryOp X__Xx__XX3)"

ga_monotonicity_39 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_40 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_41 [rule_format] :
"(X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Rat)
 (uncurryOp X__Xx__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => Pos * Pos => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_42 [rule_format] :
"(X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__Xx__XX3) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_43 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__Xx__XX4) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_44 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX2)"

ga_monotonicity_45 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * Pos => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => X_Int)
 (uncurryOp X__XPlus__XX3)"

ga_monotonicity_46 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => Pos * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_47 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_48 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_49 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * Pos => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => X_Nat)
 (uncurryOp X__XPlus__XX3)"

ga_monotonicity_50 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => Pos * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_51 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_52 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_53 [rule_format] :
"(X_gn_inj :: (X_Nat * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__XPlus__XX3) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * Pos => Pos)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_54 [rule_format] :
"(X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => Rat)
 (uncurryOp X__XPlus__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * Pos => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_55 [rule_format] :
"(X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => Rat)
 (uncurryOp X__XPlus__XX4) =
 (X_gn_inj :: (Rat * Rat => Rat) => Pos * X_Nat => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_56 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XPlus__XX5) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_57 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX2)"

ga_monotonicity_58 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__XMinus__XX3)"

ga_monotonicity_59 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_60 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XMinus__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XMinus__XX3)"

ga_monotonicity_61 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX2) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_62 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XMinus__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_63 [rule_format] :
"(X_gn_inj :: (X_Int * Pos => Rat) => X_Int * Pos => Rat)
 (uncurryOp X__XSlash__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * Pos => Rat)
 (uncurryOp X__XSlash__XX3)"

ga_monotonicity_64 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__XSlashXQuest__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__XSlashXQuest__XX2)"

ga_monotonicity_65 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX2)"

ga_monotonicity_66 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLt__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLt__XX3)"

ga_monotonicity_67 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX3)"

ga_monotonicity_68 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX2)"

ga_monotonicity_69 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLtXEq__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLtXEq__XX3)"

ga_monotonicity_70 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX3)"

ga_monotonicity_71 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX2)"

ga_monotonicity_72 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGt__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGt__XX3)"

ga_monotonicity_73 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX3)"

ga_monotonicity_74 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX2)"

ga_monotonicity_75 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGtXEq__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGtXEq__XX3)"

ga_monotonicity_76 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX3)"

ga_monotonicity_77 [rule_format] :
"(X_gn_inj :: (X_Int * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XCaret__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XCaret__XX2)"

ga_monotonicity_78 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__div__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__div__XX2)"

ga_monotonicity_79 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Nat partial) => X_Nat * X_Nat => X_Nat partial)
 (uncurryOp X__mod__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Nat partial)
 (uncurryOp X__mod__XX2)"

ga_monotonicity_80 [rule_format] :
"(X_gn_inj :: (X_Int => X_Nat) => X_Int => Rat) X_absX1 =
 (X_gn_inj :: (Rat => Rat) => X_Int => Rat) X_absX2"

ga_monotonicity_81 [rule_format] :
"(X_gn_inj :: (Rat => Rat) => Rat => Rat) X_absX2 =
 (X_gn_inj :: (Rat => Rat) => Rat => Rat) X_absX3"

ga_monotonicity_82 [rule_format] :
"(X_gn_inj :: (X_Int => bool) => X_Nat => bool) X_evenX1 =
 (X_gn_inj :: (X_Nat => bool) => X_Nat => bool) X_evenX2"

ga_monotonicity_83 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_maxX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_maxX2)"

ga_monotonicity_84 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X_maxX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X_maxX3)"

ga_monotonicity_85 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_maxX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_maxX3)"

ga_monotonicity_86 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_minX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_minX2)"

ga_monotonicity_87 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X_minX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X_minX3)"

ga_monotonicity_88 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_minX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_minX3)"

ga_monotonicity_89 [rule_format] :
"(X_gn_inj :: (X_Int => bool) => X_Nat => bool) X_oddX1 =
 (X_gn_inj :: (X_Nat => bool) => X_Nat => bool) X_oddX2"

ga_monotonicity_90 [rule_format] :
"(X_gn_inj :: (X_Nat => X_Nat) => X_Nat => X_Nat) sucX1 =
 (X_gn_inj :: (X_Nat => Pos) => X_Nat => X_Nat) sucX2"

ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt(x, y)"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c). gn_subt(x, y) & gn_subt(y, z) --> gn_subt(x, z)"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt(x, y) -->
 y = (X_gn_inj :: 'a => 'b) x =
 (makePartial x = (X_gn_proj :: 'b => 'a partial) y)"

ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt(x, y) & gn_subt(y, z) & y = (X_gn_inj :: 'a => 'b) x -->
 z = (X_gn_inj :: 'a => 'c) x = (z = (X_gn_inj :: 'b => 'c) y)"

ga_subt_Int_XLt_Rat [rule_format] :
"ALL (x :: X_Int). ALL (y :: Rat). gn_subt(x, y)"

ga_subt_Nat_XLt_Int [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Int). gn_subt(x, y)"

ga_subt_Pos_XLt_Nat [rule_format] :
"ALL (x :: Pos). ALL (y :: X_Nat). gn_subt(x, y)"

NotFalse [rule_format] : "notH False' = True'"

NotTrue [rule_format] : "notH True' = False'"

AndFalse [rule_format] : "ALL (x :: Bool). False' && x = False'"

AndTrue [rule_format] : "ALL (x :: Bool). True' && x = x"

AndSym [rule_format] :
"ALL (x :: Bool). ALL (y :: Bool). x && y = y && x"

OrDef [rule_format] :
"ALL (x :: Bool).
 ALL (y :: Bool). x || y = notH (notH x && notH y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

NotFalse1 [rule_format] :
"ALL (x :: Bool). notH x = True' = (x = False')"

NotTrue1 [rule_format] :
"ALL (x :: Bool). notH x = False' = (x = True')"

notNot1 [rule_format] :
"ALL (x :: Bool). (~ x = True') = (notH x = True')"

notNot2 [rule_format] :
"ALL (x :: Bool). (~ x = False') = (notH x = False')"

EqualTDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x = y --> x ==' y = True'"

EqualSymDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL (x :: 'a). x ==' x = True'"

EqualTransT [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & y ==' z = True' --> x ==' z = True'"

DiffDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x /= y = notH (x ==' y)"

DiffSymDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x /= y = y /= x"

DiffTDef [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x /= y = True' = (notH (x ==' y) = True')"

DiffFDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x /= y = False' = (x ==' y = True')"

TE1 [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x ==' y = False' --> ~ x = y"

TE2 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). notH (x ==' y) = True' = (x ==' y = False')"

TE3 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). notH (x ==' y) = False' = (x ==' y = True')"

TE4 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). (~ x ==' y = True') = (x ==' y = False')"

IBE1 [rule_format] : "True' ==' True' = True'"

IBE2 [rule_format] : "False' ==' False' = True'"

IBE3 [rule_format] : "False' ==' True' = False'"

IBE4 [rule_format] : "True' ==' False' = False'"

IBE5 [rule_format] : "True' /= False' = True'"

IBE6 [rule_format] : "False' /= True' = True'"

IBE7 [rule_format] : "notH (True' ==' False') = True'"

IBE8 [rule_format] : "notH notH (True' ==' False') = False'"

IUE1 [rule_format] : "() ==' () = True'"

IUE2 [rule_format] : "() /= () = False'"

IOE01 [rule_format] : "LT ==' LT = True'"

IOE02 [rule_format] : "EQ ==' EQ = True'"

IOE03 [rule_format] : "GT ==' GT = True'"

IOE04 [rule_format] : "LT ==' EQ = False'"

IOE05 [rule_format] : "LT ==' GT = False'"

IOE06 [rule_format] : "EQ ==' GT = False'"

IOE07 [rule_format] : "LT /= EQ = True'"

IOE08 [rule_format] : "LT /= GT = True'"

IOE09 [rule_format] : "EQ /= GT = True'"

LeIrreflexivity [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x ==' y = True' --> x <_4 y = False'"

LeTAsymmetry [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <_4 y = True' --> y <_4 x = False'"

LeTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x <_4 y = True' & y <_4 z = True' --> x <_4 z = True'"

LeTTotal [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 (x <_4 y = True' | y <_4 x = True') | x ==' y = True'"

GeDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >_4 y = y <_4 x"

GeIrreflexivity [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x ==' y = True' --> x >_4 y = False'"

GeTAsymmetry [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >_4 y = True' --> y >_4 x = False'"

GeTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (x >_4 y) && (y >_4 z) = True' --> x >_4 z = True'"

GeTTotal [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). ((x >_4 y) || (y >_4 x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <=_4 y = (x <_4 y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL (x :: 'a). x <=_4 x = True'"

LeqTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 (x <=_4 y) && (y <=_4 z) = True' --> x <=_4 z = True'"

LeqTTotal [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). (x <=_4 y) && (y <=_4 x) = x ==' y"

GeqDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >=_4 y = (x >_4 y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL (x :: 'a). x >=_4 x = True'"

GeqTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 (x >=_4 y) && (y >=_4 z) = True' --> x >=_4 z = True'"

GeqTTotal [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). (x >=_4 y) && (y >=_4 x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = True' = (x <_4 y = False' & x >_4 y = False')"

EqFSOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = False' = (x <_4 y = True' | x >_4 y = True')"

EqTOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = True' = (x <=_4 y = True' & x >=_4 y = True')"

EqFOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = False' = (x <=_4 y = True' | x >=_4 y = True')"

EqTOrdTSubstE [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & y <_4 z = True' --> x <_4 z = True'"

EqTOrdFSubstE [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & y <_4 z = False' --> x <_4 z = False'"

EqTOrdTSubstD [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & z <_4 y = True' --> z <_4 x = True'"

EqTOrdFSubstD [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & z <_4 y = False' --> z <_4 x = False'"

LeTGeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <_4 y = True' = (x >_4 y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <_4 y = False' = (x >_4 y = True' | x ==' y = True')"

LeTGeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <_4 y = True' = (y >_4 x = True')"

LeFGeFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <_4 y = False' = (y >_4 x = False')"

LeqTGetTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <=_4 y = True' = (y >=_4 x = True')"

LeqFGetFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <=_4 y = False' = (y >=_4 x = False')"

GeTLeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >_4 y = True' = (y <_4 x = True')"

GeFLeFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >_4 y = False' = (y <_4 x = False')"

GeqTLeqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >=_4 y = True' = (y <=_4 x = True')"

GeqFLeqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >=_4 y = False' = (y <=_4 x = False')"

LeqTGeFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <=_4 y = True' = (x >_4 y = False')"

LeqFGeTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <=_4 y = False' = (x >_4 y = True')"

GeTLeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >_4 y = True' = (x <_4 y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >_4 y = False' = (x <_4 y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >=_4 y = True' = (x <_4 y = False')"

GeqFLeTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >=_4 y = False' = (x <_4 y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <=_4 y = True' = (x <_4 y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <=_4 y = False' = (x <_4 y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >=_4 y = True' = (x >_4 y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >=_4 y = False' = (x >_4 y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <_4 y = True' = (x >=_4 y = False')"

GeTLeqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >_4 y = True' = (x <=_4 y = False')"

LeLeqDiff [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <_4 y = (x <=_4 y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' LT = x <_4 y"

CmpEQDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' GT = x >_4 y"

MaxYDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_maxX4 x y ==' y = x <=_4 y"

MaxXDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_maxX4 x y ==' x = y <=_4 x"

MinXDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_minX4 x y ==' x = x <=_4 y"

MinYDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_minX4 x y ==' y = y <=_4 x"

MaxSym [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). X_maxX4 x y ==' y = X_maxX4 y x ==' y"

MinSym [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). X_minX4 x y ==' y = X_minX4 y x ==' y"

TO1 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 (x ==' y = True' | x <_4 y = True') = (x <=_4 y = True')"

TO3 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 notH notH (x <_4 y) = True' | notH (x <_4 y) = True'"

TO4 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <_4 y = True' --> notH (x ==' y) = True'"

TO5 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 (x <_4 y = True' & y <_4 z = True') & z <_4 w = True' -->
 x <_4 w = True'"

IOO13 [rule_format] : "LT <_4 EQ = True'"

IOO14 [rule_format] : "EQ <_4 GT = True'"

IOO15 [rule_format] : "LT <_4 GT = True'"

IOO16 [rule_format] : "LT <=_4 EQ = True'"

IOO17 [rule_format] : "EQ <=_4 GT = True'"

IOO18 [rule_format] : "LT <=_4 GT = True'"

IOO19 [rule_format] : "EQ >=_4 LT = True'"

IOO20 [rule_format] : "GT >=_4 EQ = True'"

IOO21 [rule_format] : "GT >=_4 LT = True'"

IOO22 [rule_format] : "EQ >_4 LT = True'"

IOO23 [rule_format] : "GT >_4 EQ = True'"

IOO24 [rule_format] : "GT >_4 LT = True'"

IOO25 [rule_format] : "X_maxX4 LT EQ ==' EQ = True'"

IOO26 [rule_format] : "X_maxX4 EQ GT ==' GT = True'"

IOO27 [rule_format] : "X_maxX4 LT GT ==' GT = True'"

IOO28 [rule_format] : "X_minX4 LT EQ ==' LT = True'"

IOO29 [rule_format] : "X_minX4 EQ GT ==' EQ = True'"

IOO30 [rule_format] : "X_minX4 LT GT ==' LT = True'"

IOO31 [rule_format] : "compare LT LT ==' EQ = True'"

IOO32 [rule_format] : "compare EQ EQ ==' EQ = True'"

IOO33 [rule_format] : "compare GT GT ==' EQ = True'"

IBO5 [rule_format] : "False' <_4 True' = True'"

IBO6 [rule_format] : "False' >=_4 True' = False'"

IBO7 [rule_format] : "True' >=_4 False' = True'"

IBO8 [rule_format] : "True' <_4 False' = False'"

IBO9 [rule_format] : "X_maxX4 False' True' ==' True' = True'"

IBO10 [rule_format] : "X_minX4 False' True' ==' False' = True'"

IBO11 [rule_format] : "compare True' True' ==' EQ = True'"

IBO12 [rule_format] : "compare False' False' ==' EQ = True'"

IUO01 [rule_format] : "() <=_4 () = True'"

IUO02 [rule_format] : "() <_4 () = False'"

IUO03 [rule_format] : "() >=_4 () = True'"

IUO04 [rule_format] : "() >_4 () = False'"

IUO05 [rule_format] : "X_maxX4 () () ==' () = True'"

IUO06 [rule_format] : "X_minX4 () () ==' () = True'"

IUO07 [rule_format] : "compare () () ==' EQ = True'"

ga_selector_pre [rule_format] :
"ALL (XX1 :: X_Nat). pre(suc'(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL (XX1 :: X_Nat).
 ALL (Y1 :: X_Nat). suc'(XX1) = suc'(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] :
"ALL (Y1 :: X_Nat). ~ 0'' = suc'(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0''))"

X1_def_Nat [rule_format] : "1'' = suc'(0'')"

X2_def_Nat [rule_format] : "2'' = suc'(1'')"

X3_def_Nat [rule_format] : "3'' = suc'(2'')"

X4_def_Nat [rule_format] : "4'' = suc'(3'')"

X5_def_Nat [rule_format] : "5'' = suc'(4'')"

X6_def_Nat [rule_format] : "6'' = suc'(5'')"

X7_def_Nat [rule_format] : "7'' = suc'(6'')"

X8_def_Nat [rule_format] : "8'' = suc'(7'')"

X9_def_Nat [rule_format] : "9'' = suc'(8'')"

decimal_def [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m @@ X_n = (m *'' suc'(9'')) +'' X_n"

ga_comm___XPlus__ [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). x +'' y = y +'' x"

ga_assoc___XPlus__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___XPlus__ [rule_format] :
"ALL (x :: X_Nat). x +'' 0'' = x"

ga_left_unit___XPlus__ [rule_format] :
"ALL (x :: X_Nat). 0'' +'' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). x +'' (y +'' z) = y +'' (x +'' z)"

ga_comm___Xx__ [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). x *'' y = y *'' x"

ga_assoc___Xx__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx__ [rule_format] :
"ALL (x :: X_Nat). x *'' 1'' = x"

ga_left_unit___Xx__ [rule_format] :
"ALL (x :: X_Nat). 1'' *'' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). x *'' (y *'' z) = y *'' (x *'' z)"

ga_comm_min [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). min''(x, y) = min''(y, x)"

ga_assoc_min [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). min''(min''(x, y), z) = min''(x, min''(y, z))"

ga_left_comm_min [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). min''(x, min''(y, z)) = min''(y, min''(x, z))"

ga_comm_max [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Nat). max''(x, y) = max''(y, x)"

ga_assoc_max [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). max''(max''(x, y), z) = max''(x, max''(y, z))"

ga_right_unit_max [rule_format] :
"ALL (x :: X_Nat). max''(x, 0'') = x"

ga_left_unit_max [rule_format] :
"ALL (x :: X_Nat). max''(0'', x) = x"

ga_left_comm_max [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 ALL (z :: X_Nat). max''(x, max''(y, z)) = max''(y, max''(x, z))"

leq_def1_Nat [rule_format] : "ALL (X_n :: X_Nat). 0'' <='' X_n"

dvd_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 (m dvd' X_n) = (EX (k :: X_Nat). X_n = m *'' k)"

leq_def2_Nat [rule_format] :
"ALL (X_n :: X_Nat). ~ suc'(X_n) <='' 0''"

leq_def3_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). (suc'(m) <='' suc'(X_n)) = (m <='' X_n)"

geq_def_Nat [rule_format] :
"ALL (m :: X_Nat). ALL (X_n :: X_Nat). (m >='' X_n) = (X_n <='' m)"

less_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). (m <'' X_n) = (m <='' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL (m :: X_Nat). ALL (X_n :: X_Nat). (m >'' X_n) = (X_n <'' m)"

even_0_Nat [rule_format] : "even''(0'')"

even_suc_Nat [rule_format] :
"ALL (m :: X_Nat). even''(suc'(m)) = odd''(m)"

odd_def_Nat [rule_format] :
"ALL (m :: X_Nat). odd''(m) = (~ even''(m))"

factorial_0 [rule_format] : "0'' !' = 1''"

factorial_suc [rule_format] :
"ALL (X_n :: X_Nat). suc'(X_n) !' = suc'(X_n) *'' X_n !'"

add_0_Nat [rule_format] : "ALL (m :: X_Nat). 0'' +'' m = m"

add_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). suc'(X_n) +'' m = suc'(X_n +'' m)"

mult_0_Nat [rule_format] : "ALL (m :: X_Nat). 0'' *'' m = 0''"

mult_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). suc'(X_n) *'' m = (X_n *'' m) +'' m"

power_0_Nat [rule_format] : "ALL (m :: X_Nat). m ^'' 0'' = 1''"

power_suc_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m ^'' suc'(X_n) = m *'' (m ^'' X_n)"

min_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 min''(m, X_n) = (if m <='' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 max''(m, X_n) = (if m <='' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). m >'' X_n --> X_n -! m = 0''"

subTotal_def2_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 m <='' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m -? X_n) = (m >='' X_n)"

sub_def_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat). m -? X_n = makePartial r = (m = r +'' X_n)"

divide_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 defOp (m /?'' X_n) = (~ X_n = 0'' & m mod'' X_n = makePartial 0'')"

divide_0_Nat [rule_format] :
"ALL (m :: X_Nat). ~ defOp (m /?'' 0'')"

divide_Pos_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat).
 X_n >'' 0'' --> m /?'' X_n = makePartial r = (m = r *'' X_n)"

div_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m div'' X_n) = (~ X_n = 0'')"

div_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (r :: X_Nat).
 m div'' X_n = makePartial r =
 (EX (s :: X_Nat). m = (X_n *'' r) +'' s & s <'' X_n)"

mod_dom_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat). defOp (m mod'' X_n) = (~ X_n = 0'')"

mod_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ALL (s :: X_Nat).
 m mod'' X_n = makePartial s =
 (EX (r :: X_Nat). m = (X_n *'' r) +'' s & s <'' X_n)"

distr1_Nat [rule_format] :
"ALL (r :: X_Nat).
 ALL (s :: X_Nat).
 ALL (t :: X_Nat). (r +'' s) *'' t = (r *'' t) +'' (s *'' t)"

distr2_Nat [rule_format] :
"ALL (r :: X_Nat).
 ALL (s :: X_Nat).
 ALL (t :: X_Nat). t *'' (r +'' s) = (t *'' r) +'' (t *'' s)"

Pos_def [rule_format] :
"ALL (p :: X_Nat).
 defOp ((X_gn_proj :: X_Nat => Pos partial) p) = (p >'' 0'')"

X1_as_Pos_def [rule_format] : "1_3 = suc''(0'')"

min_0 [rule_format] : "ALL (m :: X_Nat). min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (X_n :: X_Nat).
 ~ X_n = 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div'' X_n) *'' X_n) +'' makeTotal (m mod'' X_n)))
 (defOp (m div'' X_n) & defOp (m mod'' X_n))"

power_Nat [rule_format] :
"ALL (m :: X_Nat).
 ALL (r :: X_Nat).
 ALL (s :: X_Nat). m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

ga_generated_Int [rule_format] :
"ALL (p_Int :: X_Int => bool).
 (ALL (x_1 :: X_Nat). ALL (x_2 :: X_Nat). p_Int (x_1 -'' x_2)) -->
 (ALL (x :: X_Int). p_Int x)"

equality_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat). a -'' b = c -'' d = (a +'' d = c +'' b)"

Nat2Int_embedding [rule_format] :
"ALL (a :: X_Nat). (X_gn_inj :: X_Nat => X_Int) a = a -'' 0''"

ga_comm___XPlus___80 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x +' y = y +' x"

ga_assoc___XPlus___76 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus___90 [rule_format] :
"ALL (x :: X_Int). x +' (X_gn_inj :: X_Nat => X_Int) 0'' = x"

ga_left_unit___XPlus___88 [rule_format] :
"ALL (x :: X_Int). (X_gn_inj :: X_Nat => X_Int) 0'' +' x = x"

ga_left_comm___XPlus___84 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx___79 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x *' y = y *' x"

ga_assoc___Xx___75 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___89 [rule_format] :
"ALL (x :: X_Int). x *' (X_gn_inj :: Pos => X_Int) 1_3 = x"

ga_left_unit___Xx___87 [rule_format] :
"ALL (x :: X_Int). (X_gn_inj :: Pos => X_Int) 1_3 *' x = x"

ga_left_comm___Xx___83 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int). ALL (z :: X_Int). x *' (y *' z) = y *' (x *' z)"

ga_comm_min_82 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). min'(x, y) = min'(y, x)"

ga_comm_max_81 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). max'(x, y) = max'(y, x)"

ga_assoc_min_78 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_assoc_max_77 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_left_comm_min_86 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_left_comm_max_85 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 ALL (z :: X_Int). max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 (m <=' X_n) =
 defOp ((X_gn_proj :: X_Int => X_Nat partial) (X_n -' m))"

geq_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). (m >=' X_n) = (X_n <=' m)"

less_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). (m >' X_n) = (X_n <' m)"

even_def_Int [rule_format] :
"ALL (m :: X_Int). even'(m) = even''(abs'(m))"

odd_def_Int [rule_format] :
"ALL (m :: X_Int). odd'(m) = (~ even'(m))"

odd_alt_Int [rule_format] :
"ALL (m :: X_Int). odd'(m) = odd''(abs'(m))"

neg_def_Int [rule_format] :
"ALL (a :: X_Nat). ALL (b :: X_Nat). -' (a -'' b) = b -'' a"

sign_def_Int [rule_format] :
"ALL (m :: X_Int).
 sign(m) =
 (if m = (X_gn_inj :: X_Nat => X_Int) 0''
     then (X_gn_inj :: X_Nat => X_Int) 0''
     else if m >' (X_gn_inj :: X_Nat => X_Int) 0''
             then (X_gn_inj :: Pos => X_Int) 1_3
             else -' (X_gn_inj :: Pos => X_Int) 1_3)"

abs_def_Int [rule_format] :
"ALL (m :: X_Int).
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) =
 (if m <' (X_gn_inj :: X_Nat => X_Int) 0'' then -' m else m)"

add_def_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat). (a -'' b) +' (c -'' d) = (a +'' c) -'' (b +'' d)"

mult_def_Int [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 ALL (c :: X_Nat).
 ALL (d :: X_Nat).
 (a -'' b) *' (c -'' d) =
 ((a *'' c) +'' (b *'' d)) -'' ((b *'' c) +'' (a *'' d))"

sub_def_Int [rule_format] :
"ALL (m :: X_Int). ALL (X_n :: X_Int). m -' X_n = m +' -' X_n"

min_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int). max'(m, X_n) = (if m <=' X_n then X_n else m)"

power_neg1_Int [rule_format] :
"ALL (a :: X_Nat).
 -' (X_gn_inj :: Pos => X_Int) 1_3 ^' a =
 (if even''(a) then (X_gn_inj :: Pos => X_Int) 1_3
     else -' (X_gn_inj :: Pos => X_Int) 1_3)"

power_others_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (a :: X_Nat).
 ~ m = -' (X_gn_inj :: Pos => X_Int) 1_3 -->
 m ^' a =
 (sign(m) ^' a) *' (X_gn_inj :: X_Nat => X_Int) (abs'(m) ^'' a)"

divide_dom2_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m /?' X_n) = (m mod' X_n = makePartial 0'')"

divide_alt_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m /?' X_n = makePartial r =
 (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' & X_n *' r = m)"

divide_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 m /?' X_n =
 restrictOp
 (makePartial
  ((sign(m) *' sign(X_n)) *'
   (X_gn_inj :: X_Nat => X_Int) (makeTotal (abs'(m) /?'' abs'(X_n)))))
 (defOp (abs'(m) /?'' abs'(X_n)))"

div_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m div' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

div_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m div' X_n = makePartial r =
 (EX (a :: X_Nat).
  m = (X_n *' r) +' (X_gn_inj :: X_Nat => X_Int) a &
  a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m quot' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

quot_neg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m <' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m quot' X_n = makePartial r =
 (EX (s :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' >=' s &
  s >' -' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

quot_nonneg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (r :: X_Int).
 m >=' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m quot' X_n = makePartial r =
 (EX (s :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' <=' s &
  s <' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

rem_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m rem' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

rem_neg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (s :: X_Int).
 m <' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m rem' X_n = makePartial s =
 (EX (r :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' >=' s &
  s >' -' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

rem_nonneg_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (s :: X_Int).
 m >=' (X_gn_inj :: X_Nat => X_Int) 0'' -->
 m rem' X_n = makePartial s =
 (EX (r :: X_Int).
  m = (X_n *' r) +' s &
  (X_gn_inj :: X_Nat => X_Int) 0'' <=' s &
  s <' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n)))"

mod_dom_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 defOp (m mod' X_n) = (~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'')"

mod_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ALL (a :: X_Nat).
 m mod' X_n = makePartial a =
 (EX (r :: X_Int).
  m = (X_n *' r) +' (X_gn_inj :: X_Nat => X_Int) a &
  a <'' abs'(X_n))"

distr1_Int [rule_format] :
"ALL (r :: X_Int).
 ALL (s :: X_Int).
 ALL (t :: X_Int). (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Int [rule_format] :
"ALL (r :: X_Int).
 ALL (s :: X_Int).
 ALL (t :: X_Int). t *' (r +' s) = (t *' r) +' (t *' s)"

Int_Nat_sub_compat [rule_format] :
"ALL (a :: X_Nat).
 ALL (b :: X_Nat).
 defOp (a -? b) -->
 restrictOp
 (makePartial ((X_gn_inj :: X_Nat => X_Int) (makeTotal (a -? b))))
 (defOp (a -? b)) =
 makePartial (a -'' b)"

abs_decomp_Int [rule_format] :
"ALL (m :: X_Int).
 m = sign(m) *' (X_gn_inj :: X_Nat => X_Int) (abs'(m))"

mod_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 m mod' X_n = m mod' (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

div_mod_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div' X_n) *' X_n) +'
   (X_gn_inj :: X_Nat => X_Int) (makeTotal (m mod' X_n))))
 (defOp (m div' X_n) & defOp (m mod' X_n))"

quot_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 restrictOp
 (makePartial
  ((X_gn_inj :: X_Nat => X_Int) (abs'(makeTotal (m quot' X_n)))))
 (defOp (m quot' X_n)) =
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) quot'
 (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

rem_abs_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 restrictOp
 (makePartial
  ((X_gn_inj :: X_Nat => X_Int) (abs'(makeTotal (m rem' X_n)))))
 (defOp (m rem' X_n)) =
 (X_gn_inj :: X_Nat => X_Int) (abs'(m)) rem'
 (X_gn_inj :: X_Nat => X_Int) (abs'(X_n))"

quot_rem_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (X_n :: X_Int).
 ~ X_n = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m quot' X_n) *' X_n) +' makeTotal (m rem' X_n)))
 (defOp (m quot' X_n) & defOp (m rem' X_n))"

power_Int [rule_format] :
"ALL (m :: X_Int).
 ALL (a :: X_Nat).
 ALL (b :: X_Nat). m ^' (a +'' b) = (m ^' a) *' (m ^' b)"

ga_generated_Rat [rule_format] :
"ALL (p_Rat :: Rat => bool).
 (ALL (x_1 :: X_Int). ALL (x_2 :: Pos). p_Rat (x_1 /' x_2)) -->
 (ALL (x :: Rat). p_Rat x)"

equality_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 i /' p = j /' q =
 (i *' (X_gn_inj :: Pos => X_Int) q =
  j *' (X_gn_inj :: Pos => X_Int) p)"

Int2Rat_embedding [rule_format] :
"ALL (i :: X_Int). (X_gn_inj :: X_Int => Rat) i = i /' 1_3"

ga_comm___XPlus___139 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x +_5 y = y +_5 x"

ga_assoc___XPlus___135 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). (x +_5 y) +_5 z = x +_5 (y +_5 z)"

ga_right_unit___XPlus___149 [rule_format] :
"ALL (x :: Rat). x +_5 (X_gn_inj :: X_Nat => Rat) 0'' = x"

ga_left_unit___XPlus___147 [rule_format] :
"ALL (x :: Rat). (X_gn_inj :: X_Nat => Rat) 0'' +_5 x = x"

ga_left_comm___XPlus___143 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). x +_5 (y +_5 z) = y +_5 (x +_5 z)"

ga_comm___Xx___138 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x *_4 y = y *_4 x"

ga_assoc___Xx___134 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). (x *_4 y) *_4 z = x *_4 (y *_4 z)"

ga_right_unit___Xx___148 [rule_format] :
"ALL (x :: Rat). x *_4 (X_gn_inj :: Pos => Rat) 1_3 = x"

ga_left_unit___Xx___146 [rule_format] :
"ALL (x :: Rat). (X_gn_inj :: Pos => Rat) 1_3 *_4 x = x"

ga_left_comm___Xx___142 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). ALL (z :: Rat). x *_4 (y *_4 z) = y *_4 (x *_4 z)"

ga_comm_min_141 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). min_3(x, y) = min_3(y, x)"

ga_comm_max_140 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). max_3(x, y) = max_3(y, x)"

ga_assoc_min_137 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). min_3(min_3(x, y), z) = min_3(x, min_3(y, z))"

ga_assoc_max_136 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). max_3(max_3(x, y), z) = max_3(x, max_3(y, z))"

ga_left_comm_min_145 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). min_3(x, min_3(y, z)) = min_3(y, min_3(x, z))"

ga_left_comm_max_144 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). max_3(x, max_3(y, z)) = max_3(y, max_3(x, z))"

leq_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int).
 (i /' p <=_3 j /' q) =
 (i *' (X_gn_inj :: Pos => X_Int) q <='
  j *' (X_gn_inj :: Pos => X_Int) p)"

geq_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x >=_3 y) = (y <=_3 x)"

less_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x <_3 y) = (x <=_3 y & ~ x = y)"

greater_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). (x >_3 y) = (y <_3 x)"

minus_def_Rat [rule_format] :
"ALL (p :: Pos). ALL (i :: X_Int). -'' (i /' p) = -' i /' p"

abs_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (i :: X_Int).
 abs''(i /' p) = (X_gn_inj :: X_Nat => X_Int) (abs'(i)) /' p"

add_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int).
 (i /' p) +_5 (j /' q) =
 ((i *' (X_gn_inj :: Pos => X_Int) q) +'
  (j *' (X_gn_inj :: Pos => X_Int) p))
 /' (p *_3 q)"

sub_def_Rat [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x -_3 y = x +_5 -'' y"

mult_def_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (q :: Pos).
 ALL (i :: X_Int).
 ALL (j :: X_Int). (i /' p) *_4 (j /' q) = (i *' j) /' (p *_3 q)"

min_def_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). min_3(x, y) = (if x <=_3 y then x else y)"

max_def_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). max_3(x, y) = (if x <=_3 y then y else x)"

divide_def1_Rat [rule_format] :
"ALL (x :: Rat). ~ defOp (x /'' (X_gn_inj :: X_Nat => Rat) 0'')"

divide_def2_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat).
 ~ y = (X_gn_inj :: X_Nat => Rat) 0'' -->
 x /'' y = makePartial z = (x = z *_4 y)"

power_0_Rat [rule_format] :
"ALL (x :: Rat).
 x ^_3 (X_gn_inj :: X_Nat => X_Int) 0'' =
 makePartial ((X_gn_inj :: Pos => Rat) 1_3)"

power_suc_Rat [rule_format] :
"ALL (X_n :: X_Nat).
 ALL (x :: Rat).
 x ^_3 (X_gn_inj :: Pos => X_Int) (suc''(X_n)) =
 restrictOp
 (makePartial
  (x *_4 makeTotal (x ^_3 (X_gn_inj :: X_Nat => X_Int) X_n)))
 (defOp (x ^_3 (X_gn_inj :: X_Nat => X_Int) X_n))"

power_neg_Rat [rule_format] :
"ALL (p :: Pos).
 ALL (x :: Rat).
 x ^_3 -' (X_gn_inj :: Pos => X_Int) p =
 restrictOp
 ((X_gn_inj :: Pos => Rat) 1_3 /''
  makeTotal (x ^_3 (X_gn_inj :: Pos => X_Int) p))
 (defOp (x ^_3 (X_gn_inj :: Pos => X_Int) p))"

distr1_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). (x +_5 y) *_4 z = (x *_4 z) +_5 (y *_4 z)"

distr2_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 ALL (z :: Rat). z *_4 (x +_5 y) = (z *_4 x) +_5 (z *_4 y)"

sub_rule_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 (i /' p) -_3 (j /' q) =
 ((i *' (X_gn_inj :: Pos => X_Int) q) -'
  (j *' (X_gn_inj :: Pos => X_Int) p))
 /' (p *_3 q)"

divide_dom_Rat [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat).
 defOp (x /'' y) = (~ y = (X_gn_inj :: X_Nat => Rat) 0'')"

divide_rule_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (p :: Pos).
 ALL (q :: Pos).
 ~ j = (X_gn_inj :: X_Nat => X_Int) 0'' -->
 (i /' p) /'' (j /' q) =
 (X_gn_inj :: X_Int => Rat) (i *' (X_gn_inj :: Pos => X_Int) q) /''
 (X_gn_inj :: X_Int => Rat) ((X_gn_inj :: Pos => X_Int) p *' j)"

power_Rat [rule_format] :
"ALL (i :: X_Int).
 ALL (j :: X_Int).
 ALL (x :: Rat).
 x ^_3 (i +' j) =
 restrictOp
 (makePartial (makeTotal (x ^_3 i) *_4 makeTotal (x ^_3 j)))
 (defOp (x ^_3 i) & defOp (x ^_3 j))"

IPN01 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x +' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x +'' (X_gn_inj :: Pos => X_Nat) y)"

IPN02 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x *' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x *'' (X_gn_inj :: Pos => X_Nat) y)"

IPN03 [rule_format] :
"ALL (x :: Pos).
 ALL (y :: Pos).
 (X_gn_inj :: Pos => X_Int) x -' (X_gn_inj :: Pos => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int)
 ((X_gn_inj :: Pos => X_Nat) x -! (X_gn_inj :: Pos => X_Nat) y)"

IPN04 [rule_format] :
"ALL (x :: Pos).
 (X_gn_inj :: Pos => X_Nat) (negate(x)) =
 0'' -! (X_gn_inj :: Pos => X_Nat) x"

IPN05 [rule_format] : "ALL (x :: Pos). abs_3(x) = x"

IPN06 [rule_format] : "ALL (x :: Pos). signum(x) = 1_3"

IPN07 [rule_format] :
"ALL (z :: X_Int).
 makePartial (fromInteger(z)) =
 (X_gn_proj :: X_Int => Pos partial) z"

INN01 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x +' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x +'' y)"

INN02 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x *' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x *'' y)"

INN03 [rule_format] :
"ALL (x :: X_Nat).
 ALL (y :: X_Nat).
 (X_gn_inj :: X_Nat => X_Int) x -' (X_gn_inj :: X_Nat => X_Int) y =
 (X_gn_inj :: X_Nat => X_Int) (x -! y)"

INN04 [rule_format] : "ALL (x :: X_Nat). negate(x) = 0'' -! x"

INN05 [rule_format] : "ALL (x :: X_Nat). abs_3(x) = x"

INN06 [rule_format] :
"ALL (x :: X_Nat). signum(x) = (X_gn_inj :: Pos => X_Nat) 1_3"

INN07 [rule_format] :
"ALL (z :: X_Int).
 makePartial (fromInteger(z)) =
 (X_gn_proj :: X_Int => X_Nat partial) z"

IIN01 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x +' y = x +' y"

IIN02 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x *' y = x *' y"

IIN03 [rule_format] :
"ALL (x :: X_Int). ALL (y :: X_Int). x -' y = x -' y"

IIN04 [rule_format] :
"ALL (x :: X_Int).
 negate(x) = (X_gn_inj :: X_Nat => X_Int) 0'' -' x"

IIN05 [rule_format] :
"ALL (x :: X_Int).
 x >=_4 (X_gn_inj :: X_Nat => X_Int) 0'' = True' --> abs_3(x) = x"

IIN06 [rule_format] :
"ALL (x :: X_Int).
 x <_4 (X_gn_inj :: X_Nat => X_Int) 0'' = True' -->
 abs_3(x) = negate(x)"

IIN07 [rule_format] :
"ALL (x :: X_Int).
 x >_4 (X_gn_inj :: X_Nat => X_Int) 0'' = True' -->
 signum(x) = (X_gn_inj :: Pos => X_Int) 1_3"

IIN07_1 [rule_format] :
"ALL (x :: X_Int).
 x ==' (X_gn_inj :: X_Nat => X_Int) 0'' = True' -->
 signum(x) = (X_gn_inj :: X_Nat => X_Int) 0''"

IIN08 [rule_format] :
"ALL (x :: X_Int).
 x <_4 (X_gn_inj :: X_Nat => X_Int) 0'' = True' -->
 signum(x) = -' (X_gn_inj :: Pos => X_Int) 1_3"

IIN09 [rule_format] : "ALL (x :: X_Int). fromInteger(x) = x"

IRN01 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x +_5 y = x +_5 y"

IRN02 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x *_4 y = x *_4 y"

IRN03 [rule_format] :
"ALL (x :: Rat). ALL (y :: Rat). x -_3 y = x -_3 y"

IRN04 [rule_format] :
"ALL (x :: Rat). negate(x) = (X_gn_inj :: X_Nat => Rat) 0'' -_3 x"

IRN05 [rule_format] :
"ALL (x :: Rat).
 x >=_4 (X_gn_inj :: X_Nat => Rat) 0'' = True' --> abs_3(x) = x"

IRN06 [rule_format] :
"ALL (x :: Rat).
 x <_4 (X_gn_inj :: X_Nat => Rat) 0'' = True' -->
 abs_3(x) = negate(x)"

IRN07 [rule_format] :
"ALL (x :: Rat).
 x >_4 (X_gn_inj :: X_Nat => Rat) 0'' = True' -->
 signum(x) = (X_gn_inj :: Pos => Rat) 1_3"

IRN07_2 [rule_format] :
"ALL (x :: Rat).
 x ==' (X_gn_inj :: X_Nat => Rat) 0'' = True' -->
 signum(x) = (X_gn_inj :: X_Nat => Rat) 0''"

IRN08 [rule_format] :
"ALL (x :: Rat).
 x <_4 (X_gn_inj :: X_Nat => Rat) 0'' = True' -->
 signum(x) =
 (X_gn_inj :: X_Int => Rat) (-' (X_gn_inj :: Pos => X_Int) 1_3)"

IRN09 [rule_format] : "ALL (z :: X_Int). fromInteger(z) = z /' 1_3"

IRI01 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (z, w) = quotRem x y --> x quot'' y = z"

IRI02 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (z, w) = quotRem x y --> x rem'' y = w"

IRI03 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (z, w) = divMod x y --> x div_3 y = z"

IRI04 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (z, w) = divMod x y --> x mod_3 y = w"

IRI05 [rule_format] :
"ALL (s :: 'a).
 ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 signum(w) = negate(signum(y)) & (z, w) = quotRem x y -->
 divMod x y =
 (z -_4 fromInteger(toInteger((X_gn_inj :: Pos => X_Nat) 1_3)),
  w +_6 s)"

IRI06 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 ~ signum(w) = negate(signum(y)) & (z, w) = quotRem x y -->
 divMod x y = (z, w)"

IRI01_3 [rule_format] :
"ALL (x :: X_Int).
 makePartial ((X_gn_inj :: X_Int => Rat) (recip(x))) =
 (X_gn_inj :: Pos => Rat) 1_3 /'' (X_gn_inj :: X_Int => Rat) x"

IRI02_4 [rule_format] :
"ALL (x :: X_Int).
 ALL (y :: X_Int).
 (X_gn_inj :: X_Int => Rat) x /'' (X_gn_inj :: X_Int => Rat) y =
 makePartial ((X_gn_inj :: X_Int => Rat) (x *' recip(y)))"

IRF01 [rule_format] :
"ALL (x :: Rat).
 makePartial (recip(x)) = (X_gn_inj :: Pos => Rat) 1_3 /'' x"

IRF02 [rule_format] :
"ALL (x :: Rat).
 ALL (y :: Rat). x /'' y = makePartial (x *_4 recip(y))"

declare ga_subt_reflexive [simp]
declare ga_subt_Int_XLt_Rat [simp]
declare ga_subt_Nat_XLt_Int [simp]
declare ga_subt_Pos_XLt_Nat [simp]
declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare EqualReflex [simp]
declare IBE1 [simp]
declare IBE2 [simp]
declare IBE3 [simp]
declare IBE4 [simp]
declare IBE5 [simp]
declare IBE6 [simp]
declare IBE7 [simp]
declare IBE8 [simp]
declare IOE01 [simp]
declare IOE02 [simp]
declare IOE03 [simp]
declare IOE04 [simp]
declare IOE05 [simp]
declare IOE06 [simp]
declare IOE07 [simp]
declare IOE08 [simp]
declare IOE09 [simp]
declare LeIrreflexivity [simp]
declare LeTAsymmetry [simp]
declare GeIrreflexivity [simp]
declare GeTAsymmetry [simp]
declare GeTTransitive [simp]
declare GeTTotal [simp]
declare LeqReflexivity [simp]
declare LeqTTransitive [simp]
declare LeqTTotal [simp]
declare GeqReflexivity [simp]
declare GeqTTransitive [simp]
declare GeqTTotal [simp]
declare CmpLTDef [simp]
declare CmpEQDef [simp]
declare CmpGTDef [simp]
declare MaxYDef [simp]
declare MaxXDef [simp]
declare MinXDef [simp]
declare MinYDef [simp]
declare TO4 [simp]
declare IOO13 [simp]
declare IOO14 [simp]
declare IOO15 [simp]
declare IOO16 [simp]
declare IOO17 [simp]
declare IOO18 [simp]
declare IOO19 [simp]
declare IOO20 [simp]
declare IOO21 [simp]
declare IOO22 [simp]
declare IOO23 [simp]
declare IOO24 [simp]
declare IOO25 [simp]
declare IOO26 [simp]
declare IOO27 [simp]
declare IOO28 [simp]
declare IOO29 [simp]
declare IOO30 [simp]
declare IOO31 [simp]
declare IOO32 [simp]
declare IOO33 [simp]
declare IBO5 [simp]
declare IBO6 [simp]
declare IBO7 [simp]
declare IBO8 [simp]
declare IBO9 [simp]
declare IBO10 [simp]
declare IBO11 [simp]
declare IBO12 [simp]
declare IUO05 [simp]
declare IUO06 [simp]
declare IUO07 [simp]
declare ga_selector_pre [simp]
declare ga_selector_undef_pre_0 [simp]
declare ga_comm___XPlus__ [simp]
declare ga_assoc___XPlus__ [simp]
declare ga_right_unit___XPlus__ [simp]
declare ga_left_unit___XPlus__ [simp]
declare ga_left_comm___XPlus__ [simp]
declare ga_comm___Xx__ [simp]
declare ga_assoc___Xx__ [simp]
declare ga_right_unit___Xx__ [simp]
declare ga_left_unit___Xx__ [simp]
declare ga_left_comm___Xx__ [simp]
declare ga_comm_min [simp]
declare ga_assoc_min [simp]
declare ga_left_comm_min [simp]
declare ga_comm_max [simp]
declare ga_assoc_max [simp]
declare ga_right_unit_max [simp]
declare ga_left_unit_max [simp]
declare ga_left_comm_max [simp]
declare leq_def1_Nat [simp]
declare dvd_def_Nat [simp]
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare geq_def_Nat [simp]
declare less_def_Nat [simp]
declare greater_def_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare odd_def_Nat [simp]
declare factorial_0 [simp]
declare factorial_suc [simp]
declare add_0_Nat [simp]
declare add_suc_Nat [simp]
declare mult_0_Nat [simp]
declare mult_suc_Nat [simp]
declare power_0_Nat [simp]
declare power_suc_Nat [simp]
declare subTotal_def1_Nat [simp]
declare subTotal_def2_Nat [simp]
declare sub_dom_Nat [simp]
declare divide_0_Nat [simp]
declare min_0 [simp]
declare ga_comm___XPlus___80 [simp]
declare ga_assoc___XPlus___76 [simp]
declare ga_right_unit___XPlus___90 [simp]
declare ga_left_unit___XPlus___88 [simp]
declare ga_left_comm___XPlus___84 [simp]
declare ga_comm___Xx___79 [simp]
declare ga_assoc___Xx___75 [simp]
declare ga_right_unit___Xx___89 [simp]
declare ga_left_unit___Xx___87 [simp]
declare ga_left_comm___Xx___83 [simp]
declare ga_comm_min_82 [simp]
declare ga_comm_max_81 [simp]
declare ga_assoc_min_78 [simp]
declare ga_assoc_max_77 [simp]
declare ga_left_comm_min_86 [simp]
declare ga_left_comm_max_85 [simp]
declare leq_def_Int [simp]
declare even_def_Int [simp]
declare odd_alt_Int [simp]
declare neg_def_Int [simp]
declare sign_def_Int [simp]
declare abs_def_Int [simp]
declare add_def_Int [simp]
declare mult_def_Int [simp]
declare sub_def_Int [simp]
declare min_def_Int [simp]
declare max_def_Int [simp]
declare power_neg1_Int [simp]
declare power_others_Int [simp]
declare divide_Int [simp]
declare div_Int [simp]
declare quot_neg_Int [simp]
declare quot_nonneg_Int [simp]
declare rem_neg_Int [simp]
declare rem_nonneg_Int [simp]
declare mod_Int [simp]
declare Int_Nat_sub_compat [simp]
declare quot_abs_Int [simp]
declare rem_abs_Int [simp]
declare ga_comm___XPlus___139 [simp]
declare ga_assoc___XPlus___135 [simp]
declare ga_right_unit___XPlus___149 [simp]
declare ga_left_unit___XPlus___147 [simp]
declare ga_left_comm___XPlus___143 [simp]
declare ga_comm___Xx___138 [simp]
declare ga_assoc___Xx___134 [simp]
declare ga_right_unit___Xx___148 [simp]
declare ga_left_unit___Xx___146 [simp]
declare ga_left_comm___Xx___142 [simp]
declare ga_comm_min_141 [simp]
declare ga_comm_max_140 [simp]
declare ga_assoc_min_137 [simp]
declare ga_assoc_max_136 [simp]
declare ga_left_comm_min_145 [simp]
declare ga_left_comm_max_144 [simp]
declare divide_def1_Rat [simp]
declare power_0_Rat [simp]
declare IPN05 [simp]
declare IPN06 [simp]
declare IPN07 [simp]
declare INN01 [simp]
declare INN02 [simp]
declare INN03 [simp]
declare INN05 [simp]
declare INN07 [simp]
declare IIN05 [simp]
declare IIN09 [simp]
declare IRN05 [simp]

theorem AbsSignumLaw : "ALL (x :: 'a). abs_3(x) *_5 signum(x) = x"
oops

setup "Header.record \"AbsSignumLaw\""

end
