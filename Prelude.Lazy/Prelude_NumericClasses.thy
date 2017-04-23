theory Prelude_NumericClasses
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
     \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
     \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
     \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"DiffSymDef\",
     \"DiffTDef\", \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\",
     \"IUE1\", \"IUE2\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\",
     \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IOE01\", \"IOE02\",
     \"IOE03\", \"IOE04\", \"IOE05\", \"IOE06\", \"IOE07\", \"IOE08\",
     \"IOE09\", \"LeIrreflexivity\", \"LeTAsymmetry\",
     \"LeTTransitive\", \"LeTTotal\", \"GeDef\", \"GeIrreflexivity\",
     \"GeTAsymmetry\", \"GeTTransitive\", \"GeTTotal\", \"LeqDef\",
     \"LeqReflexivity\", \"LeqTTransitive\", \"LeqTTotal\", \"GeqDef\",
     \"GeqReflexivity\", \"GeqTTransitive\", \"GeqTTotal\",
     \"EqTSOrdRel\", \"EqFSOrdRel\", \"EqTOrdRel\", \"EqFOrdRel\",
     \"EqTOrdTSubstE\", \"EqTOrdFSubstE\", \"EqTOrdTSubstD\",
     \"EqTOrdFSubstD\", \"LeTGeFEqFRel\", \"LeFGeTEqTRel\",
     \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\", \"LeqFGetFRel\",
     \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\", \"GeqFLeqFRel\",
     \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\", \"GeFLeTEqTRel\",
     \"GeqTLeFRel\", \"GeqFLeTRel\", \"LeqTLeTEqTRel\",
     \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\", \"GeqFGeFEqFRel\",
     \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\", \"CmpLTDef\",
     \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\", \"MinXDef\",
     \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\", \"TO3\",
     \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IUO01\", \"IUO02\",
     \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"IOO13\",
     \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\",
     \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\",
     \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\",
     \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\",
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"ga_selector_pre\",
     \"ga_injective_suc\", \"ga_disjoint_0_suc\",
     \"ga_selector_undef_pre_0\", \"X1_def_Nat\", \"X2_def_Nat\",
     \"X3_def_Nat\", \"X4_def_Nat\", \"X5_def_Nat\", \"X6_def_Nat\",
     \"X7_def_Nat\", \"X8_def_Nat\", \"X9_def_Nat\", \"decimal_def\",
     \"ga_comm___XPlus__\", \"ga_assoc___XPlus__\",
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
     \"equality_Int\", \"Nat2Int_embedding\", \"ga_comm___XPlus___1\",
     \"ga_assoc___XPlus___1\", \"ga_right_unit___XPlus___1\",
     \"ga_left_unit___XPlus___1\", \"ga_left_comm___XPlus___1\",
     \"ga_comm___Xx___1\", \"ga_assoc___Xx___1\",
     \"ga_right_unit___Xx___1\", \"ga_left_unit___Xx___1\",
     \"ga_left_comm___Xx___1\", \"ga_comm_min_1\", \"ga_comm_max_1\",
     \"ga_assoc_min_1\", \"ga_assoc_max_1\", \"ga_left_comm_min_1\",
     \"ga_left_comm_max_1\", \"leq_def_Int\", \"geq_def_Int\",
     \"less_def_Int\", \"greater_def_Int\", \"even_def_Int\",
     \"odd_def_Int\", \"odd_alt_Int\", \"neg_def_Int\",
     \"sign_def_Int\", \"abs_def_Int\", \"add_def_Int\",
     \"mult_def_Int\", \"sub_def_Int\", \"min_def_Int\",
     \"max_def_Int\", \"power_neg1_Int\", \"power_others_Int\",
     \"divide_dom2_Int\", \"divide_alt_Int\", \"divide_Int\",
     \"div_dom_Int\", \"div_Int\", \"quot_dom_Int\", \"quot_neg_Int\",
     \"quot_nonneg_Int\", \"rem_dom_Int\", \"quot_rem_Int\",
     \"rem_nonneg_Int\", \"mod_dom_Int\", \"mod_Int\", \"distr1_Int\",
     \"distr2_Int\", \"Int_Nat_sub_compat\", \"abs_decomp_Int\",
     \"mod_abs_Int\", \"div_mod_Int\", \"quot_abs_Int\",
     \"rem_abs_Int\", \"quot_rem_Int_1\", \"power_Int\",
     \"ga_generated_Rat\", \"equality_Rat\", \"Int2Rat_embedding\",
     \"ga_comm___XPlus___2_1\", \"ga_assoc___XPlus___2_1\",
     \"ga_right_unit___XPlus___2_1\", \"ga_left_unit___XPlus___2_1\",
     \"ga_left_comm___XPlus___2_1\", \"ga_comm___Xx___2_1\",
     \"ga_assoc___Xx___2_1\", \"ga_right_unit___Xx___2_1\",
     \"ga_left_unit___Xx___2_1\", \"ga_left_comm___Xx___2_1\",
     \"ga_comm_min_2_1\", \"ga_comm_max_2_1\", \"ga_assoc_min_2_1\",
     \"ga_assoc_max_2_1\", \"ga_left_comm_min_2_1\",
     \"ga_left_comm_max_2_1\", \"leq_def_Rat\", \"geq_def_Rat\",
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
     \"IRN03\", \"IRN04\", \"IRN05\", \"IRN06\", \"IRN07\", \"IRN07_1\",
     \"IRN08\", \"IRN09\", \"IRI01\", \"IRI02\", \"IRI03\", \"IRI04\",
     \"IRI05\", \"IRI06\", \"IRI01_1\", \"IRI02_1\", \"IRF01\",
     \"IRF02\", \"AbsSignumLaw\"]"

typedecl Bool
typedecl Pos
typedecl Rat
typedecl Unit
typedecl X_Int

datatype Ordering = EQ | GT | LT
datatype X_Nat = X0X2 ("0''''") | sucX1 "X_Nat" ("suc''/'(_')" [3] 999)

consts
Not__X :: "bool => bool" ("(Not''/ _)" [56] 56)
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
X__XAmpXAmp__X :: "bool => bool => bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XCaret__XX3 :: "Rat => X_Int => Rat partial" ("(_/ ^'_3/ _)" [54,54] 52)
X__XEqXEq__X :: "'a partial => 'a partial => bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "Rat => Rat => bool" ("(_/ >='_3/ _)" [44,44] 42)
X__XGtXEq__XX4 :: "'a partial => 'a partial => bool" ("(_/ >='_4/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "Rat => Rat => bool" ("(_/ >'_3/ _)" [44,44] 42)
X__XGt__XX4 :: "'a partial => 'a partial => bool" ("(_/ >'_4/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Rat => Rat => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLtXEq__XX4 :: "'a partial => 'a partial => bool" ("(_/ <='_4/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "Rat => Rat => bool" ("(_/ <'_3/ _)" [44,44] 42)
X__XLt__XX4 :: "'a partial => 'a partial => bool" ("(_/ <'_4/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Rat => Rat => Rat" ("(_/ -'_3/ _)" [54,54] 52)
X__XMinus__XX4 :: "'a partial => 'a partial => 'a partial" ("(_/ -'_4/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Pos => X_Nat => Pos" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "Rat => Rat => Rat" ("(_/ +'_5/ _)" [54,54] 52)
X__XPlus__XX6 :: "'a partial => 'a partial => 'a partial" ("(_/ +'_6/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a partial => 'a partial => bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XSlash__XX1 :: "X_Int => Pos => Rat" ("(_/ '/''/ _)" [54,54] 52)
X__XSlash__XX2 :: "Rat => Rat => Rat partial" ("(_/ '/''''/ _)" [54,54] 52)
X__XSlash__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ '/'_3/ _)" [54,54] 52)
X__XVBarXVBar__X :: "bool => bool => bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Pos => Pos => Pos" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Rat => Rat => Rat" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "'a partial => 'a partial => 'a partial" ("(_/ *'_5/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__div__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ div'_3/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__mod__XX3 :: "'a partial => 'a partial => 'a partial" ("(_/ mod'_3/ _)" [54,54] 52)
X__quot__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ quot''/ _)" [54,54] 52)
X__quot__XX2 :: "'a partial => 'a partial => 'a partial" ("(_/ quot''''/ _)" [54,54] 52)
X__rem__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ rem''/ _)" [54,54] 52)
X__rem__XX2 :: "'a partial => 'a partial => 'a partial" ("(_/ rem''''/ _)" [54,54] 52)
X_absX1 :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_absX2 :: "Rat => Rat" ("abs''''/'(_')" [3] 999)
X_absX3 :: "'a partial => 'a partial" ("abs'_3/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_fromInteger :: "X_Int => 'a partial" ("fromInteger/'(_')" [3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "Rat => Rat => Rat" ("max'_3/'(_,/ _')" [3,3] 999)
X_maxX4 :: "'a partial => 'a partial => 'a partial"
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "Rat => Rat => Rat" ("min'_3/'(_,/ _')" [3,3] 999)
X_minX4 :: "'a partial => 'a partial => 'a partial"
X_negate :: "'a partial => 'a partial" ("negate/'(_')" [3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_recip :: "'a partial => 'a partial" ("recip/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_signum :: "'a partial => 'a partial" ("signum/'(_')" [3] 999)
X_toInteger :: "'a partial => X_Int" ("toInteger/'(_')" [3] 999)
compare :: "'a partial => 'a partial => Ordering partial"
divMod :: "'a partial => 'a partial => 'a partial * 'a partial"
otherwiseH :: "bool"
quotRem :: "'a partial => 'a partial => 'a partial * 'a partial"
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)

axioms
NotFalse [rule_format] : "Not' False"

NotTrue [rule_format] : "~ Not' True"

AndFalse [rule_format] : "ALL x. ~ False && x"

AndTrue [rule_format] : "ALL x. True && x = x"

AndSym [rule_format] : "ALL x. ALL y. x && y = y && x"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH"

NotFalse1 [rule_format] : "ALL x. Not' x = (~ x)"

NotTrue1 [rule_format] : "ALL x. ~ Not' x = x"

notNot1 [rule_format] : "ALL x. (~ x) = Not' x"

notNot2 [rule_format] : "ALL x. (~ ~ x) = (~ Not' x)"

EqualTDef [rule_format] : "ALL x. ALL y. x = y --> x ==' y"

EqualSymDef [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL x. x ==' x"

EqualTransT [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & y ==' z --> x ==' z"

DiffDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

DiffSymDef [rule_format] : "ALL x. ALL y. x /= y = y /= x"

DiffTDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

DiffFDef [rule_format] : "ALL x. ALL y. (~ x /= y) = x ==' y"

TE1 [rule_format] : "ALL x. ALL y. ~ x ==' y --> ~ x = y"

TE2 [rule_format] : "ALL x. ALL y. Not' (x ==' y) = (~ x ==' y)"

TE3 [rule_format] : "ALL x. ALL y. (~ Not' (x ==' y)) = x ==' y"

TE4 [rule_format] : "ALL x. ALL y. (~ x ==' y) = (~ x ==' y)"

IUE1 [rule_format] : "makePartial () ==' makePartial ()"

IUE2 [rule_format] : "~ makePartial () /= makePartial ()"

IBE1 [rule_format] : "makePartial () ==' makePartial ()"

IBE2 [rule_format] : "undefinedOp ==' undefinedOp"

IBE3 [rule_format] : "~ undefinedOp ==' makePartial ()"

IBE4 [rule_format] : "~ makePartial () ==' undefinedOp"

IBE5 [rule_format] : "makePartial () /= undefinedOp"

IBE6 [rule_format] : "undefinedOp /= makePartial ()"

IBE7 [rule_format] : "Not' (makePartial () ==' undefinedOp)"

IBE8 [rule_format] : "~ Not' Not' (makePartial () ==' undefinedOp)"

IOE01 [rule_format] : "makePartial LT ==' makePartial LT"

IOE02 [rule_format] : "makePartial EQ ==' makePartial EQ"

IOE03 [rule_format] : "makePartial GT ==' makePartial GT"

IOE04 [rule_format] : "~ makePartial LT ==' makePartial EQ"

IOE05 [rule_format] : "~ makePartial LT ==' makePartial GT"

IOE06 [rule_format] : "~ makePartial EQ ==' makePartial GT"

IOE07 [rule_format] : "makePartial LT /= makePartial EQ"

IOE08 [rule_format] : "makePartial LT /= makePartial GT"

IOE09 [rule_format] : "makePartial EQ /= makePartial GT"

LeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y --> ~ x <_4 y"

LeTAsymmetry [rule_format] : "ALL x. ALL y. x <_4 y --> ~ y <_4 x"

LeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. x <_4 y & y <_4 z --> x <_4 z"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <_4 y | y <_4 x) | x ==' y"

GeDef [rule_format] : "ALL x. ALL y. x >_4 y = y <_4 x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y --> ~ x >_4 y"

GeTAsymmetry [rule_format] : "ALL x. ALL y. x >_4 y --> ~ y >_4 x"

GeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >_4 y) && (y >_4 z) --> x >_4 z"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >_4 y) || (y >_4 x)) || (x ==' y)"

LeqDef [rule_format] :
"ALL x. ALL y. x <=_4 y = (x <_4 y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <=_4 x"

LeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x <=_4 y) && (y <=_4 z) --> x <=_4 z"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <=_4 y) && (y <=_4 x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >=_4 y = (x >_4 y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >=_4 x"

GeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >=_4 y) && (y >=_4 z) --> x >=_4 z"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >=_4 y) && (y >=_4 x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (~ x <_4 y & ~ x >_4 y)"

EqFSOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <_4 y | x >_4 y)"

EqTOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (x <=_4 y & x >=_4 y)"

EqFOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <=_4 y | x >=_4 y)"

EqTOrdTSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & y <_4 z --> x <_4 z"

EqTOrdFSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ y <_4 z --> ~ x <_4 z"

EqTOrdTSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & z <_4 y --> z <_4 x"

EqTOrdFSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ z <_4 y --> ~ z <_4 x"

LeTGeFEqFRel [rule_format] :
"ALL x. ALL y. x <_4 y = (~ x >_4 y & ~ x ==' y)"

LeFGeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x <_4 y) = (x >_4 y | x ==' y)"

LeTGeTRel [rule_format] : "ALL x. ALL y. x <_4 y = y >_4 x"

LeFGeFRel [rule_format] : "ALL x. ALL y. (~ x <_4 y) = (~ y >_4 x)"

LeqTGetTRel [rule_format] : "ALL x. ALL y. x <=_4 y = y >=_4 x"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. (~ x <=_4 y) = (~ y >=_4 x)"

GeTLeTRel [rule_format] : "ALL x. ALL y. x >_4 y = y <_4 x"

GeFLeFRel [rule_format] : "ALL x. ALL y. (~ x >_4 y) = (~ y <_4 x)"

GeqTLeqTRel [rule_format] : "ALL x. ALL y. x >=_4 y = y <=_4 x"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. (~ x >=_4 y) = (~ y <=_4 x)"

LeqTGeFRel [rule_format] : "ALL x. ALL y. x <=_4 y = (~ x >_4 y)"

LeqFGeTRel [rule_format] : "ALL x. ALL y. (~ x <=_4 y) = x >_4 y"

GeTLeFEqFRel [rule_format] :
"ALL x. ALL y. x >_4 y = (~ x <_4 y & ~ x ==' y)"

GeFLeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x >_4 y) = (x <_4 y | x ==' y)"

GeqTLeFRel [rule_format] : "ALL x. ALL y. x >=_4 y = (~ x <_4 y)"

GeqFLeTRel [rule_format] : "ALL x. ALL y. (~ x >=_4 y) = x <_4 y"

LeqTLeTEqTRel [rule_format] :
"ALL x. ALL y. x <=_4 y = (x <_4 y | x ==' y)"

LeqFLeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x <=_4 y) = (~ x <_4 y & ~ x ==' y)"

GeqTGeTEqTRel [rule_format] :
"ALL x. ALL y. x >=_4 y = (x >_4 y | x ==' y)"

GeqFGeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x >=_4 y) = (~ x >_4 y & ~ x ==' y)"

LeTGeqFRel [rule_format] : "ALL x. ALL y. x <_4 y = (~ x >=_4 y)"

GeTLeqFRel [rule_format] : "ALL x. ALL y. x >_4 y = (~ x <=_4 y)"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <_4 y = (x <=_4 y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial LT = x <_4 y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial GT = x >_4 y"

MaxYDef [rule_format] :
"ALL x. ALL y. X_maxX4 x y ==' y = x <=_4 y"

MaxXDef [rule_format] :
"ALL x. ALL y. X_maxX4 x y ==' x = y <=_4 x"

MinXDef [rule_format] :
"ALL x. ALL y. X_minX4 x y ==' x = x <=_4 y"

MinYDef [rule_format] :
"ALL x. ALL y. X_minX4 x y ==' y = y <=_4 x"

MaxSym [rule_format] :
"ALL x. ALL y. X_maxX4 x y ==' y = X_maxX4 y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_minX4 x y ==' y = X_minX4 y x ==' y"

TO1 [rule_format] : "ALL x. ALL y. (x ==' y | x <_4 y) = x <=_4 y"

TO2 [rule_format] : "ALL x. ALL y. x ==' y --> ~ x <_4 y"

TO3 [rule_format] :
"ALL x. ALL y. Not' Not' (x <_4 y) | Not' (x <_4 y)"

TO4 [rule_format] : "ALL x. ALL y. x <_4 y --> Not' (x ==' y)"

TO5 [rule_format] :
"ALL w.
 ALL x. ALL y. ALL z. (x <_4 y & y <_4 z) & z <_4 w --> x <_4 w"

TO6 [rule_format] : "ALL x. ALL z. z <_4 x --> Not' (x <_4 z)"

TO7 [rule_format] : "ALL x. ALL y. x <_4 y = y >_4 x"

IUO01 [rule_format] : "makePartial () <=_4 makePartial ()"

IUO02 [rule_format] : "~ makePartial () <_4 makePartial ()"

IUO03 [rule_format] : "makePartial () >=_4 makePartial ()"

IUO04 [rule_format] : "~ makePartial () >_4 makePartial ()"

IUO05 [rule_format] :
"X_maxX4 (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO06 [rule_format] :
"X_minX4 (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO07 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IOO13 [rule_format] : "makePartial LT <_4 makePartial EQ"

IOO14 [rule_format] : "makePartial EQ <_4 makePartial GT"

IOO15 [rule_format] : "makePartial LT <_4 makePartial GT"

IOO16 [rule_format] : "makePartial LT <=_4 makePartial EQ"

IOO17 [rule_format] : "makePartial EQ <=_4 makePartial GT"

IOO18 [rule_format] : "makePartial LT <=_4 makePartial GT"

IOO19 [rule_format] : "makePartial EQ >=_4 makePartial LT"

IOO20 [rule_format] : "makePartial GT >=_4 makePartial EQ"

IOO21 [rule_format] : "makePartial GT >=_4 makePartial LT"

IOO22 [rule_format] : "makePartial EQ >_4 makePartial LT"

IOO23 [rule_format] : "makePartial GT >_4 makePartial EQ"

IOO24 [rule_format] : "makePartial GT >_4 makePartial LT"

IOO25 [rule_format] :
"X_maxX4 (makePartial LT) (makePartial EQ) ==' makePartial EQ"

IOO26 [rule_format] :
"X_maxX4 (makePartial EQ) (makePartial GT) ==' makePartial GT"

IOO27 [rule_format] :
"X_maxX4 (makePartial LT) (makePartial GT) ==' makePartial GT"

IOO28 [rule_format] :
"X_minX4 (makePartial LT) (makePartial EQ) ==' makePartial LT"

IOO29 [rule_format] :
"X_minX4 (makePartial EQ) (makePartial GT) ==' makePartial EQ"

IOO30 [rule_format] :
"X_minX4 (makePartial LT) (makePartial GT) ==' makePartial LT"

IOO31 [rule_format] :
"compare (makePartial LT) (makePartial LT) ==' makePartial EQ"

IOO32 [rule_format] :
"compare (makePartial EQ) (makePartial EQ) ==' makePartial EQ"

IOO33 [rule_format] :
"compare (makePartial GT) (makePartial GT) ==' makePartial EQ"

IBO5 [rule_format] : "undefinedOp <_4 makePartial ()"

IBO6 [rule_format] : "~ undefinedOp >=_4 makePartial ()"

IBO7 [rule_format] : "makePartial () >=_4 undefinedOp"

IBO8 [rule_format] : "~ makePartial () <_4 undefinedOp"

IBO9 [rule_format] :
"X_maxX4 undefinedOp (makePartial ()) ==' makePartial ()"

IBO10 [rule_format] :
"X_minX4 undefinedOp (makePartial ()) ==' undefinedOp"

IBO11 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IBO12 [rule_format] :
"compare undefinedOp undefinedOp ==' makePartial EQ"

ga_selector_pre [rule_format] :
"ALL XX1. pre(suc'(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc'(XX1) = suc'(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0'' = suc'(Y1)"

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
"ALL m. ALL X_n. m @@ X_n = (m *'' suc'(9'')) +'' X_n"

ga_comm___XPlus__ [rule_format] : "ALL x. ALL y. x +'' y = y +'' x"

ga_assoc___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. (x +'' y) +'' z = x +'' (y +'' z)"

ga_right_unit___XPlus__ [rule_format] : "ALL x. x +'' 0'' = x"

ga_left_unit___XPlus__ [rule_format] : "ALL x. 0'' +'' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. x +'' (y +'' z) = y +'' (x +'' z)"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x *'' y = y *'' x"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x *'' y) *'' z = x *'' (y *'' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *'' 1'' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 1'' *'' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. x *'' (y *'' z) = y *'' (x *'' z)"

ga_comm_min [rule_format] :
"ALL x. ALL y. min''(x, y) = min''(y, x)"

ga_assoc_min [rule_format] :
"ALL x.
 ALL y. ALL z. min''(min''(x, y), z) = min''(x, min''(y, z))"

ga_left_comm_min [rule_format] :
"ALL x.
 ALL y. ALL z. min''(x, min''(y, z)) = min''(y, min''(x, z))"

ga_comm_max [rule_format] :
"ALL x. ALL y. max''(x, y) = max''(y, x)"

ga_assoc_max [rule_format] :
"ALL x.
 ALL y. ALL z. max''(max''(x, y), z) = max''(x, max''(y, z))"

ga_right_unit_max [rule_format] : "ALL x. max''(x, 0'') = x"

ga_left_unit_max [rule_format] : "ALL x. max''(0'', x) = x"

ga_left_comm_max [rule_format] :
"ALL x.
 ALL y. ALL z. max''(x, max''(y, z)) = max''(y, max''(x, z))"

leq_def1_Nat [rule_format] : "ALL X_n. 0'' <='' X_n"

dvd_def_Nat [rule_format] :
"ALL m. ALL X_n. (m dvd' X_n) = (EX k. X_n = m *'' k)"

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc'(X_n) <='' 0''"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc'(m) <='' suc'(X_n)) = (m <='' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >='' X_n) = (X_n <='' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <'' X_n) = (m <='' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >'' X_n) = (X_n <'' m)"

even_0_Nat [rule_format] : "even''(0'')"

even_suc_Nat [rule_format] : "ALL m. even''(suc'(m)) = odd''(m)"

odd_def_Nat [rule_format] : "ALL m. odd''(m) = (~ even''(m))"

factorial_0 [rule_format] : "0'' !' = 1''"

factorial_suc [rule_format] :
"ALL X_n. suc'(X_n) !' = suc'(X_n) *'' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0'' +'' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) +'' m = suc'(X_n +'' m)"

mult_0_Nat [rule_format] : "ALL m. 0'' *'' m = 0''"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc'(X_n) *'' m = (X_n *'' m) +'' m"

power_0_Nat [rule_format] : "ALL m. m ^'' 0'' = 1''"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^'' suc'(X_n) = m *'' (m ^'' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min''(m, X_n) = (if m <='' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max''(m, X_n) = (if m <='' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >'' X_n --> X_n -! m = 0''"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <='' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >='' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = makePartial r = (m = r +'' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /?'' X_n) = (~ X_n = 0'' & m mod'' X_n = makePartial 0'')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /?'' 0'')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 X_n >'' 0'' --> m /?'' X_n = makePartial r = (m = r *'' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div'' X_n) = (~ X_n = 0'')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div'' X_n = makePartial r =
 (EX s. m = (X_n *'' r) +'' s & s <'' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod'' X_n) = (~ X_n = 0'')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod'' X_n = makePartial s =
 (EX r. m = (X_n *'' r) +'' s & s <'' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +'' s) *'' t = (r *'' t) +'' (s *'' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *'' (r +'' s) = (t *'' r) +'' (t *'' s)"

Pos_def [rule_format] : "ALL p. defOp (gn_proj(p)) = (p >'' 0'')"

X1_as_Pos_def [rule_format] : "1_3 = suc''(0'')"

min_0 [rule_format] : "ALL m. min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0'' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div'' X_n) *'' X_n) +'' makeTotal (m mod'' X_n)))
 (defOp (m div'' X_n) & defOp (m mod'' X_n))"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

ga_generated_Int [rule_format] :
"ALL p_Int.
 (ALL x_1. ALL x_2. p_Int (x_1 -'' x_2)) --> (ALL x. p_Int x)"

equality_Int [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a -'' b = c -'' d = (a +'' d = c +'' b)"

Nat2Int_embedding [rule_format] : "ALL a. gn_inj(a) = a -'' 0''"

ga_comm___XPlus___1 [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus___1 [rule_format] :
"ALL x. x +' gn_inj(0'') = x"

ga_left_unit___XPlus___1 [rule_format] :
"ALL x. gn_inj(0'') +' x = x"

ga_left_comm___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___1 [rule_format] :
"ALL x. x *' gn_inj(1_3) = x"

ga_left_unit___Xx___1 [rule_format] : "ALL x. gn_inj(1_3) *' x = x"

ga_left_comm___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. x *' (y *' z) = y *' (x *' z)"

ga_comm_min_1 [rule_format] :
"ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_comm_max_1 [rule_format] :
"ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_min_1 [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_assoc_max_1 [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_left_comm_min_1 [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_left_comm_max_1 [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def_Int [rule_format] :
"ALL m. ALL X_n. (m <=' X_n) = defOp (gn_proj(X_n -' m))"

geq_def_Int [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Int [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Int [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_def_Int [rule_format] : "ALL m. even'(m) = even''(abs'(m))"

odd_def_Int [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

odd_alt_Int [rule_format] : "ALL m. odd'(m) = odd''(abs'(m))"

neg_def_Int [rule_format] : "ALL a. ALL b. -' (a -'' b) = b -'' a"

sign_def_Int [rule_format] :
"ALL m.
 sign(m) =
 (if m = gn_inj(0'') then gn_inj(0'')
     else if m >' gn_inj(0'') then gn_inj(1_3) else -' gn_inj(1_3))"

abs_def_Int [rule_format] :
"ALL m. gn_inj(abs'(m)) = (if m <' gn_inj(0'') then -' m else m)"

add_def_Int [rule_format] :
"ALL a.
 ALL b.
 ALL c. ALL d. (a -'' b) +' (c -'' d) = (a +'' c) -'' (b +'' d)"

mult_def_Int [rule_format] :
"ALL a.
 ALL b.
 ALL c.
 ALL d.
 (a -'' b) *' (c -'' d) =
 ((a *'' c) +'' (b *'' d)) -'' ((b *'' c) +'' (a *'' d))"

sub_def_Int [rule_format] :
"ALL m. ALL X_n. m -' X_n = m +' -' X_n"

min_def_Int [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Int [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

power_neg1_Int [rule_format] :
"ALL a.
 -' gn_inj(1_3) ^' a =
 (if even''(a) then gn_inj(1_3) else -' gn_inj(1_3))"

power_others_Int [rule_format] :
"ALL m.
 ALL a.
 ~ m = -' gn_inj(1_3) -->
 m ^' a = (sign(m) ^' a) *' gn_inj(abs'(m) ^'' a)"

divide_dom2_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m /?' X_n) = (m mod' X_n = makePartial 0'')"

divide_alt_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m /?' X_n = makePartial r = (~ X_n = gn_inj(0'') & X_n *' r = m)"

divide_Int [rule_format] :
"ALL m.
 ALL X_n.
 m /?' X_n =
 restrictOp
 (makePartial
  ((sign(m) *' sign(X_n)) *'
   gn_inj(makeTotal (abs'(m) /?'' abs'(X_n)))))
 (defOp (abs'(m) /?'' abs'(X_n)))"

div_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = gn_inj(0''))"

div_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX a. m = (X_n *' r) +' gn_inj(a) & a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m quot' X_n) = (~ X_n = gn_inj(0''))"

quot_neg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m <' gn_inj(0'') -->
 m quot' X_n = makePartial r =
 (EX s.
  m = (X_n *' r) +' s &
  gn_inj(0'') >=' s & s >' -' gn_inj(abs'(X_n)))"

quot_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m >=' gn_inj(0'') -->
 m quot' X_n = makePartial r =
 (EX s.
  m = (X_n *' r) +' s & gn_inj(0'') <=' s & s <' gn_inj(abs'(X_n)))"

rem_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m rem' X_n) = (~ X_n = gn_inj(0''))"

quot_rem_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m <' gn_inj(0'') -->
 m rem' X_n = makePartial s =
 (EX r.
  m = (X_n *' r) +' s &
  gn_inj(0'') >=' s & s >' -' gn_inj(abs'(X_n)))"

rem_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m >=' gn_inj(0'') -->
 m rem' X_n = makePartial s =
 (EX r.
  m = (X_n *' r) +' s & gn_inj(0'') <=' s & s <' gn_inj(abs'(X_n)))"

mod_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = gn_inj(0''))"

mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL a.
 m mod' X_n = makePartial a =
 (EX r. m = (X_n *' r) +' gn_inj(a) & a <'' abs'(X_n))"

distr1_Int [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Int [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

Int_Nat_sub_compat [rule_format] :
"ALL a.
 ALL b.
 defOp (a -? b) -->
 restrictOp (makePartial (gn_inj(makeTotal (a -? b))))
 (defOp (a -? b)) =
 makePartial (a -'' b)"

abs_decomp_Int [rule_format] :
"ALL m. m = sign(m) *' gn_inj(abs'(m))"

mod_abs_Int [rule_format] :
"ALL m. ALL X_n. m mod' X_n = m mod' gn_inj(abs'(X_n))"

div_mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = gn_inj(0'') -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div' X_n) *' X_n) +'
   gn_inj(makeTotal (m mod' X_n))))
 (defOp (m div' X_n) & defOp (m mod' X_n))"

quot_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 restrictOp (makePartial (gn_inj(abs'(makeTotal (m quot' X_n)))))
 (defOp (m quot' X_n)) =
 gn_inj(abs'(m)) quot' gn_inj(abs'(X_n))"

rem_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 restrictOp (makePartial (gn_inj(abs'(makeTotal (m rem' X_n)))))
 (defOp (m rem' X_n)) =
 gn_inj(abs'(m)) rem' gn_inj(abs'(X_n))"

quot_rem_Int_1 [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = gn_inj(0'') -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m quot' X_n) *' X_n) +' makeTotal (m rem' X_n)))
 (defOp (m quot' X_n) & defOp (m rem' X_n))"

power_Int [rule_format] :
"ALL m. ALL a. ALL b. m ^' (a +'' b) = (m ^' a) *' (m ^' b)"

ga_generated_Rat [rule_format] :
"ALL p_Rat.
 (ALL x_1. ALL x_2. p_Rat (x_1 /' x_2)) --> (ALL x. p_Rat x)"

equality_Rat [rule_format] :
"ALL i.
 ALL j.
 ALL p. ALL q. i /' p = j /' q = (i *' gn_inj(q) = j *' gn_inj(p))"

Int2Rat_embedding [rule_format] : "ALL i. gn_inj(i) = i /' 1_3"

ga_comm___XPlus___2_1 [rule_format] :
"ALL x. ALL y. x +_5 y = y +_5 x"

ga_assoc___XPlus___2_1 [rule_format] :
"ALL x. ALL y. ALL z. (x +_5 y) +_5 z = x +_5 (y +_5 z)"

ga_right_unit___XPlus___2_1 [rule_format] :
"ALL x. x +_5 gn_inj(0'') = x"

ga_left_unit___XPlus___2_1 [rule_format] :
"ALL x. gn_inj(0'') +_5 x = x"

ga_left_comm___XPlus___2_1 [rule_format] :
"ALL x. ALL y. ALL z. x +_5 (y +_5 z) = y +_5 (x +_5 z)"

ga_comm___Xx___2_1 [rule_format] :
"ALL x. ALL y. x *_4 y = y *_4 x"

ga_assoc___Xx___2_1 [rule_format] :
"ALL x. ALL y. ALL z. (x *_4 y) *_4 z = x *_4 (y *_4 z)"

ga_right_unit___Xx___2_1 [rule_format] :
"ALL x. x *_4 gn_inj(1_3) = x"

ga_left_unit___Xx___2_1 [rule_format] :
"ALL x. gn_inj(1_3) *_4 x = x"

ga_left_comm___Xx___2_1 [rule_format] :
"ALL x. ALL y. ALL z. x *_4 (y *_4 z) = y *_4 (x *_4 z)"

ga_comm_min_2_1 [rule_format] :
"ALL x. ALL y. min_3(x, y) = min_3(y, x)"

ga_comm_max_2_1 [rule_format] :
"ALL x. ALL y. max_3(x, y) = max_3(y, x)"

ga_assoc_min_2_1 [rule_format] :
"ALL x.
 ALL y. ALL z. min_3(min_3(x, y), z) = min_3(x, min_3(y, z))"

ga_assoc_max_2_1 [rule_format] :
"ALL x.
 ALL y. ALL z. max_3(max_3(x, y), z) = max_3(x, max_3(y, z))"

ga_left_comm_min_2_1 [rule_format] :
"ALL x.
 ALL y. ALL z. min_3(x, min_3(y, z)) = min_3(y, min_3(x, z))"

ga_left_comm_max_2_1 [rule_format] :
"ALL x.
 ALL y. ALL z. max_3(x, max_3(y, z)) = max_3(y, max_3(x, z))"

leq_def_Rat [rule_format] :
"ALL p.
 ALL q.
 ALL i.
 ALL j. (i /' p <=_3 j /' q) = (i *' gn_inj(q) <=' j *' gn_inj(p))"

geq_def_Rat [rule_format] : "ALL x. ALL y. (x >=_3 y) = (y <=_3 x)"

less_def_Rat [rule_format] :
"ALL x. ALL y. (x <_3 y) = (x <=_3 y & ~ x = y)"

greater_def_Rat [rule_format] :
"ALL x. ALL y. (x >_3 y) = (y <_3 x)"

minus_def_Rat [rule_format] :
"ALL p. ALL i. -'' (i /' p) = -' i /' p"

abs_def_Rat [rule_format] :
"ALL p. ALL i. abs''(i /' p) = gn_inj(abs'(i)) /' p"

add_def_Rat [rule_format] :
"ALL p.
 ALL q.
 ALL i.
 ALL j.
 (i /' p) +_5 (j /' q) =
 ((i *' gn_inj(q)) +' (j *' gn_inj(p))) /' (p *_3 q)"

sub_def_Rat [rule_format] : "ALL x. ALL y. x -_3 y = x +_5 -'' y"

mult_def_Rat [rule_format] :
"ALL p.
 ALL q. ALL i. ALL j. (i /' p) *_4 (j /' q) = (i *' j) /' (p *_3 q)"

min_def_Rat [rule_format] :
"ALL x. ALL y. min_3(x, y) = (if x <=_3 y then x else y)"

max_def_Rat [rule_format] :
"ALL x. ALL y. max_3(x, y) = (if x <=_3 y then y else x)"

divide_def1_Rat [rule_format] :
"ALL x. ~ defOp (x /'' gn_inj(0''))"

divide_def2_Rat [rule_format] :
"ALL x.
 ALL y.
 ALL z.
 ~ y = gn_inj(0'') --> x /'' y = makePartial z = (x = z *_4 y)"

power_0_Rat [rule_format] :
"ALL x. x ^_3 gn_inj(0'') = makePartial (gn_inj(1_3))"

power_suc_Rat [rule_format] :
"ALL X_n.
 ALL x.
 x ^_3 gn_inj(suc''(X_n)) =
 restrictOp (makePartial (x *_4 makeTotal (x ^_3 gn_inj(X_n))))
 (defOp (x ^_3 gn_inj(X_n)))"

power_neg_Rat [rule_format] :
"ALL p.
 ALL x.
 x ^_3 -' gn_inj(p) =
 restrictOp (gn_inj(1_3) /'' makeTotal (x ^_3 gn_inj(p)))
 (defOp (x ^_3 gn_inj(p)))"

distr1_Rat [rule_format] :
"ALL x. ALL y. ALL z. (x +_5 y) *_4 z = (x *_4 z) +_5 (y *_4 z)"

distr2_Rat [rule_format] :
"ALL x. ALL y. ALL z. z *_4 (x +_5 y) = (z *_4 x) +_5 (z *_4 y)"

sub_rule_Rat [rule_format] :
"ALL i.
 ALL j.
 ALL p.
 ALL q.
 (i /' p) -_3 (j /' q) =
 ((i *' gn_inj(q)) -' (j *' gn_inj(p))) /' (p *_3 q)"

divide_dom_Rat [rule_format] :
"ALL x. ALL y. defOp (x /'' y) = (~ y = gn_inj(0''))"

divide_rule_Rat [rule_format] :
"ALL i.
 ALL j.
 ALL p.
 ALL q.
 ~ j = gn_inj(0'') -->
 (i /' p) /'' (j /' q) =
 gn_inj(i *' gn_inj(q)) /'' gn_inj(gn_inj(p) *' j)"

power_Rat [rule_format] :
"ALL i.
 ALL j.
 ALL x.
 x ^_3 (i +' j) =
 restrictOp
 (makePartial (makeTotal (x ^_3 i) *_4 makeTotal (x ^_3 j)))
 (defOp (x ^_3 i) & defOp (x ^_3 j))"

IPN01 [rule_format] :
"ALL x.
 ALL y.
 makePartial (gn_inj(x) +' gn_inj(y)) =
 gn_inj(gn_inj(x) +'' gn_inj(y))"

IPN02 [rule_format] :
"ALL x.
 ALL y.
 makePartial (gn_inj(x) *' gn_inj(y)) =
 gn_inj(gn_inj(x) *'' gn_inj(y))"

IPN03 [rule_format] :
"ALL x.
 ALL y.
 makePartial (gn_inj(x) -' gn_inj(y)) =
 gn_inj(gn_inj(x) -! gn_inj(y))"

IPN04 [rule_format] :
"ALL x.
 gn_inj(negate(makePartial x)) = makePartial (0'' -! gn_inj(x))"

IPN05 [rule_format] : "ALL x. abs_3(makePartial x) = makePartial x"

IPN06 [rule_format] :
"ALL x. signum(makePartial x) = makePartial 1_3"

IPN07 [rule_format] : "ALL z. fromInteger(z) = gn_proj(z)"

INN01 [rule_format] :
"ALL x.
 ALL y. makePartial (gn_inj(x) +' gn_inj(y)) = gn_inj(x +'' y)"

INN02 [rule_format] :
"ALL x.
 ALL y. makePartial (gn_inj(x) *' gn_inj(y)) = gn_inj(x *'' y)"

INN03 [rule_format] :
"ALL x.
 ALL y. makePartial (gn_inj(x) -' gn_inj(y)) = gn_inj(x -! y)"

INN04 [rule_format] :
"ALL x. negate(makePartial x) = makePartial (0'' -! x)"

INN05 [rule_format] : "ALL x. abs_3(makePartial x) = makePartial x"

INN06 [rule_format] : "ALL x. signum(makePartial x) = gn_inj(1_3)"

INN07 [rule_format] : "ALL z. fromInteger(z) = gn_proj(z)"

IIN01 [rule_format] : "ALL x. ALL y. x +' y = x +' y"

IIN02 [rule_format] : "ALL x. ALL y. x *' y = x *' y"

IIN03 [rule_format] : "ALL x. ALL y. x -' y = x -' y"

IIN04 [rule_format] :
"ALL x. negate(makePartial x) = makePartial (gn_inj(0'') -' x)"

IIN05 [rule_format] :
"ALL x.
 gn_inj(x) >=_3 gn_inj(0'') -->
 abs_3(makePartial x) = makePartial x"

IIN06 [rule_format] :
"ALL x.
 gn_inj(x) <_3 gn_inj(0'') -->
 abs_3(makePartial x) = negate(makePartial x)"

IIN07 [rule_format] :
"ALL x.
 gn_inj(x) >_3 gn_inj(0'') --> signum(makePartial x) = gn_inj(1_3)"

IIN07_1 [rule_format] :
"ALL x.
 makePartial x ==' gn_inj(0'') -->
 signum(makePartial x) = gn_inj(0'')"

IIN08 [rule_format] :
"ALL x.
 gn_inj(x) <_3 gn_inj(0'') -->
 signum(makePartial x) = makePartial (-' gn_inj(1_3))"

IIN09 [rule_format] : "ALL x. fromInteger(x) = makePartial x"

IRN01 [rule_format] : "ALL x. ALL y. x +_5 y = x +_5 y"

IRN02 [rule_format] : "ALL x. ALL y. x *_4 y = x *_4 y"

IRN03 [rule_format] : "ALL x. ALL y. x -_3 y = x -_3 y"

IRN04 [rule_format] :
"ALL x. negate(makePartial x) = makePartial (gn_inj(0'') -_3 x)"

IRN05 [rule_format] :
"ALL x.
 x >=_3 gn_inj(0'') --> abs_3(makePartial x) = makePartial x"

IRN06 [rule_format] :
"ALL x.
 x <_3 gn_inj(0'') --> abs_3(makePartial x) = negate(makePartial x)"

IRN07 [rule_format] :
"ALL x. x >_3 gn_inj(0'') --> signum(makePartial x) = gn_inj(1_3)"

IRN07_1 [rule_format] :
"ALL x.
 makePartial x ==' gn_inj(0'') -->
 signum(makePartial x) = gn_inj(0'')"

IRN08 [rule_format] :
"ALL x.
 x <_3 gn_inj(0'') -->
 signum(makePartial x) = gn_inj(-' gn_inj(1_3))"

IRN09 [rule_format] :
"ALL z. fromInteger(z) = makePartial (z /' 1_3)"

IRI01 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (quotRem x y))) -->
 x quot'' y = z"

IRI02 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (quotRem x y))) -->
 x rem'' y = w"

IRI03 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (divMod x y))) -->
 x div_3 y = z"

IRI04 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (divMod x y))) -->
 x mod_3 y = w"

IRI05 [rule_format] :
"ALL s.
 ALL w.
 ALL x.
 ALL y.
 ALL z.
 signum(w) = negate(signum(y)) &
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (quotRem x y))) -->
 makePartial (mapSnd makeTotal (mapFst makeTotal (divMod x y))) =
 restrictOp
 (makePartial
  (makeTotal
   (z -_4 fromInteger(toInteger(makePartial (gn_inj(1_3))))),
   makeTotal (w +_6 s)))
 (defOp (z -_4 fromInteger(toInteger(makePartial (gn_inj(1_3))))) &
  defOp (w +_6 s))"

IRI06 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 ~ signum(w) = negate(signum(y)) &
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w) =
 makePartial (mapSnd makeTotal (mapFst makeTotal (quotRem x y))) -->
 makePartial (mapSnd makeTotal (mapFst makeTotal (divMod x y))) =
 restrictOp (makePartial (makeTotal z, makeTotal w))
 (defOp z & defOp w)"

IRI01_1 [rule_format] :
"ALL x. gn_inj(recip(makePartial x)) = gn_inj(1_3) /'' gn_inj(x)"

IRI02_1 [rule_format] :
"ALL x.
 ALL y.
 gn_inj(x) /'' gn_inj(y) =
 restrictOp (gn_inj(x *' makeTotal (recip(makePartial y))))
 (defOp (recip(makePartial y)))"

IRF01 [rule_format] :
"ALL x. recip(makePartial x) = gn_inj(1_3) /'' x"

IRF02 [rule_format] :
"ALL x.
 ALL y.
 x /'' y =
 restrictOp (makePartial (x *_4 makeTotal (recip(makePartial y))))
 (defOp (recip(makePartial y)))"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare OtherwiseDef [simp]
declare NotTrue1 [simp]
declare EqualReflex [simp]
declare IUE1 [simp]
declare IUE2 [simp]
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
declare TO2 [simp]
declare TO4 [simp]
declare TO6 [simp]
declare IUO01 [simp]
declare IUO02 [simp]
declare IUO03 [simp]
declare IUO04 [simp]
declare IUO05 [simp]
declare IUO06 [simp]
declare IUO07 [simp]
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
declare ga_comm___XPlus___1 [simp]
declare ga_assoc___XPlus___1 [simp]
declare ga_right_unit___XPlus___1 [simp]
declare ga_left_unit___XPlus___1 [simp]
declare ga_left_comm___XPlus___1 [simp]
declare ga_comm___Xx___1 [simp]
declare ga_assoc___Xx___1 [simp]
declare ga_right_unit___Xx___1 [simp]
declare ga_left_unit___Xx___1 [simp]
declare ga_left_comm___Xx___1 [simp]
declare ga_comm_min_1 [simp]
declare ga_comm_max_1 [simp]
declare ga_assoc_min_1 [simp]
declare ga_assoc_max_1 [simp]
declare ga_left_comm_min_1 [simp]
declare ga_left_comm_max_1 [simp]
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
declare quot_rem_Int [simp]
declare rem_nonneg_Int [simp]
declare mod_Int [simp]
declare Int_Nat_sub_compat [simp]
declare quot_abs_Int [simp]
declare rem_abs_Int [simp]
declare ga_comm___XPlus___2_1 [simp]
declare ga_assoc___XPlus___2_1 [simp]
declare ga_right_unit___XPlus___2_1 [simp]
declare ga_left_unit___XPlus___2_1 [simp]
declare ga_left_comm___XPlus___2_1 [simp]
declare ga_comm___Xx___2_1 [simp]
declare ga_assoc___Xx___2_1 [simp]
declare ga_right_unit___Xx___2_1 [simp]
declare ga_left_unit___Xx___2_1 [simp]
declare ga_left_comm___Xx___2_1 [simp]
declare ga_comm_min_2_1 [simp]
declare ga_comm_max_2_1 [simp]
declare ga_assoc_min_2_1 [simp]
declare ga_assoc_max_2_1 [simp]
declare ga_left_comm_min_2_1 [simp]
declare ga_left_comm_max_2_1 [simp]
declare divide_def1_Rat [simp]
declare power_0_Rat [simp]
declare IPN05 [simp]
declare IPN06 [simp]
declare INN01 [simp]
declare INN02 [simp]
declare INN03 [simp]
declare INN05 [simp]
declare INN06 [simp]
declare IIN05 [simp]
declare IIN07 [simp]
declare IIN07_1 [simp]
declare IRN05 [simp]
declare IRN07 [simp]
declare IRN07_1 [simp]

theorem AbsSignumLaw : "ALL x. abs_3(x) *_5 signum(x) = x"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def Pos_def
      X1_as_Pos_def
by (auto)

ML "Header.record \"AbsSignumLaw\""

end
