theory Prelude_List
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ga_selector_pre\", \"ga_injective_suc\", \"ga_disjoint_0_suc\",
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
     \"ga_left_comm_max\", \"leq_def1_Nat\", \"leq_def2_Nat\",
     \"leq_def3_Nat\", \"geq_def_Nat\", \"less_def_Nat\",
     \"greater_def_Nat\", \"even_0_Nat\", \"even_suc_Nat\",
     \"odd_def_Nat\", \"factorial_0\", \"factorial_suc\", \"add_0_Nat\",
     \"add_suc_Nat\", \"mult_0_Nat\", \"mult_suc_Nat\", \"power_0_Nat\",
     \"power_suc_Nat\", \"min_def_Nat\", \"max_def_Nat\",
     \"subTotal_def1_Nat\", \"subTotal_def2_Nat\", \"sub_dom_Nat\",
     \"sub_def_Nat\", \"divide_dom_Nat\", \"divide_0_Nat\",
     \"divide_Pos_Nat\", \"div_dom_Nat\", \"div_Nat\", \"mod_dom_Nat\",
     \"mod_Nat\", \"distr1_Nat\", \"distr2_Nat\", \"min_0\",
     \"div_mod_Nat\", \"power_Nat\", \"equality_Int\", \"NatToInt\",
     \"IntToNat\", \"ga_comm___XPlus___1\", \"ga_assoc___XPlus___1\",
     \"ga_right_unit___XPlus___1\", \"ga_left_unit___XPlus___1\",
     \"ga_left_comm___XPlus___1\", \"ga_comm___Xx___1\",
     \"ga_assoc___Xx___1\", \"ga_right_unit___Xx___1\",
     \"ga_left_unit___Xx___1\", \"ga_left_comm___Xx___1\",
     \"ga_comm_min_1\", \"ga_comm_max_1\", \"ga_assoc_min_1\",
     \"ga_assoc_max_1\", \"ga_left_comm_min_1\", \"ga_left_comm_max_1\",
     \"geq_def_Int\", \"less_def_Int\", \"greater_def_Int\",
     \"even_def_Int\", \"odd_def_Int\", \"odd_alt_Int\",
     \"neg_def_Int\", \"sign_def_Int\", \"abs_def_Int\",
     \"add_def_Int\", \"mult_def_Int\", \"sub_def_Int\",
     \"min_def_Int\", \"max_def_Int\", \"power_neg1_Int\",
     \"power_others_Int\", \"divide_dom2_Int\", \"divide_alt_Int\",
     \"divide_Int\", \"div_dom_Int\", \"div_Int\", \"quot_dom_Int\",
     \"quot_neg_Int\", \"quot_nonneg_Int\", \"rem_dom_Int\",
     \"quot_rem_Int\", \"rem_nonneg_Int\", \"mod_dom_Int\", \"mod_Int\",
     \"distr1_Int\", \"distr2_Int\", \"Int_Nat_sub_compat\",
     \"abs_decomp_Int\", \"mod_abs_Int\", \"div_mod_Int\",
     \"quot_abs_Int\", \"rem_abs_Int\", \"quot_rem_Int_1\",
     \"power_Int\", \"NotFalse\", \"NotTrue\", \"AndFalse\",
     \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
     \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\", \"Comp\",
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
     \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeTRel\", \"LeFGeFRel\",
     \"LeqTGetTRel\", \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\",
     \"GeqTLeqTRel\", \"GeqFLeqFRel\", \"LeTGeFEqFRel\",
     \"LeFGeTEqTRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
     \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
     \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
     \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
     \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
     \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\",
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IOO13\", \"IOO14\",
     \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\",
     \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\",
     \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\",
     \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\",
     \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\",
     \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"LengthNil\",
     \"LengthCons\", \"NotDefHead\", \"HeadDef\", \"NotDefTail\",
     \"TailDef\", \"FoldrNil\", \"FoldrCons\", \"FoldlNil\",
     \"FoldlCons\", \"MapNil\", \"MapCons\", \"XPlusXPlusNil\",
     \"XPlusXPlusCons\", \"FilterNil\", \"FilterConsT\",
     \"FilterConsF\", \"ZipNil\", \"ZipConsNil\", \"ZipConsCons\",
     \"UnzipNil\", \"UnzipCons\", \"FoldlDecomp\", \"MapDecomp\",
     \"MapFunctor\", \"FilterProm\", \"ZipSpec\", \"EqualListNilDef\",
     \"EqualListDef\", \"LeListDef\", \"LeListNilFalse\"]"

typedecl Unit
typedecl X_Int

datatype Nat = X0X2 ("0''''") | X_suc "Nat" ("suc/'(_')" [3] 999)
datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
IntToNat__X :: "X_Int => Nat partial" ("(IntToNat/ _)" [56] 56)
NatToInt__X :: "Nat => X_Int" ("(NatToInt/ _)" [56] 56)
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X0X1 :: "X_Int" ("0''")
X1X1 :: "X_Int" ("1''")
X1X2 :: "Nat" ("1''''")
X2X1 :: "X_Int" ("2''")
X2X2 :: "Nat" ("2''''")
X3X1 :: "X_Int" ("3''")
X3X2 :: "Nat" ("3''''")
X4X1 :: "X_Int" ("4''")
X4X2 :: "Nat" ("4''''")
X5X1 :: "X_Int" ("5''")
X5X2 :: "Nat" ("5''''")
X6X1 :: "X_Int" ("6''")
X6X2 :: "Nat" ("6''''")
X7X1 :: "X_Int" ("7''")
X7X2 :: "Nat" ("7''''")
X8X1 :: "X_Int" ("8''")
X8X2 :: "Nat" ("8''''")
X9X1 :: "X_Int" ("9''")
X9X2 :: "Nat" ("9''''")
XMinus__X :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "Nat => Nat => Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "Nat => Nat => Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "Nat => Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "Nat => Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "'a => 'a => Bool" ("(_/ >='_3/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "Nat => Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "'a => 'a => Bool" ("(_/ >'_3/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "Nat => Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "'a => 'a => Bool" ("(_/ <='_3/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "Nat => Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "'a => 'a => Bool" ("(_/ <'_3/ _)" [54,54] 52)
X__XMinusXExclam__X :: "Nat => Nat => Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "Nat => Nat => Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "Nat => Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Nat => Nat => Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "Nat => Nat => Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Nat => Nat => Nat" ("(_/ *''''/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "Nat => Nat => Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__mod__XX1 :: "X_Int => X_Int => Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "Nat => Nat => Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X__quot__X :: "X_Int => X_Int => X_Int partial" ("(_/ quot/ _)" [54,54] 52)
X__rem__X :: "X_Int => X_Int => X_Int partial" ("(_/ rem/ _)" [54,54] 52)
X_abs :: "X_Int => Nat" ("abs''/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "Nat => bool" ("even''''/'(_')" [3] 999)
X_filter :: "('a => Bool) => 'a List => 'a List" ("filter''/'(_,/ _')" [3,3] 999)
X_foldl :: "('a * 'b => 'a) => 'a => 'b List => 'a" ("foldl''/'(_,/ _,/ _')" [3,3,3] 999)
X_foldr :: "('a * 'b => 'b) => 'b => 'a List => 'b" ("foldr''/'(_,/ _,/ _')" [3,3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_length :: "'a List => X_Int" ("length''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List" ("map''/'(_,/ _')" [3,3] 999)
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "Nat => Nat => Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "'a => 'a => 'a"
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "Nat => Nat => Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "'a => 'a => 'a"
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "Nat => bool" ("odd''''/'(_')" [3] 999)
X_pre :: "Nat => Nat partial" ("pre/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List" ("zip''/'(_,/ _')" [3,3] 999)
compare :: "'a => 'a => Ordering"
otherwiseH :: "Bool"

axioms
ga_selector_pre [rule_format] :
"ALL XX1. pre(suc(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc(XX1) = suc(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0'' = suc(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0''))"

X1_def_Nat [rule_format] : "1'' = suc(0'')"

X2_def_Nat [rule_format] : "2'' = suc(1'')"

X3_def_Nat [rule_format] : "3'' = suc(2'')"

X4_def_Nat [rule_format] : "4'' = suc(3'')"

X5_def_Nat [rule_format] : "5'' = suc(4'')"

X6_def_Nat [rule_format] : "6'' = suc(5'')"

X7_def_Nat [rule_format] : "7'' = suc(6'')"

X8_def_Nat [rule_format] : "8'' = suc(7'')"

X9_def_Nat [rule_format] : "9'' = suc(8'')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *'' suc(9'')) +'' X_n"

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

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc(X_n) <='' 0''"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc(m) <='' suc(X_n)) = (m <='' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >='' X_n) = (X_n <='' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <'' X_n) = (m <='' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >'' X_n) = (X_n <'' m)"

even_0_Nat [rule_format] : "even''(0'')"

even_suc_Nat [rule_format] : "ALL m. even''(suc(m)) = odd''(m)"

odd_def_Nat [rule_format] : "ALL m. odd''(m) = (~ even''(m))"

factorial_0 [rule_format] : "0'' !' = 1''"

factorial_suc [rule_format] :
"ALL X_n. suc(X_n) !' = suc(X_n) *'' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0'' +'' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) +'' m = suc(X_n +'' m)"

mult_0_Nat [rule_format] : "ALL m. 0'' *'' m = 0''"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) *'' m = (X_n *'' m) +'' m"

power_0_Nat [rule_format] : "ALL m. m ^'' 0'' = 1''"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^'' suc(X_n) = m *'' (m ^'' X_n)"

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

min_0 [rule_format] : "ALL m. min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0'' -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m div'' X_n
      in if Xb4 then makePartial (Xc3 *'' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m mod'' X_n
             in if Xb2 then makePartial (Xc0 +'' Xc1) else noneOp
        else noneOp)"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

equality_Int [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a -'' b = c -'' d = (a +'' d = c +'' b)"

NatToInt [rule_format] : "ALL a. NatToInt a = a -'' 0''"

IntToNat [rule_format] :
"ALL a. ALL b. IntToNat (a -'' b) = makePartial (a -! b)"

ga_comm___XPlus___1 [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus___1 [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___XPlus___1 [rule_format] : "ALL x. 0' +' x = x"

ga_left_comm___XPlus___1 [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx___1 [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx___1 [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx___1 [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx___1 [rule_format] : "ALL x. 1' *' x = x"

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
 sign(m) = (if m = 0' then 0' else if m >' 0' then 1' else -' 1')"

abs_def_Int [rule_format] :
"ALL m.
 makePartial (abs'(m)) =
 (if m <' 0' then IntToNat -' m else IntToNat m)"

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
"ALL a. -' 1' ^' a = (if even''(a) then 1' else -' 1')"

power_others_Int [rule_format] :
"ALL m.
 ALL a.
 ~ m = -' 1' --> m ^' a = (sign(m) ^' a) *' (NatToInt abs'(m) ^' a)"

divide_dom2_Int [rule_format] :
"ALL m.
 ALL X_n. defOp (m /?' X_n) = (m mod' X_n = makePartial 0'')"

divide_alt_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r. m /?' X_n = makePartial r = (~ X_n = 0' & X_n *' r = m)"

divide_Int [rule_format] :
"ALL m.
 ALL X_n.
 m /?' X_n =
 (let (Xb1, Xc0) = NatToInt abs'(m) /?' NatToInt abs'(X_n)
  in if Xb1 then makePartial ((sign(m) *' sign(X_n)) *' Xc0)
        else noneOp)"

div_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX a. m = (X_n *' r) +' NatToInt a & a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m quot X_n) = (~ X_n = 0')"

quot_neg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m <' 0' -->
 m quot X_n = makePartial r =
 (EX s.
  m = (X_n *' r) +' s & 0' >=' s & s >' -' NatToInt abs'(X_n))"

quot_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m >=' 0' -->
 m quot X_n = makePartial r =
 (EX s. m = (X_n *' r) +' s & 0' <=' s & s <' NatToInt abs'(X_n))"

rem_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m rem X_n) = (~ X_n = 0')"

quot_rem_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m <' 0' -->
 m rem X_n = makePartial s =
 (EX r.
  m = (X_n *' r) +' s & 0' >=' s & s >' -' NatToInt abs'(X_n))"

rem_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m >=' 0' -->
 m rem X_n = makePartial s =
 (EX r. m = (X_n *' r) +' s & 0' <=' s & s <' NatToInt abs'(X_n))"

mod_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL a.
 m mod' X_n = makePartial a =
 (EX r. m = (X_n *' r) +' NatToInt a & a <'' abs'(X_n))"

distr1_Int [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Int [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

Int_Nat_sub_compat [rule_format] :
"ALL a. ALL b. defOp (a -? b) --> a -? b = IntToNat (a -'' b)"

abs_decomp_Int [rule_format] :
"ALL m. m = sign(m) *' NatToInt abs'(m)"

mod_abs_Int [rule_format] :
"ALL m. ALL X_n. m mod' X_n = m mod' NatToInt abs'(X_n)"

div_mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 (let (Xb7, Xc0) =
      let (Xb6, Xc5) = m div' X_n
      in if Xb6 then makePartial (Xc5 *' X_n) else noneOp
  in if Xb7
        then let (Xb4, Xc1) =
                 let (Xb3, Xc2) = m mod' X_n
                 in if Xb3 then makePartial (NatToInt Xc2) else noneOp
             in if Xb4 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

quot_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = m quot X_n
      in if Xb2 then makePartial (abs'(Xc1)) else noneOp
  in if Xb3 then makePartial (NatToInt Xc0) else noneOp) =
 NatToInt abs'(m) quot NatToInt abs'(X_n)"

rem_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (let (Xb3, Xc0) =
      let (Xb2, Xc1) = m rem X_n
      in if Xb2 then makePartial (abs'(Xc1)) else noneOp
  in if Xb3 then makePartial (NatToInt Xc0) else noneOp) =
 NatToInt abs'(m) rem NatToInt abs'(X_n)"

quot_rem_Int_1 [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 (let (Xb5, Xc0) =
      let (Xb4, Xc3) = m quot X_n
      in if Xb4 then makePartial (Xc3 *' X_n) else noneOp
  in if Xb5
        then let (Xb2, Xc1) = m rem X_n
             in if Xb2 then makePartial (Xc0 +' Xc1) else noneOp
        else noneOp)"

power_Int [rule_format] :
"ALL m. ALL a. ALL b. m ^' (a +'' b) = (m ^' a) *' (m ^' b)"

NotFalse [rule_format] : "Not' False' = True'"

NotTrue [rule_format] : "Not' True' = False'"

AndFalse [rule_format] : "ALL x. False' && x = False'"

AndTrue [rule_format] : "ALL x. True' && x = x"

AndSym [rule_format] : "ALL x. ALL y. x && y = y && x"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

NotFalse1 [rule_format] : "ALL x. Not' x = True' = (x = False')"

NotTrue1 [rule_format] : "ALL x. Not' x = False' = (x = True')"

notNot1 [rule_format] : "ALL x. (~ x = True') = (Not' x = True')"

notNot2 [rule_format] : "ALL x. (~ x = False') = (Not' x = False')"

Comp [rule_format] :
"ALL f.
 ALL g. makePartial o X__o__X (f, g) = makePartial o (% x. f (g x))"

EqualTDef [rule_format] : "ALL x. ALL y. x = y --> x ==' y = True'"

EqualSymDef [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL x. x ==' x = True'"

EqualTransT [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y ==' z = True' --> x ==' z = True'"

DiffDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

DiffSymDef [rule_format] : "ALL x. ALL y. x /= y = y /= x"

DiffTDef [rule_format] :
"ALL x. ALL y. x /= y = True' = (Not' (x ==' y) = True')"

DiffFDef [rule_format] :
"ALL x. ALL y. x /= y = False' = (x ==' y = True')"

TE1 [rule_format] : "ALL x. ALL y. x ==' y = False' --> ~ x = y"

TE2 [rule_format] :
"ALL x. ALL y. Not' (x ==' y) = True' = (x ==' y = False')"

TE3 [rule_format] :
"ALL x. ALL y. Not' (x ==' y) = False' = (x ==' y = True')"

TE4 [rule_format] :
"ALL x. ALL y. (~ x ==' y = True') = (x ==' y = False')"

IBE1 [rule_format] : "True' ==' True' = True'"

IBE2 [rule_format] : "False' ==' False' = True'"

IBE3 [rule_format] : "False' ==' True' = False'"

IBE4 [rule_format] : "True' ==' False' = False'"

IBE5 [rule_format] : "True' /= False' = True'"

IBE6 [rule_format] : "False' /= True' = True'"

IBE7 [rule_format] : "Not' (True' ==' False') = True'"

IBE8 [rule_format] : "Not' Not' (True' ==' False') = False'"

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
"ALL x. ALL y. x ==' y = True' --> x <_3 y = False'"

LeTAsymmetry [rule_format] :
"ALL x. ALL y. x <_3 y = True' --> y <_3 x = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. x <_3 y = True' & y <_3 z = True' --> x <_3 z = True'"

LeTTotal [rule_format] :
"ALL x.
 ALL y. (x <_3 y = True' | y <_3 x = True') | x ==' y = True'"

GeDef [rule_format] : "ALL x. ALL y. x >_3 y = y <_3 x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x >_3 y = False'"

GeTAsymmetry [rule_format] :
"ALL x. ALL y. x >_3 y = True' --> y >_3 x = False'"

GeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x >_3 y) && (y >_3 z) = True' --> x >_3 z = True'"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >_3 y) || (y >_3 x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL x. ALL y. x <=_3 y = (x <_3 y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <=_3 x = True'"

LeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x <=_3 y) && (y <=_3 z) = True' --> x <=_3 z = True'"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <=_3 y) && (y <=_3 x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >=_3 y = (x >_3 y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >=_3 x = True'"

GeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x >=_3 y) && (y >=_3 z) = True' --> x >=_3 z = True'"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >=_3 y) && (y >=_3 x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <_3 y = False' & x >_3 y = False')"

EqFSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <_3 y = True' | x >_3 y = True')"

EqTOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <=_3 y = True' & x >=_3 y = True')"

EqFOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <=_3 y = True' | x >=_3 y = True')"

EqTOrdTSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <_3 z = True' --> x <_3 z = True'"

EqTOrdFSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <_3 z = False' --> x <_3 z = False'"

EqTOrdTSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <_3 y = True' --> z <_3 x = True'"

EqTOrdFSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <_3 y = False' --> z <_3 x = False'"

LeTGeTRel [rule_format] :
"ALL x. ALL y. x <_3 y = True' = (y >_3 x = True')"

LeFGeFRel [rule_format] :
"ALL x. ALL y. x <_3 y = False' = (y >_3 x = False')"

LeqTGetTRel [rule_format] :
"ALL x. ALL y. x <=_3 y = True' = (y >=_3 x = True')"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. x <=_3 y = False' = (y >=_3 x = False')"

GeTLeTRel [rule_format] :
"ALL x. ALL y. x >_3 y = True' = (y <_3 x = True')"

GeFLeFRel [rule_format] :
"ALL x. ALL y. x >_3 y = False' = (y <_3 x = False')"

GeqTLeqTRel [rule_format] :
"ALL x. ALL y. x >=_3 y = True' = (y <=_3 x = True')"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. x >=_3 y = False' = (y <=_3 x = False')"

LeTGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <_3 y = True' = (x >_3 y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <_3 y = False' = (x >_3 y = True' | x ==' y = True')"

LeqTGeFRel [rule_format] :
"ALL x. ALL y. x <=_3 y = True' = (x >_3 y = False')"

LeqFGeTRel [rule_format] :
"ALL x. ALL y. x <=_3 y = False' = (x >_3 y = True')"

GeTLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >_3 y = True' = (x <_3 y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >_3 y = False' = (x <_3 y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL x. ALL y. x >=_3 y = True' = (x <_3 y = False')"

GeqFLeTRel [rule_format] :
"ALL x. ALL y. x >=_3 y = False' = (x <_3 y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <=_3 y = True' = (x <_3 y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <=_3 y = False' = (x <_3 y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >=_3 y = True' = (x >_3 y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >=_3 y = False' = (x >_3 y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL x. ALL y. x <_3 y = True' = (x >=_3 y = False')"

GeTLeqFRel [rule_format] :
"ALL x. ALL y. x >_3 y = True' = (x <=_3 y = False')"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <_3 y = (x <=_3 y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' LT = x <_3 y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' GT = x >_3 y"

MaxYDef [rule_format] :
"ALL x. ALL y. X_maxX3 x y ==' y = x <=_3 y"

MaxXDef [rule_format] :
"ALL x. ALL y. X_maxX3 x y ==' x = y <=_3 x"

MinXDef [rule_format] :
"ALL x. ALL y. X_minX3 x y ==' x = x <=_3 y"

MinYDef [rule_format] :
"ALL x. ALL y. X_minX3 x y ==' y = y <=_3 x"

MaxSym [rule_format] :
"ALL x. ALL y. X_maxX3 x y ==' y = X_maxX3 y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_minX3 x y ==' y = X_minX3 y x ==' y"

TO1 [rule_format] :
"ALL x.
 ALL y. (x ==' y = True' | x <_3 y = True') = (x <=_3 y = True')"

TO2 [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <_3 y = False'"

TO3 [rule_format] :
"ALL x.
 ALL y. Not' Not' (x <_3 y) = True' | Not' (x <_3 y) = True'"

TO4 [rule_format] :
"ALL x. ALL y. x <_3 y = True' --> Not' (x ==' y) = True'"

TO5 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <_3 y = True' & y <_3 z = True') & z <_3 w = True' -->
 x <_3 w = True'"

TO6 [rule_format] :
"ALL x. ALL z. z <_3 x = True' --> Not' (x <_3 z) = True'"

TO7 [rule_format] :
"ALL x. ALL y. x <_3 y = True' = (y >_3 x = True')"

IOO13 [rule_format] : "LT <_3 EQ = True'"

IOO14 [rule_format] : "EQ <_3 GT = True'"

IOO15 [rule_format] : "LT <_3 GT = True'"

IOO16 [rule_format] : "LT <=_3 EQ = True'"

IOO17 [rule_format] : "EQ <=_3 GT = True'"

IOO18 [rule_format] : "LT <=_3 GT = True'"

IOO19 [rule_format] : "EQ >=_3 LT = True'"

IOO20 [rule_format] : "GT >=_3 EQ = True'"

IOO21 [rule_format] : "GT >=_3 LT = True'"

IOO22 [rule_format] : "EQ >_3 LT = True'"

IOO23 [rule_format] : "GT >_3 EQ = True'"

IOO24 [rule_format] : "GT >_3 LT = True'"

IOO25 [rule_format] : "X_maxX3 LT EQ ==' EQ = True'"

IOO26 [rule_format] : "X_maxX3 EQ GT ==' GT = True'"

IOO27 [rule_format] : "X_maxX3 LT GT ==' GT = True'"

IOO28 [rule_format] : "X_minX3 LT EQ ==' LT = True'"

IOO29 [rule_format] : "X_minX3 EQ GT ==' EQ = True'"

IOO30 [rule_format] : "X_minX3 LT GT ==' LT = True'"

IOO31 [rule_format] : "compare LT LT ==' EQ = True'"

IOO32 [rule_format] : "compare EQ EQ ==' EQ = True'"

IOO33 [rule_format] : "compare GT GT ==' EQ = True'"

IBO5 [rule_format] : "False' <_3 True' = True'"

IBO6 [rule_format] : "False' >=_3 True' = False'"

IBO7 [rule_format] : "True' >=_3 False' = True'"

IBO8 [rule_format] : "True' <_3 False' = False'"

IBO9 [rule_format] : "X_maxX3 False' True' ==' True' = True'"

IBO10 [rule_format] : "X_minX3 False' True' ==' False' = True'"

IBO11 [rule_format] : "compare True' True' ==' EQ = True'"

IBO12 [rule_format] : "compare False' False' ==' EQ = True'"

IUO01 [rule_format] : "() <=_3 () = True'"

IUO02 [rule_format] : "() <_3 () = False'"

IUO03 [rule_format] : "() >=_3 () = True'"

IUO04 [rule_format] : "() >_3 () = False'"

IUO05 [rule_format] : "X_maxX3 () () ==' () = True'"

IUO06 [rule_format] : "X_minX3 () () ==' () = True'"

IUO07 [rule_format] : "compare () () ==' EQ = True'"

LengthNil [rule_format] : "length'(Nil') = 0'"

LengthCons [rule_format] :
"ALL x. ALL xs. length'(X_Cons x xs) = length'(xs) +' 1'"

NotDefHead [rule_format] : "~ defOp (head(Nil'))"

HeadDef [rule_format] :
"ALL x. ALL xs. head(X_Cons x xs) = makePartial x"

NotDefTail [rule_format] : "~ defOp (tail(Nil'))"

TailDef [rule_format] :
"ALL x. ALL xs. tail(X_Cons x xs) = makePartial xs"

FoldrNil [rule_format] : "ALL f. ALL s. foldr'(f, s, Nil') = s"

FoldrCons [rule_format] :
"ALL f.
 ALL s.
 ALL x. ALL xs. foldr'(f, s, X_Cons x xs) = f (x, foldr'(f, s, xs))"

FoldlNil [rule_format] : "ALL g. ALL t. foldl'(g, t, Nil') = t"

FoldlCons [rule_format] :
"ALL g.
 ALL t.
 ALL z. ALL zs. foldl'(g, t, X_Cons z zs) = foldl'(g, g (t, z), zs)"

MapNil [rule_format] : "ALL h. map'(h, Nil') = Nil'"

MapCons [rule_format] :
"ALL h.
 ALL x. ALL xs. map'(h, X_Cons x xs) = X_Cons (h x) (map'(h, xs))"

XPlusXPlusNil [rule_format] : "ALL l. Nil' ++' l = l"

XPlusXPlusCons [rule_format] :
"ALL l. ALL x. ALL xs. X_Cons x xs ++' l = X_Cons x (xs ++' l)"

FilterNil [rule_format] : "ALL p. filter'(p, Nil') = Nil'"

FilterConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x = True' -->
 filter'(p, X_Cons x xs) = X_Cons x (filter'(p, xs))"

FilterConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs. p x = False' --> filter'(p, X_Cons x xs) = filter'(p, xs)"

ZipNil [rule_format] : "ALL l. zip'(Nil', l) = Nil'"

ZipConsNil [rule_format] :
"ALL l. ALL x. ALL xs. l = Nil' --> zip'(X_Cons x xs, l) = Nil'"

ZipConsCons [rule_format] :
"ALL l.
 ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 l = X_Cons y ys -->
 zip'(X_Cons x xs, l) = X_Cons (x, y) (zip'(xs, ys))"

UnzipNil [rule_format] : "unzip(Nil') = (Nil', Nil')"

UnzipCons [rule_format] :
"ALL ps.
 ALL x.
 ALL z.
 unzip(X_Cons (x, z) ps) =
 (let (ys, zs) = unzip(ps) in (X_Cons x ys, X_Cons z zs))"

FoldlDecomp [rule_format] :
"ALL e.
 ALL i.
 ALL xs.
 ALL zs. foldl'(i, e, xs ++' zs) = foldl'(i, foldl'(i, e, xs), zs)"

MapDecomp [rule_format] :
"ALL f.
 ALL xs. ALL zs. map'(f, xs ++' zs) = map'(f, xs) ++' map'(f, zs)"

MapFunctor [rule_format] :
"ALL f.
 ALL g. ALL xs. map'(X__o__X (g, f), xs) = map'(g, map'(f, xs))"

FilterProm [rule_format] :
"ALL f.
 ALL p.
 ALL xs.
 filter'(p, map'(f, xs)) = map'(f, filter'(X__o__X (p, f), xs))"

ZipSpec [rule_format] :
"ALL xs.
 ALL ys.
 length'(xs) = length'(ys) --> unzip(zip'(xs, ys)) = (xs, ys)"

EqualListNilDef [rule_format] : "Nil' ==' Nil' = True'"

EqualListDef [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys. X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

LeListDef [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. X_Cons z zs <_3 X_Cons w ws = (z <_3 w) && (zs <_3 ws)"

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
declare leq_def2_Nat [simp]
declare leq_def3_Nat [simp]
declare even_0_Nat [simp]
declare even_suc_Nat [simp]
declare factorial_0 [simp]
declare add_0_Nat [simp]
declare mult_0_Nat [simp]
declare power_0_Nat [simp]
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
declare neg_def_Int [simp]
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
declare TO2 [simp]
declare TO4 [simp]
declare TO6 [simp]
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
declare LengthNil [simp]
declare NotDefHead [simp]
declare HeadDef [simp]
declare NotDefTail [simp]
declare TailDef [simp]
declare FoldrNil [simp]
declare FoldlNil [simp]
declare MapNil [simp]
declare XPlusXPlusNil [simp]
declare FilterNil [simp]
declare FilterConsF [simp]
declare ZipNil [simp]
declare EqualListNilDef [simp]

theorem LeListNilFalse : "Nil' <_3 Nil' = False'"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by auto

ML "Header.record \"LeListNilFalse\""

end
