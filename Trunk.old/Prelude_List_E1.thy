theory Prelude_List_E1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"FoldlDecomp\", \"MapDecomp\", \"MapFunctor\", \"FilterProm\",
     \"ZipSpec\", \"ga_selector_pre\", \"ga_injective_suc\",
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
     \"LengthNil\", \"LengthCons\", \"NotDefHead\", \"HeadDef\",
     \"FoldrNil\", \"FoldrCons\", \"FoldlNil\", \"FoldlCons\",
     \"MapNil\", \"MapCons\", \"XPlusXPlusNil\", \"XPlusXPlusCons\",
     \"FilterNil\", \"FilterConsT\", \"FilterConsF\", \"ZipNil\",
     \"ZipConsNil\", \"ZipConsCons\", \"UnzipNil\", \"UnzipCons\"]"

typedecl X_Int

datatype Nat = X0X2 ("0''''") | X_suc "Nat" ("suc/'(_')" [3] 999)
datatype Bool = X_False ("False''") | X_True ("True''")
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
IntToNat__X :: "X_Int => Nat option" ("(IntToNat/ _)" [56] 56)
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
X__XExclam :: "Nat => Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "Nat => Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "Nat => Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "Nat => Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "Nat => Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XMinusXExclam__X :: "Nat => Nat => Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "Nat => Nat => Nat option" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "Nat => Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "Nat => Nat => Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int option" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "Nat => Nat => Nat option" ("(_/ '/?''''/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "Nat => Nat => Nat" ("(_/ *''''/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int option" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "Nat => Nat => Nat option" ("(_/ div''''/ _)" [54,54] 52)
X__mod__XX1 :: "X_Int => X_Int => Nat option" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "Nat => Nat => Nat option" ("(_/ mod''''/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X__quot__X :: "X_Int => X_Int => X_Int option" ("(_/ quot/ _)" [54,54] 52)
X__rem__X :: "X_Int => X_Int => X_Int option" ("(_/ rem/ _)" [54,54] 52)
X_abs :: "X_Int => Nat" ("abs''/'(_')" [3] 999)
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "Nat => bool" ("even''''/'(_')" [3] 999)
X_filter :: "('a => Bool) => 'a List => 'a List" ("filter''/'(_,/ _')" [3,3] 999)
X_foldl :: "('a * 'b => 'a) => 'a => 'b List => 'a" ("foldl''/'(_,/ _,/ _')" [3,3,3] 999)
X_foldr :: "('a * 'b => 'b) => 'b => 'a List => 'b" ("foldr''/'(_,/ _,/ _')" [3,3,3] 999)
X_head :: "'a List => 'a" ("head/'(_')" [3] 999)
X_length :: "'a List => X_Int" ("length''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List" ("map''/'(_,/ _')" [3,3] 999)
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "Nat => Nat => Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "Nat => Nat => Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "Nat => bool" ("odd''''/'(_')" [3] 999)
X_pre :: "Nat => Nat option" ("pre/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List" ("zip''/'(_,/ _')" [3,3] 999)
otherwiseH :: "Bool"

instance Bool:: type ..
instance List::("type") type ..
instance Nat:: type ..
instance X_Int:: type ..

axioms
ga_selector_pre [rule_format] : "ALL XX1. pre(suc(XX1)) = Some XX1"

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
"ALL m. ALL X_n. m <='' X_n --> Some (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >='' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = Some r = (m = r +'' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /?'' X_n) = (~ X_n = 0'' & m mod'' X_n = Some 0'')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /?'' 0'')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r. X_n >'' 0'' --> m /?'' X_n = Some r = (m = r *'' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div'' X_n) = (~ X_n = 0'')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div'' X_n = Some r = (EX s. m = (X_n *'' r) +'' s & s <'' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod'' X_n) = (~ X_n = 0'')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod'' X_n = Some s = (EX r. m = (X_n *'' r) +'' s & s <'' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +'' s) *'' t = (r *'' t) +'' (s *'' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *'' (r +'' s) = (t *'' r) +'' (t *'' s)"

min_0 [rule_format] : "ALL m. min''(m, 0'') = 0''"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0'' -->
 Some m =
 (case case m div'' X_n of
       None => None |
       Some Xc2 => Some (Xc2 *'' X_n) of
  None => None |
  Some Xc0 =>
  (case m mod'' X_n of
   None => None |
   Some Xc1 => Some (Xc0 +'' Xc1)))"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^'' (r +'' s) = (m ^'' r) *'' (m ^'' s)"

equality_Int [rule_format] :
"ALL a.
 ALL b. ALL c. ALL d. a -'' b = c -'' d = (a +'' d = c +'' b)"

NatToInt [rule_format] : "ALL a. NatToInt a = a -'' 0''"

IntToNat [rule_format] :
"ALL a. ALL b. IntToNat (a -'' b) = Some (a -! b)"

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
 Some (abs'(m)) = (if m <' 0' then IntToNat -' m else IntToNat m)"

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
"ALL m. ALL X_n. defOp (m /?' X_n) = (m mod' X_n = Some 0'')"

divide_alt_Int [rule_format] :
"ALL m.
 ALL X_n. ALL r. m /?' X_n = Some r = (~ X_n = 0' & X_n *' r = m)"

divide_Int [rule_format] :
"ALL m.
 ALL X_n.
 m /?' X_n =
 (case NatToInt abs'(m) /?' NatToInt abs'(X_n) of
  None => None |
  Some Xc0 => Some ((sign(m) *' sign(X_n)) *' Xc0))"

div_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = Some r =
 (EX a. m = (X_n *' r) +' NatToInt a & a <'' abs'(X_n))"

quot_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m quot X_n) = (~ X_n = 0')"

quot_neg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m <' 0' -->
 m quot X_n = Some r =
 (EX s.
  m = (X_n *' r) +' s & 0' >=' s & s >' -' NatToInt abs'(X_n))"

quot_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m >=' 0' -->
 m quot X_n = Some r =
 (EX s. m = (X_n *' r) +' s & 0' <=' s & s <' NatToInt abs'(X_n))"

rem_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m rem X_n) = (~ X_n = 0')"

quot_rem_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m <' 0' -->
 m rem X_n = Some s =
 (EX r.
  m = (X_n *' r) +' s & 0' >=' s & s >' -' NatToInt abs'(X_n))"

rem_nonneg_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m >=' 0' -->
 m rem X_n = Some s =
 (EX r. m = (X_n *' r) +' s & 0' <=' s & s <' NatToInt abs'(X_n))"

mod_dom_Int [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Int [rule_format] :
"ALL m.
 ALL X_n.
 ALL a.
 m mod' X_n = Some a =
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
 Some m =
 (case case m div' X_n of
       None => None |
       Some Xc3 => Some (Xc3 *' X_n) of
  None => None |
  Some Xc0 =>
  (case case m mod' X_n of
        None => None |
        Some Xc2 => Some (NatToInt Xc2) of
   None => None |
   Some Xc1 => Some (Xc0 +' Xc1)))"

quot_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (case case m quot X_n of
       None => None |
       Some Xc1 => Some (abs'(Xc1)) of
  None => None |
  Some Xc0 => Some (NatToInt Xc0)) =
 NatToInt abs'(m) quot NatToInt abs'(X_n)"

rem_abs_Int [rule_format] :
"ALL m.
 ALL X_n.
 (case case m rem X_n of
       None => None |
       Some Xc1 => Some (abs'(Xc1)) of
  None => None |
  Some Xc0 => Some (NatToInt Xc0)) =
 NatToInt abs'(m) rem NatToInt abs'(X_n)"

quot_rem_Int_1 [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 Some m =
 (case case m quot X_n of
       None => None |
       Some Xc2 => Some (Xc2 *' X_n) of
  None => None |
  Some Xc0 =>
  (case m rem X_n of
   None => None |
   Some Xc1 => Some (Xc0 +' Xc1)))"

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
"ALL f. ALL g. Some o X__o__X (f, g) = Some o (% x. f (g x))"

LengthNil [rule_format] : "length'(Nil') = 0'"

LengthCons [rule_format] :
"ALL x. ALL xs. length'(X_Cons x xs) = length'(xs) +' 1'"

NotDefHead [rule_format] : "~ True"

HeadDef [rule_format] : "ALL x. ALL xs. head(X_Cons x xs) = x"

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
declare LengthNil [simp]
declare NotDefHead [simp]
declare HeadDef [simp]
declare FoldrNil [simp]
declare FoldlNil [simp]
declare MapNil [simp]
declare XPlusXPlusNil [simp]
declare FilterNil [simp]
declare FilterConsF [simp]
declare ZipNil [simp]

theorem FoldlDecomp :
"ALL e.
 ALL i.
 ALL xs.
 ALL zs. foldl'(i, e, xs ++' zs) = foldl'(i, foldl'(i, e, xs), zs)"
using HeadDef by auto

ML "Header.record \"FoldlDecomp\""

theorem MapDecomp :
"ALL f.
 ALL xs. ALL zs. map'(f, xs ++' zs) = map'(f, xs) ++' map'(f, zs)"
using HeadDef by auto

ML "Header.record \"MapDecomp\""

theorem MapFunctor :
"ALL f.
 ALL g. ALL xs. map'(X__o__X (g, f), xs) = map'(g, map'(f, xs))"
using HeadDef by auto

ML "Header.record \"MapFunctor\""

theorem FilterProm :
"ALL f.
 ALL p.
 ALL xs.
 filter'(p, map'(f, xs)) = map'(f, filter'(X__o__X (p, f), xs))"
using HeadDef by auto

ML "Header.record \"FilterProm\""

theorem ZipSpec :
"ALL xs.
 ALL ys.
 length'(xs) = length'(ys) --> unzip(zip'(xs, ys)) = (xs, ys)"
using HeadDef by auto

ML "Header.record \"ZipSpec\""

end
