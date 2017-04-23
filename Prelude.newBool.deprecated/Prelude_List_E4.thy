theory Prelude_List_E4
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
     \"div_mod_Nat\", \"power_Nat\", \"Comp1\", \"IdDef\", \"FlipDef\",
     \"FstDef\", \"SndDef\", \"CurryDef\", \"UncurryDef\", \"NotFalse\",
     \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\",
     \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\", \"notNot1\",
     \"notNot2\", \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\",
     \"EqualTransT\", \"DiffDef\", \"DiffSymDef\", \"DiffTDef\",
     \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IUE1\",
     \"IUE2\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\", \"IBE5\",
     \"IBE6\", \"IBE7\", \"IBE8\", \"IOE01\", \"IOE02\", \"IOE03\",
     \"IOE04\", \"IOE05\", \"IOE06\", \"IOE07\", \"IOE08\", \"IOE09\",
     \"LeIrreflexivity\", \"LeTAsymmetry\", \"LeTTransitive\",
     \"LeTTotal\", \"GeDef\", \"GeIrreflexivity\", \"GeTAsymmetry\",
     \"GeTTransitive\", \"GeTTotal\", \"LeqDef\", \"LeqReflexivity\",
     \"LeqTTransitive\", \"LeqTTotal\", \"GeqDef\", \"GeqReflexivity\",
     \"GeqTTransitive\", \"GeqTTotal\", \"EqTSOrdRel\", \"EqFSOrdRel\",
     \"EqTOrdRel\", \"EqFOrdRel\", \"EqTOrdTSubstE\", \"EqTOrdFSubstE\",
     \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeFEqFRel\",
     \"LeFGeTEqTRel\", \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\",
     \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\",
     \"GeqFLeqFRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
     \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
     \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
     \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
     \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
     \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\",
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IUO01\", \"IUO02\",
     \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"IOO13\",
     \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\",
     \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\",
     \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\",
     \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\",
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"LengthNil\",
     \"LengthCons\", \"NotDefHead\", \"HeadDef\", \"NotDefTail\",
     \"TailDef\", \"FoldrNil\", \"FoldrCons\", \"FoldlNil\",
     \"FoldlCons\", \"MapNil\", \"MapCons\", \"XPlusXPlusNil\",
     \"XPlusXPlusCons\", \"XPlusXPlusPrefixDef\", \"FilterNil\",
     \"FilterConsT\", \"FilterConsF\", \"ZipNil\", \"ZipConsNil\",
     \"ZipConsCons\", \"UnzipNil\", \"UnzipCons\", \"ILE02\", \"ILO05\",
     \"ILO06\", \"ILO07\", \"ILE01\", \"ILO01\", \"ILO02\", \"ILO03\",
     \"ILO04\", \"ILO08\", \"ILO09\", \"ILO10\", \"ILO11\", \"ILO12\",
     \"ILO13\", \"ILO14\", \"ILO15\", \"ILO16\", \"ILO17\", \"ILO18\",
     \"ILO19\", \"ILO20\", \"ILO21\", \"ILO22\", \"FoldlDecomp\",
     \"MapDecomp\", \"MapFunctor\", \"FilterProm\", \"LengthNil1\",
     \"LengthEqualNil\", \"LengthEqualCons\", \"ZipSpec\"]"

typedecl Bool
typedecl Unit

datatype X_Nat = X0 ("0''") | X_suc "X_Nat" ("suc/'(_')" [3] 999)
datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
Not__X :: "bool => bool" ("(Not''/ _)" [56] 56)
X1 :: "X_Nat" ("1''")
X2 :: "X_Nat" ("2''")
X3 :: "X_Nat" ("3''")
X4 :: "X_Nat" ("4''")
X5 :: "X_Nat" ("5''")
X6 :: "X_Nat" ("6''")
X7 :: "X_Nat" ("7''")
X8 :: "X_Nat" ("8''")
X9 :: "X_Nat" ("9''")
XLtXPlusXPlusXGt :: "'a List => 'a List => 'a List"
X__XAmpXAmp__X :: "bool => bool => bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "'a => 'a => bool" ("(_/ >=''''/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Nat => X_Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "'a => 'a => bool" ("(_/ >''''/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Nat => X_Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "'a => 'a => bool" ("(_/ <=''''/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Nat => X_Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "'a => 'a => bool" ("(_/ <''''/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__XVBarXVBar__X :: "bool => bool => bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__X :: "X_Nat => X_Nat => X_Nat" ("(_/ *''/ _)" [54,54] 52)
X__div__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__mod__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X_curry :: "('a * 'b => 'c) => 'a => 'b => 'c"
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_filter :: "('a => bool) => 'a List => 'a List"
X_flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
X_foldl :: "('a => 'b => 'a) => 'a => 'b List => 'a"
X_foldr :: "('a => 'b => 'b) => 'b => 'a List => 'b"
X_fst :: "'a => 'b => 'a" ("fst''/'(_,/ _')" [3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a => 'a" ("id''/'(_')" [3] 999)
X_length :: "'a List => X_Nat" ("length''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_maxX1 :: "X_Nat => X_Nat => X_Nat" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "'a => 'a => 'a"
X_minX1 :: "X_Nat => X_Nat => X_Nat" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "'a => 'a => 'a"
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_snd :: "'a => 'b => 'b" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List"
compare :: "'a => 'a => Ordering"
otherwiseH :: "bool"
uncurry :: "('a => 'b => 'c) => 'a * 'b => 'c"

axioms
ga_selector_pre [rule_format] :
"ALL XX1. pre(suc(XX1)) = makePartial XX1"

ga_injective_suc [rule_format] :
"ALL XX1. ALL Y1. suc(XX1) = suc(Y1) = (XX1 = Y1)"

ga_disjoint_0_suc [rule_format] : "ALL Y1. ~ 0' = suc(Y1)"

ga_selector_undef_pre_0 [rule_format] : "~ defOp (pre(0'))"

X1_def_Nat [rule_format] : "1' = suc(0')"

X2_def_Nat [rule_format] : "2' = suc(1')"

X3_def_Nat [rule_format] : "3' = suc(2')"

X4_def_Nat [rule_format] : "4' = suc(3')"

X5_def_Nat [rule_format] : "5' = suc(4')"

X6_def_Nat [rule_format] : "6' = suc(5')"

X7_def_Nat [rule_format] : "7' = suc(6')"

X8_def_Nat [rule_format] : "8' = suc(7')"

X9_def_Nat [rule_format] : "9' = suc(8')"

decimal_def [rule_format] :
"ALL m. ALL X_n. m @@ X_n = (m *' suc(9')) +' X_n"

ga_comm___XPlus__ [rule_format] : "ALL x. ALL y. x +' y = y +' x"

ga_assoc___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. (x +' y) +' z = x +' (y +' z)"

ga_right_unit___XPlus__ [rule_format] : "ALL x. x +' 0' = x"

ga_left_unit___XPlus__ [rule_format] : "ALL x. 0' +' x = x"

ga_left_comm___XPlus__ [rule_format] :
"ALL x. ALL y. ALL z. x +' (y +' z) = y +' (x +' z)"

ga_comm___Xx__ [rule_format] : "ALL x. ALL y. x *' y = y *' x"

ga_assoc___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. (x *' y) *' z = x *' (y *' z)"

ga_right_unit___Xx__ [rule_format] : "ALL x. x *' 1' = x"

ga_left_unit___Xx__ [rule_format] : "ALL x. 1' *' x = x"

ga_left_comm___Xx__ [rule_format] :
"ALL x. ALL y. ALL z. x *' (y *' z) = y *' (x *' z)"

ga_comm_min [rule_format] : "ALL x. ALL y. min'(x, y) = min'(y, x)"

ga_assoc_min [rule_format] :
"ALL x. ALL y. ALL z. min'(min'(x, y), z) = min'(x, min'(y, z))"

ga_left_comm_min [rule_format] :
"ALL x. ALL y. ALL z. min'(x, min'(y, z)) = min'(y, min'(x, z))"

ga_comm_max [rule_format] : "ALL x. ALL y. max'(x, y) = max'(y, x)"

ga_assoc_max [rule_format] :
"ALL x. ALL y. ALL z. max'(max'(x, y), z) = max'(x, max'(y, z))"

ga_right_unit_max [rule_format] : "ALL x. max'(x, 0') = x"

ga_left_unit_max [rule_format] : "ALL x. max'(0', x) = x"

ga_left_comm_max [rule_format] :
"ALL x. ALL y. ALL z. max'(x, max'(y, z)) = max'(y, max'(x, z))"

leq_def1_Nat [rule_format] : "ALL X_n. 0' <=' X_n"

leq_def2_Nat [rule_format] : "ALL X_n. ~ suc(X_n) <=' 0'"

leq_def3_Nat [rule_format] :
"ALL m. ALL X_n. (suc(m) <=' suc(X_n)) = (m <=' X_n)"

geq_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >=' X_n) = (X_n <=' m)"

less_def_Nat [rule_format] :
"ALL m. ALL X_n. (m <' X_n) = (m <=' X_n & ~ m = X_n)"

greater_def_Nat [rule_format] :
"ALL m. ALL X_n. (m >' X_n) = (X_n <' m)"

even_0_Nat [rule_format] : "even'(0')"

even_suc_Nat [rule_format] : "ALL m. even'(suc(m)) = odd'(m)"

odd_def_Nat [rule_format] : "ALL m. odd'(m) = (~ even'(m))"

factorial_0 [rule_format] : "0' !' = 1'"

factorial_suc [rule_format] :
"ALL X_n. suc(X_n) !' = suc(X_n) *' X_n !'"

add_0_Nat [rule_format] : "ALL m. 0' +' m = m"

add_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) +' m = suc(X_n +' m)"

mult_0_Nat [rule_format] : "ALL m. 0' *' m = 0'"

mult_suc_Nat [rule_format] :
"ALL m. ALL X_n. suc(X_n) *' m = (X_n *' m) +' m"

power_0_Nat [rule_format] : "ALL m. m ^' 0' = 1'"

power_suc_Nat [rule_format] :
"ALL m. ALL X_n. m ^' suc(X_n) = m *' (m ^' X_n)"

min_def_Nat [rule_format] :
"ALL m. ALL X_n. min'(m, X_n) = (if m <=' X_n then m else X_n)"

max_def_Nat [rule_format] :
"ALL m. ALL X_n. max'(m, X_n) = (if m <=' X_n then X_n else m)"

subTotal_def1_Nat [rule_format] :
"ALL m. ALL X_n. m >' X_n --> X_n -! m = 0'"

subTotal_def2_Nat [rule_format] :
"ALL m. ALL X_n. m <=' X_n --> makePartial (X_n -! m) = X_n -? m"

sub_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m -? X_n) = (m >=' X_n)"

sub_def_Nat [rule_format] :
"ALL m. ALL X_n. ALL r. m -? X_n = makePartial r = (m = r +' X_n)"

divide_dom_Nat [rule_format] :
"ALL m.
 ALL X_n.
 defOp (m /? X_n) = (~ X_n = 0' & m mod' X_n = makePartial 0')"

divide_0_Nat [rule_format] : "ALL m. ~ defOp (m /? 0')"

divide_Pos_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r. X_n >' 0' --> m /? X_n = makePartial r = (m = r *' X_n)"

div_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m div' X_n) = (~ X_n = 0')"

div_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL r.
 m div' X_n = makePartial r =
 (EX s. m = (X_n *' r) +' s & s <' X_n)"

mod_dom_Nat [rule_format] :
"ALL m. ALL X_n. defOp (m mod' X_n) = (~ X_n = 0')"

mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ALL s.
 m mod' X_n = makePartial s =
 (EX r. m = (X_n *' r) +' s & s <' X_n)"

distr1_Nat [rule_format] :
"ALL r. ALL s. ALL t. (r +' s) *' t = (r *' t) +' (s *' t)"

distr2_Nat [rule_format] :
"ALL r. ALL s. ALL t. t *' (r +' s) = (t *' r) +' (t *' s)"

min_0 [rule_format] : "ALL m. min'(m, 0') = 0'"

div_mod_Nat [rule_format] :
"ALL m.
 ALL X_n.
 ~ X_n = 0' -->
 makePartial m =
 restrictOp
 (makePartial
  ((makeTotal (m div' X_n) *' X_n) +' makeTotal (m mod' X_n)))
 (defOp (m div' X_n) & defOp (m mod' X_n))"

power_Nat [rule_format] :
"ALL m. ALL r. ALL s. m ^' (r +' s) = (m ^' r) *' (m ^' s)"

Comp1 [rule_format] :
"ALL f. ALL g. ALL y. X__o__X (f, g) y = f (g y)"

IdDef [rule_format] : "ALL x. id'(x) = x"

FlipDef [rule_format] : "ALL f. ALL x. ALL y. X_flip f y x = f x y"

FstDef [rule_format] : "ALL x. ALL y. fst'(x, y) = x"

SndDef [rule_format] : "ALL x. ALL y. snd'(x, y) = y"

CurryDef [rule_format] :
"ALL g. ALL x. ALL y. X_curry g x y = g (x, y)"

UncurryDef [rule_format] :
"ALL f. ALL x. ALL y. uncurry f (x, y) = f x y"

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

IUE1 [rule_format] : "() ==' ()"

IUE2 [rule_format] : "~ () /= ()"

IBE1 [rule_format] : "() ==' ()"

IBE2 [rule_format] : "False & () ==' ()"

IBE3 [rule_format] : "~ (False & () ==' ())"

IBE4 [rule_format] : "~ (False & () ==' ())"

IBE5 [rule_format] : "False & () /= ()"

IBE6 [rule_format] : "False & () /= ()"

IBE7 [rule_format] : "Not' (False & () ==' ())"

IBE8 [rule_format] : "~ Not' Not' (False & () ==' ())"

IOE01 [rule_format] : "LT ==' LT"

IOE02 [rule_format] : "EQ ==' EQ"

IOE03 [rule_format] : "GT ==' GT"

IOE04 [rule_format] : "~ LT ==' EQ"

IOE05 [rule_format] : "~ LT ==' GT"

IOE06 [rule_format] : "~ EQ ==' GT"

IOE07 [rule_format] : "LT /= EQ"

IOE08 [rule_format] : "LT /= GT"

IOE09 [rule_format] : "EQ /= GT"

LeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y --> ~ x <'' y"

LeTAsymmetry [rule_format] : "ALL x. ALL y. x <'' y --> ~ y <'' x"

LeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. x <'' y & y <'' z --> x <'' z"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <'' y | y <'' x) | x ==' y"

GeDef [rule_format] : "ALL x. ALL y. x >'' y = y <'' x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y --> ~ x >'' y"

GeTAsymmetry [rule_format] : "ALL x. ALL y. x >'' y --> ~ y >'' x"

GeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >'' y) && (y >'' z) --> x >'' z"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >'' y) || (y >'' x)) || (x ==' y)"

LeqDef [rule_format] :
"ALL x. ALL y. x <='' y = (x <'' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <='' x"

LeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x <='' y) && (y <='' z) --> x <='' z"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <='' y) && (y <='' x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >='' y = (x >'' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >='' x"

GeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >='' y) && (y >='' z) --> x >='' z"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >='' y) && (y >='' x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (~ x <'' y & ~ x >'' y)"

EqFSOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <'' y | x >'' y)"

EqTOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (x <='' y & x >='' y)"

EqFOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <='' y | x >='' y)"

EqTOrdTSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & y <'' z --> x <'' z"

EqTOrdFSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ y <'' z --> ~ x <'' z"

EqTOrdTSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & z <'' y --> z <'' x"

EqTOrdFSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ z <'' y --> ~ z <'' x"

LeTGeFEqFRel [rule_format] :
"ALL x. ALL y. x <'' y = (~ x >'' y & ~ x ==' y)"

LeFGeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x <'' y) = (x >'' y | x ==' y)"

LeTGeTRel [rule_format] : "ALL x. ALL y. x <'' y = y >'' x"

LeFGeFRel [rule_format] : "ALL x. ALL y. (~ x <'' y) = (~ y >'' x)"

LeqTGetTRel [rule_format] : "ALL x. ALL y. x <='' y = y >='' x"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. (~ x <='' y) = (~ y >='' x)"

GeTLeTRel [rule_format] : "ALL x. ALL y. x >'' y = y <'' x"

GeFLeFRel [rule_format] : "ALL x. ALL y. (~ x >'' y) = (~ y <'' x)"

GeqTLeqTRel [rule_format] : "ALL x. ALL y. x >='' y = y <='' x"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. (~ x >='' y) = (~ y <='' x)"

LeqTGeFRel [rule_format] : "ALL x. ALL y. x <='' y = (~ x >'' y)"

LeqFGeTRel [rule_format] : "ALL x. ALL y. (~ x <='' y) = x >'' y"

GeTLeFEqFRel [rule_format] :
"ALL x. ALL y. x >'' y = (~ x <'' y & ~ x ==' y)"

GeFLeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x >'' y) = (x <'' y | x ==' y)"

GeqTLeFRel [rule_format] : "ALL x. ALL y. x >='' y = (~ x <'' y)"

GeqFLeTRel [rule_format] : "ALL x. ALL y. (~ x >='' y) = x <'' y"

LeqTLeTEqTRel [rule_format] :
"ALL x. ALL y. x <='' y = (x <'' y | x ==' y)"

LeqFLeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x <='' y) = (~ x <'' y & ~ x ==' y)"

GeqTGeTEqTRel [rule_format] :
"ALL x. ALL y. x >='' y = (x >'' y | x ==' y)"

GeqFGeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x >='' y) = (~ x >'' y & ~ x ==' y)"

LeTGeqFRel [rule_format] : "ALL x. ALL y. x <'' y = (~ x >='' y)"

GeTLeqFRel [rule_format] : "ALL x. ALL y. x >'' y = (~ x <='' y)"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <'' y = (x <='' y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' LT = x <'' y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' GT = x >'' y"

MaxYDef [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' y = x <='' y"

MaxXDef [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' x = y <='' x"

MinXDef [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' x = x <='' y"

MinYDef [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' y = y <='' x"

MaxSym [rule_format] :
"ALL x. ALL y. X_maxX2 x y ==' y = X_maxX2 y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_minX2 x y ==' y = X_minX2 y x ==' y"

TO1 [rule_format] : "ALL x. ALL y. (x ==' y | x <'' y) = x <='' y"

TO2 [rule_format] : "ALL x. ALL y. x ==' y --> ~ x <'' y"

TO3 [rule_format] :
"ALL x. ALL y. Not' Not' (x <'' y) | Not' (x <'' y)"

TO4 [rule_format] : "ALL x. ALL y. x <'' y --> Not' (x ==' y)"

TO5 [rule_format] :
"ALL w.
 ALL x. ALL y. ALL z. (x <'' y & y <'' z) & z <'' w --> x <'' w"

TO6 [rule_format] : "ALL x. ALL z. z <'' x --> Not' (x <'' z)"

TO7 [rule_format] : "ALL x. ALL y. x <'' y = y >'' x"

IUO01 [rule_format] : "() <='' ()"

IUO02 [rule_format] : "bool2partial (() <'' ()) = undefinedOp"

IUO03 [rule_format] : "() >='' ()"

IUO04 [rule_format] : "bool2partial (() >'' ()) = undefinedOp"

IUO05 [rule_format] : "X_maxX2 () () ==' ()"

IUO06 [rule_format] : "X_minX2 () () ==' ()"

IUO07 [rule_format] : "compare () () ==' EQ"

IOO13 [rule_format] : "LT <'' EQ"

IOO14 [rule_format] : "EQ <'' GT"

IOO15 [rule_format] : "LT <'' GT"

IOO16 [rule_format] : "LT <='' EQ"

IOO17 [rule_format] : "EQ <='' GT"

IOO18 [rule_format] : "LT <='' GT"

IOO19 [rule_format] : "EQ >='' LT"

IOO20 [rule_format] : "GT >='' EQ"

IOO21 [rule_format] : "GT >='' LT"

IOO22 [rule_format] : "EQ >'' LT"

IOO23 [rule_format] : "GT >'' EQ"

IOO24 [rule_format] : "GT >'' LT"

IOO25 [rule_format] : "X_maxX2 LT EQ ==' EQ"

IOO26 [rule_format] : "X_maxX2 EQ GT ==' GT"

IOO27 [rule_format] : "X_maxX2 LT GT ==' GT"

IOO28 [rule_format] : "X_minX2 LT EQ ==' LT"

IOO29 [rule_format] : "X_minX2 EQ GT ==' EQ"

IOO30 [rule_format] : "X_minX2 LT GT ==' LT"

IOO31 [rule_format] : "compare LT LT ==' EQ"

IOO32 [rule_format] : "compare EQ EQ ==' EQ"

IOO33 [rule_format] : "compare GT GT ==' EQ"

IBO5 [rule_format] : "False & () <'' ()"

IBO6 [rule_format] : "~ (False & () >='' ())"

IBO7 [rule_format] : "False & () >='' ()"

IBO8 [rule_format] : "~ (False & () <'' ())"

IBO9 [rule_format] : "False & X_maxX2 () () ==' ()"

IBO10 [rule_format] : "False & X_minX2 () () ==' ()"

IBO11 [rule_format] : "compare () () ==' EQ"

IBO12 [rule_format] : "False & compare () () ==' EQ"

LengthNil [rule_format] : "length'(Nil') = 0'"

LengthCons [rule_format] :
"ALL x. ALL xs. length'(X_Cons x xs) = suc(length'(xs))"

NotDefHead [rule_format] : "~ defOp (head(Nil'))"

HeadDef [rule_format] :
"ALL x. ALL xs. head(X_Cons x xs) = makePartial x"

NotDefTail [rule_format] : "~ defOp (tail(Nil'))"

TailDef [rule_format] :
"ALL x. ALL xs. tail(X_Cons x xs) = makePartial xs"

FoldrNil [rule_format] : "ALL f. ALL s. X_foldr f s Nil' = s"

FoldrCons [rule_format] :
"ALL f.
 ALL s.
 ALL x. ALL xs. X_foldr f s (X_Cons x xs) = f x (X_foldr f s xs)"

FoldlNil [rule_format] : "ALL g. ALL t. X_foldl g t Nil' = t"

FoldlCons [rule_format] :
"ALL g.
 ALL t.
 ALL z. ALL zs. X_foldl g t (X_Cons z zs) = X_foldl g (g t z) zs"

MapNil [rule_format] : "ALL h. X_map h Nil' = Nil'"

MapCons [rule_format] :
"ALL h.
 ALL x. ALL xs. X_map h (X_Cons x xs) = X_Cons (h x) (X_map h xs)"

XPlusXPlusNil [rule_format] : "ALL l. Nil' ++' l = l"

XPlusXPlusCons [rule_format] :
"ALL l. ALL x. ALL xs. X_Cons x xs ++' l = X_Cons x (xs ++' l)"

XPlusXPlusPrefixDef [rule_format] :
"ALL xs. ALL ys. XLtXPlusXPlusXGt xs ys = xs ++' ys"

FilterNil [rule_format] : "ALL p. X_filter p Nil' = Nil'"

FilterConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x --> X_filter p (X_Cons x xs) = X_Cons x (X_filter p xs)"

FilterConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 bool2partial (p x) = undefinedOp -->
 X_filter p (X_Cons x xs) = X_filter p xs"

ZipNil [rule_format] : "ALL l. X_zip Nil' l = Nil'"

ZipConsNil [rule_format] :
"ALL l. ALL x. ALL xs. l = Nil' --> X_zip (X_Cons x xs) l = Nil'"

ZipConsCons [rule_format] :
"ALL l.
 ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 l = X_Cons y ys -->
 X_zip (X_Cons x xs) l = X_Cons (x, y) (X_zip xs ys)"

UnzipNil [rule_format] : "unzip(Nil') = (Nil', Nil')"

UnzipCons [rule_format] :
"ALL ps.
 ALL x.
 ALL z.
 unzip(X_Cons (x, z) ps) =
 (let (ys, zs) = unzip(ps) in (X_Cons x ys, X_Cons z zs))"

ILE02 [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys. X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

ILO05 [rule_format] :
"ALL w.
 ALL ws. ALL z. ALL zs. z <'' w --> X_Cons z zs <'' X_Cons w ws"

ILO06 [rule_format] :
"ALL w.
 ALL ws.
 ALL z. ALL zs. z ==' w --> X_Cons z zs <'' X_Cons w ws = zs <'' ws"

ILO07 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 bool2partial (z <'' w) = undefinedOp &
 bool2partial (z ==' w) = undefinedOp -->
 bool2partial (X_Cons z zs <'' X_Cons w ws) = undefinedOp"

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
declare Comp1 [simp]
declare IdDef [simp]
declare FlipDef [simp]
declare FstDef [simp]
declare SndDef [simp]
declare CurryDef [simp]
declare UncurryDef [simp]
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
declare IBE5 [simp]
declare IBE6 [simp]
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
declare IBO7 [simp]
declare IBO9 [simp]
declare IBO10 [simp]
declare IBO11 [simp]
declare IBO12 [simp]
declare LengthNil [simp]
declare LengthCons [simp]
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
declare ILO05 [simp]
declare ILO06 [simp]

theorem ILE01 : "Nil' ==' Nil'"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"ILE01\""

theorem ILO01 : "bool2partial (Nil' <'' Nil') = undefinedOp"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"ILO01\""

theorem ILO02 : "Nil' <='' Nil'"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"ILO02\""

theorem ILO03 : "bool2partial (Nil' >'' Nil') = undefinedOp"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"ILO03\""

theorem ILO04 : "Nil' >='' Nil'"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"ILO04\""

theorem ILO08 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 (X_Cons z zs <'' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"
apply(rule allI)+
apply(simp only: LeqDef)
done

ML "Header.record \"ILO08\""

theorem ILO09 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. X_Cons z zs >'' X_Cons w ws = X_Cons w ws <'' X_Cons z zs"
apply(rule allI)+
apply(case_tac "X_Cons z zs >'' X_Cons w ws")
apply(simp only: GeFLeFRel)
apply(simp only: GeTLeTRel)
done

ML "Header.record \"ILO09\""

theorem ILO10 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs >='' X_Cons w ws =
 (X_Cons z zs >'' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"
apply(rule allI)+
apply(simp only: GeqDef)
done

ML "Header.record \"ILO10\""

theorem ILO11 : "compare Nil' Nil' ==' EQ = Nil' ==' Nil'"
by (auto)

ML "Header.record \"ILO11\""

theorem ILO12 : "compare Nil' Nil' ==' LT = Nil' <'' Nil'"
by (auto)

ML "Header.record \"ILO12\""

theorem ILO13 : "compare Nil' Nil' ==' GT = Nil' >'' Nil'"
by (auto)

ML "Header.record \"ILO13\""

theorem ILO14 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' EQ =
 X_Cons z zs ==' X_Cons w ws"
apply(rule allI)+
apply(simp only: CmpEQDef)
done

ML "Header.record \"ILO14\""

theorem ILO15 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' LT =
 X_Cons z zs <'' X_Cons w ws"
apply(rule allI)+
apply(simp only: CmpLTDef)
done

ML "Header.record \"ILO15\""

theorem ILO16 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' GT =
 X_Cons z zs >'' X_Cons w ws"
apply(rule allI)+
apply(simp only: CmpGTDef)
done

ML "Header.record \"ILO16\""

theorem ILO17 : "X_maxX2 Nil' Nil' ==' Nil' = Nil' <='' Nil'"
by (auto)

ML "Header.record \"ILO17\""

theorem ILO18 : "X_minX2 Nil' Nil' ==' Nil' = Nil' <='' Nil'"
by (auto)

ML "Header.record \"ILO18\""

theorem ILO19 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 X_maxX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO19\""

theorem ILO20 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <='' X_Cons z zs =
 X_maxX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO20\""

theorem ILO21 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 X_minX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO21\""

theorem ILO22 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <='' X_Cons z zs =
 X_minX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO22\""

theorem FoldlDecomp :
"ALL e.
 ALL i.
 ALL ts.
 ALL ys. X_foldl i e (ys ++' ts) = X_foldl i (X_foldl i e ys) ts"
apply(auto)
apply(case_tac "ys ++' ts")
apply(auto)
apply(simp add: FoldlCons)
apply(induct_tac List)
apply(simp add: FoldlCons)
oops

ML "Header.record \"FoldlDecomp\""

theorem MapDecomp :
"ALL f.
 ALL xs. ALL zs. X_map f (xs ++' zs) = X_map f xs ++' X_map f zs"
apply(auto)
apply(induct_tac xs)
apply(auto)
apply(simp add: MapCons XPlusXPlusCons)
done

ML "Header.record \"MapDecomp\""

theorem MapFunctor :
"ALL f.
 ALL g. ALL xs. X_map (X__o__X (g, f)) xs = X_map g (X_map f xs)"
apply(auto)
apply(induct_tac xs)
apply(auto)
apply(simp add: MapNil MapCons Comp1)
done

ML "Header.record \"MapFunctor\""

theorem FilterProm :
"ALL f.
 ALL p.
 ALL xs.
 X_filter p (X_map f xs) =
 X_map f (X_filter (constTrue o X__o__X (constNil o p, f)) xs)"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"FilterProm\""

theorem LengthNil1 : "ALL xs. length'(xs) = 0' = (xs = Nil')"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"LengthNil1\""

theorem LengthEqualNil :
"ALL ys. length'(Nil') = length'(ys) --> ys = Nil'"
using X1_def_Nat X2_def_Nat X3_def_Nat X4_def_Nat X5_def_Nat
      X6_def_Nat X7_def_Nat X8_def_Nat X9_def_Nat decimal_def
by (auto)

ML "Header.record \"LengthEqualNil\""

theorem LengthEqualCons :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 length'(X_Cons x xs) = length'(X_Cons y ys) -->
 length'(xs) = length'(ys)"
by (auto)

ML "Header.record \"LengthEqualCons\""

theorem ZipSpec :
"ALL xs.
 ALL ys.
 length'(xs) = length'(ys) --> unzip(X_zip xs ys) = (xs, ys)"
oops
(*
theorem ZipSpec:
assumes "length'(xs) = length'(ys)"
 shows "unzip(X_zip xs ys) = (xs, ys)"
using assms proof (induct xs arbitrary: ys)
 fix ys
 assume "length'(Nil') = length'(ys)"
 then have "ys = Nil'" by (simp add: LengthEqualNil)
 then show "unzip(X_zip Nil' ys) = (Nil', ys)" by (simp add: ZipNil UnzipNil)
next
 fix x
 fix xs::"'a List"
 fix ys::"'b List"
 assume 1: "!!ys::'b List. length'(xs) = length'(ys) ==>
   unzip(X_zip xs ys) = (xs, ys)"
 assume 2: "length'(X_Cons x xs) = length'(ys)"
 then obtain z zs where ys: "ys = X_Cons z zs" and
   length: "length'(xs) = length'(zs)"
   sorry
 hence H: "unzip(X_zip xs zs) = (xs, zs)" using 1 by simp
 have "unzip(X_zip (X_Cons x xs) ys) = unzip(X_zip (X_Cons x xs) (X_Cons z zs))"
   using ys by simp
 also have "... = unzip(X_Cons (x, z) (X_zip xs zs))"
   by (metis ZipConsCons ys)
 also have "... = (X_Cons x xs, X_Cons z zs)"
   using H by (simp add: UnzipCons Let_def)
 also have "... = (X_Cons x xs, ys)" using ys by simp
 finally show "unzip(X_zip (X_Cons x xs) ys) = (X_Cons x xs, ys)" .
qed
*)

ML "Header.record \"ZipSpec\""

end
