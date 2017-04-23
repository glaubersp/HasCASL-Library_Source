theory Prelude_List_E1
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
     \"EqualTransT\", \"DiffDef\", \"EqualPrefixDef\",
     \"DiffPrefixDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\",
     \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\",
     \"IBE4\", \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\",
     \"IUE2\", \"IOE01\", \"IOE02\", \"IOE03\", \"IOE04\", \"IOE05\",
     \"IOE06\", \"IOE07\", \"IOE08\", \"IOE09\", \"LeIrreflexivity\",
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
     \"LePrefixDef\", \"LeqPrefixDef\", \"GePrefixDef\",
     \"GeqPrefixDef\", \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\",
     \"MaxYDef\", \"MaxXDef\", \"MinXDef\", \"MinYDef\", \"MaxSym\",
     \"MinSym\", \"TO1\", \"TO2\", \"TO3\", \"TO4\", \"TO5\", \"TO6\",
     \"TO7\", \"IOO13\", \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\",
     \"IOO18\", \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\",
     \"IOO24\", \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\",
     \"IOO30\", \"IOO31\", \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\",
     \"IBO7\", \"IBO8\", \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\",
     \"IUO01\", \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\",
     \"IUO07\", \"LengthNil\", \"LengthCons\", \"NotDefHead\",
     \"HeadDef\", \"NotDefTail\", \"TailDef\", \"FoldrNil\",
     \"FoldrCons\", \"FoldlNil\", \"FoldlCons\", \"MapNil\",
     \"MapCons\", \"XPlusXPlusNil\", \"XPlusXPlusCons\",
     \"XPlusXPlusPrefixDef\", \"FilterNil\", \"FilterConsT\",
     \"FilterConsF\", \"ZipNil\", \"ZipConsNil\", \"ZipConsCons\",
     \"UnzipNil\", \"UnzipCons\", \"ILE01\", \"ILE02\", \"ILO01\",
     \"ILO02\", \"ILO03\", \"ILO04\", \"ILO05\", \"ILO06\", \"ILO07\",
     \"ILO08\", \"ILO09\", \"ILO10\", \"ILO11\", \"ILO12\", \"ILO13\",
     \"ILO14\", \"ILO15\", \"ILO16\", \"ILO17\", \"ILO18\", \"ILO19\",
     \"ILO20\", \"ILO21\", \"ILO22\", \"FoldlDecomp\", \"MapDecomp\",
     \"MapFunctor\", \"FilterProm\", \"LengthNil1\", \"LengthEqualNil\",
     \"LengthEqualCons\", \"ZipSpec\", \"InitNil\", \"InitConsNil\",
     \"InitConsCons\", \"LastNil\", \"LastConsNil\", \"LastConsCons\",
     \"NullNil\", \"NullCons\", \"ReverseNil\", \"ReverseCons\",
     \"Foldr1Nil\", \"Foldr1ConsNil\", \"Foldr1ConsCons\",
     \"Foldl1Nil\", \"Foldl1ConsNil\", \"Foldl1ConsCons\", \"AndLNil\",
     \"AndLCons\", \"OrLNil\", \"OrLCons\", \"AnyDef\", \"AllDef\",
     \"ConcatDef\", \"ConcatMapDef\", \"MaximunNil\", \"MaximumDef\",
     \"MinimunNil\", \"MinimumDef\", \"TakeWhileNil\",
     \"TakeWhileConsT\", \"TakeWhileConsF\", \"DropWhileNil\",
     \"DropWhileConsT\", \"DropWhileConsF\", \"SpanNil\", \"SpanConsT\",
     \"SpanConsF\", \"BreakDef\", \"SplitAtZero\", \"SplitAtNil\",
     \"SplitAt\", \"SpanThm\", \"BreakThm\"]"

typedecl Unit

datatype X_Nat = X0 ("0''") | X_suc "X_Nat" ("suc/'(_')" [3] 999)
datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X1 :: "X_Nat" ("1''")
X2 :: "X_Nat" ("2''")
X3 :: "X_Nat" ("3''")
X4 :: "X_Nat" ("4''")
X5 :: "X_Nat" ("5''")
X6 :: "X_Nat" ("6''")
X7 :: "X_Nat" ("7''")
X8 :: "X_Nat" ("8''")
X9 :: "X_Nat" ("9''")
XLtXEqXEqXGt :: "'a => 'a => Bool"
XLtXGtXEqXGt :: "'a => 'a => Bool"
XLtXGtXGt :: "'a => 'a => Bool"
XLtXLtXEqXGt :: "'a => 'a => Bool"
XLtXLtXGt :: "'a => 'a => Bool"
XLtXPlusXPlusXGt :: "'a List => 'a List => 'a List"
XLtXSlashXEqXGt :: "'a => 'a => Bool"
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__X :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Nat => X_Nat => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "'a => 'a => Bool" ("(_/ >=''''/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Nat => X_Nat => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "'a => 'a => Bool" ("(_/ >''''/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Nat => X_Nat => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "'a => 'a => Bool" ("(_/ <=''''/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Nat => X_Nat => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "'a => 'a => Bool" ("(_/ <''''/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__X :: "X_Nat => X_Nat => X_Nat" ("(_/ +''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__X :: "X_Nat => X_Nat => X_Nat" ("(_/ *''/ _)" [54,54] 52)
X__div__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''/ _)" [54,54] 52)
X__mod__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X_all :: "('a => Bool) => 'a List => Bool"
X_andL :: "Bool List => Bool" ("andL/'(_')" [3] 999)
X_any :: "('a => Bool) => 'a List => Bool"
X_concat :: "'a List List => 'a List" ("concat''/'(_')" [3] 999)
X_curry :: "('a * 'b => 'c) => 'a => 'b => 'c"
X_dropWhile :: "('a => Bool) => 'a List => 'a List"
X_even :: "X_Nat => bool" ("even''/'(_')" [3] 999)
X_filter :: "('a => Bool) => 'a List => 'a List"
X_flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
X_foldl :: "('a => 'b => 'a) => 'a => 'b List => 'a"
X_foldr :: "('a => 'b => 'b) => 'b => 'a List => 'b"
X_fst :: "'a => 'b => 'a" ("fst''/'(_,/ _')" [3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a => 'a" ("id''/'(_')" [3] 999)
X_init :: "'a List => 'a List partial" ("init/'(_')" [3] 999)
X_last :: "'a List => 'a partial" ("last''/'(_')" [3] 999)
X_length :: "'a List => X_Nat" ("length''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_maxX1 :: "X_Nat => X_Nat => X_Nat" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "'a => 'a => 'a"
X_maximum :: "'d List => 'd partial" ("maximum/'(_')" [3] 999)
X_minX1 :: "X_Nat => X_Nat => X_Nat" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "'a => 'a => 'a"
X_minimum :: "'d List => 'd partial" ("minimum/'(_')" [3] 999)
X_null :: "'a List => Bool" ("null''/'(_')" [3] 999)
X_odd :: "X_Nat => bool" ("odd''/'(_')" [3] 999)
X_orL :: "Bool List => Bool" ("orL/'(_')" [3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_reverse :: "'a List => 'a List" ("reverse/'(_')" [3] 999)
X_snd :: "'a => 'b => 'b" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_takeWhile :: "('a => Bool) => 'a List => 'a List"
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List"
break :: "('a => Bool) => 'a List => 'a List * 'a List"
compare :: "'a => 'a => Ordering"
concatMap :: "('a => 'b List) => 'a List => 'b List"
foldl1 :: "('a => 'a => 'a) => 'a List => 'a partial"
foldr1 :: "('a => 'a => 'a) => 'a List => 'a partial"
otherwiseH :: "Bool"
span :: "('a => Bool) => 'a List => 'a List * 'a List"
splitAt :: "X_Nat => 'a List => 'a List * 'a List"
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

EqualTDef [rule_format] : "ALL x. ALL y. x = y --> x ==' y = True'"

EqualSymDef [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL x. x ==' x = True'"

EqualTransT [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y ==' z = True' --> x ==' z = True'"

DiffDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

EqualPrefixDef [rule_format] :
"ALL x. ALL y. XLtXEqXEqXGt x y = x ==' y"

DiffPrefixDef [rule_format] :
"ALL x. ALL y. XLtXSlashXEqXGt x y = x /= y"

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
"ALL x. ALL y. x ==' y = True' --> x <'' y = False'"

LeTAsymmetry [rule_format] :
"ALL x. ALL y. x <'' y = True' --> y <'' x = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. x <'' y = True' & y <'' z = True' --> x <'' z = True'"

LeTTotal [rule_format] :
"ALL x.
 ALL y. (x <'' y = True' | y <'' x = True') | x ==' y = True'"

GeDef [rule_format] : "ALL x. ALL y. x >'' y = y <'' x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x >'' y = False'"

GeTAsymmetry [rule_format] :
"ALL x. ALL y. x >'' y = True' --> y >'' x = False'"

GeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x >'' y) && (y >'' z) = True' --> x >'' z = True'"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >'' y) || (y >'' x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL x. ALL y. x <='' y = (x <'' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <='' x = True'"

LeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x <='' y) && (y <='' z) = True' --> x <='' z = True'"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <='' y) && (y <='' x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >='' y = (x >'' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >='' x = True'"

GeqTTransitive [rule_format] :
"ALL x.
 ALL y.
 ALL z. (x >='' y) && (y >='' z) = True' --> x >='' z = True'"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >='' y) && (y >='' x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <'' y = False' & x >'' y = False')"

EqFSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <'' y = True' | x >'' y = True')"

EqTOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <='' y = True' & x >='' y = True')"

EqFOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <='' y = True' | x >='' y = True')"

EqTOrdTSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <'' z = True' --> x <'' z = True'"

EqTOrdFSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <'' z = False' --> x <'' z = False'"

EqTOrdTSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <'' y = True' --> z <'' x = True'"

EqTOrdFSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <'' y = False' --> z <'' x = False'"

LeTGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <'' y = True' = (x >'' y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <'' y = False' = (x >'' y = True' | x ==' y = True')"

LeTGeTRel [rule_format] :
"ALL x. ALL y. x <'' y = True' = (y >'' x = True')"

LeFGeFRel [rule_format] :
"ALL x. ALL y. x <'' y = False' = (y >'' x = False')"

LeqTGetTRel [rule_format] :
"ALL x. ALL y. x <='' y = True' = (y >='' x = True')"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. x <='' y = False' = (y >='' x = False')"

GeTLeTRel [rule_format] :
"ALL x. ALL y. x >'' y = True' = (y <'' x = True')"

GeFLeFRel [rule_format] :
"ALL x. ALL y. x >'' y = False' = (y <'' x = False')"

GeqTLeqTRel [rule_format] :
"ALL x. ALL y. x >='' y = True' = (y <='' x = True')"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. x >='' y = False' = (y <='' x = False')"

LeqTGeFRel [rule_format] :
"ALL x. ALL y. x <='' y = True' = (x >'' y = False')"

LeqFGeTRel [rule_format] :
"ALL x. ALL y. x <='' y = False' = (x >'' y = True')"

GeTLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >'' y = True' = (x <'' y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >'' y = False' = (x <'' y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL x. ALL y. x >='' y = True' = (x <'' y = False')"

GeqFLeTRel [rule_format] :
"ALL x. ALL y. x >='' y = False' = (x <'' y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <='' y = True' = (x <'' y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <='' y = False' = (x <'' y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >='' y = True' = (x >'' y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >='' y = False' = (x >'' y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL x. ALL y. x <'' y = True' = (x >='' y = False')"

GeTLeqFRel [rule_format] :
"ALL x. ALL y. x >'' y = True' = (x <='' y = False')"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <'' y = (x <='' y) && (x /= y)"

LePrefixDef [rule_format] : "ALL x. ALL y. XLtXLtXGt x y = x <'' y"

LeqPrefixDef [rule_format] :
"ALL x. ALL y. XLtXLtXEqXGt x y = x <='' y"

GePrefixDef [rule_format] : "ALL x. ALL y. XLtXGtXGt x y = x >'' y"

GeqPrefixDef [rule_format] :
"ALL x. ALL y. XLtXGtXEqXGt x y = x >='' y"

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

TO1 [rule_format] :
"ALL x.
 ALL y. (x ==' y = True' | x <'' y = True') = (x <='' y = True')"

TO2 [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <'' y = False'"

TO3 [rule_format] :
"ALL x.
 ALL y. Not' Not' (x <'' y) = True' | Not' (x <'' y) = True'"

TO4 [rule_format] :
"ALL x. ALL y. x <'' y = True' --> Not' (x ==' y) = True'"

TO5 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <'' y = True' & y <'' z = True') & z <'' w = True' -->
 x <'' w = True'"

TO6 [rule_format] :
"ALL x. ALL z. z <'' x = True' --> Not' (x <'' z) = True'"

TO7 [rule_format] :
"ALL x. ALL y. x <'' y = True' = (y >'' x = True')"

IOO13 [rule_format] : "LT <'' EQ = True'"

IOO14 [rule_format] : "EQ <'' GT = True'"

IOO15 [rule_format] : "LT <'' GT = True'"

IOO16 [rule_format] : "LT <='' EQ = True'"

IOO17 [rule_format] : "EQ <='' GT = True'"

IOO18 [rule_format] : "LT <='' GT = True'"

IOO19 [rule_format] : "EQ >='' LT = True'"

IOO20 [rule_format] : "GT >='' EQ = True'"

IOO21 [rule_format] : "GT >='' LT = True'"

IOO22 [rule_format] : "EQ >'' LT = True'"

IOO23 [rule_format] : "GT >'' EQ = True'"

IOO24 [rule_format] : "GT >'' LT = True'"

IOO25 [rule_format] : "X_maxX2 LT EQ ==' EQ = True'"

IOO26 [rule_format] : "X_maxX2 EQ GT ==' GT = True'"

IOO27 [rule_format] : "X_maxX2 LT GT ==' GT = True'"

IOO28 [rule_format] : "X_minX2 LT EQ ==' LT = True'"

IOO29 [rule_format] : "X_minX2 EQ GT ==' EQ = True'"

IOO30 [rule_format] : "X_minX2 LT GT ==' LT = True'"

IOO31 [rule_format] : "compare LT LT ==' EQ = True'"

IOO32 [rule_format] : "compare EQ EQ ==' EQ = True'"

IOO33 [rule_format] : "compare GT GT ==' EQ = True'"

IBO5 [rule_format] : "False' <'' True' = True'"

IBO6 [rule_format] : "False' >='' True' = False'"

IBO7 [rule_format] : "True' >='' False' = True'"

IBO8 [rule_format] : "True' <'' False' = False'"

IBO9 [rule_format] : "X_maxX2 False' True' ==' True' = True'"

IBO10 [rule_format] : "X_minX2 False' True' ==' False' = True'"

IBO11 [rule_format] : "compare True' True' ==' EQ = True'"

IBO12 [rule_format] : "compare False' False' ==' EQ = True'"

IUO01 [rule_format] : "() <='' () = True'"

IUO02 [rule_format] : "() <'' () = False'"

IUO03 [rule_format] : "() >='' () = True'"

IUO04 [rule_format] : "() >'' () = False'"

IUO05 [rule_format] : "X_maxX2 () () ==' () = True'"

IUO06 [rule_format] : "X_minX2 () () ==' () = True'"

IUO07 [rule_format] : "compare () () ==' EQ = True'"

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
 p x = True' -->
 X_filter p (X_Cons x xs) = X_Cons x (X_filter p xs)"

FilterConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs. p x = False' --> X_filter p (X_Cons x xs) = X_filter p xs"

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

ILE01 [rule_format] : "Nil' ==' Nil' = True'"

ILE02 [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys. X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

ILO01 [rule_format] : "Nil' <'' Nil' = False'"

ILO02 [rule_format] : "Nil' <='' Nil' = True'"

ILO03 [rule_format] : "Nil' >'' Nil' = False'"

ILO04 [rule_format] : "Nil' >='' Nil' = True'"

ILO05 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. z <'' w = True' --> X_Cons z zs <'' X_Cons w ws = True'"

ILO06 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 z ==' w = True' --> X_Cons z zs <'' X_Cons w ws = zs <'' ws"

ILO07 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 z <'' w = False' & z ==' w = False' -->
 X_Cons z zs <'' X_Cons w ws = False'"

ILO08 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 (X_Cons z zs <'' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO09 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. X_Cons z zs >'' X_Cons w ws = X_Cons w ws <'' X_Cons z zs"

ILO10 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs >='' X_Cons w ws =
 (X_Cons z zs >'' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO11 [rule_format] : "compare Nil' Nil' ==' EQ = Nil' ==' Nil'"

ILO12 [rule_format] : "compare Nil' Nil' ==' LT = Nil' <'' Nil'"

ILO13 [rule_format] : "compare Nil' Nil' ==' GT = Nil' >'' Nil'"

ILO14 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' EQ =
 X_Cons z zs ==' X_Cons w ws"

ILO15 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' LT =
 X_Cons z zs <'' X_Cons w ws"

ILO16 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (X_Cons z zs) (X_Cons w ws) ==' GT =
 X_Cons z zs >'' X_Cons w ws"

ILO17 [rule_format] : "X_maxX2 Nil' Nil' ==' Nil' = Nil' <='' Nil'"

ILO18 [rule_format] : "X_minX2 Nil' Nil' ==' Nil' = Nil' <='' Nil'"

ILO19 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 X_maxX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

ILO20 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <='' X_Cons z zs =
 X_maxX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO21 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <='' X_Cons w ws =
 X_minX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO22 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <='' X_Cons z zs =
 X_minX2 (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

FoldlDecomp [rule_format] :
"ALL e.
 ALL i.
 ALL ts.
 ALL ys. X_foldl i e (ys ++' ts) = X_foldl i (X_foldl i e ys) ts"

MapDecomp [rule_format] :
"ALL f.
 ALL xs. ALL zs. X_map f (xs ++' zs) = X_map f xs ++' X_map f zs"

MapFunctor [rule_format] :
"ALL f.
 ALL g. ALL xs. X_map (X__o__X (g, f)) xs = X_map g (X_map f xs)"

FilterProm [rule_format] :
"ALL f.
 ALL p.
 ALL xs.
 X_filter p (X_map f xs) = X_map f (X_filter (X__o__X (p, f)) xs)"

LengthNil1 [rule_format] : "ALL xs. length'(xs) = 0' = (xs = Nil')"

LengthEqualNil [rule_format] :
"ALL ys. length'(Nil') = length'(ys) --> ys = Nil'"

LengthEqualCons [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 length'(X_Cons x xs) = length'(X_Cons y ys) -->
 length'(xs) = length'(ys)"

ZipSpec [rule_format] :
"ALL xs.
 ALL ys.
 length'(xs) = length'(ys) --> unzip(X_zip xs ys) = (xs, ys)"

InitNil [rule_format] : "~ defOp (init(Nil'))"

InitConsNil [rule_format] :
"ALL x. init(X_Cons x Nil') = makePartial Nil'"

InitConsCons [rule_format] :
"ALL x.
 ALL xs.
 init(X_Cons x xs) =
 restrictOp (makePartial (X_Cons x (makeTotal (init(xs)))))
 (defOp (init(xs)))"

LastNil [rule_format] : "~ defOp (last'(Nil'))"

LastConsNil [rule_format] :
"ALL x. last'(X_Cons x Nil') = makePartial x"

LastConsCons [rule_format] :
"ALL x. ALL xs. last'(X_Cons x xs) = last'(xs)"

NullNil [rule_format] : "null'(Nil') = True'"

NullCons [rule_format] :
"ALL x. ALL xs. null'(X_Cons x xs) = False'"

ReverseNil [rule_format] : "reverse(Nil') = Nil'"

ReverseCons [rule_format] :
"ALL x.
 ALL xs. reverse(X_Cons x xs) = reverse(xs) ++' X_Cons x Nil'"

Foldr1Nil [rule_format] : "ALL f. ~ defOp (foldr1 f Nil')"

Foldr1ConsNil [rule_format] :
"ALL f. ALL x. foldr1 f (X_Cons x Nil') = makePartial x"

Foldr1ConsCons [rule_format] :
"ALL f.
 ALL x.
 ALL xs.
 foldr1 f (X_Cons x xs) =
 restrictOp (makePartial (f x (makeTotal (foldr1 f xs))))
 (defOp (foldr1 f xs))"

Foldl1Nil [rule_format] : "ALL f. ~ defOp (foldl1 f Nil')"

Foldl1ConsNil [rule_format] :
"ALL f. ALL x. foldl1 f (X_Cons x Nil') = makePartial x"

Foldl1ConsCons [rule_format] :
"ALL f.
 ALL x.
 ALL xs.
 foldl1 f (X_Cons x xs) =
 restrictOp (makePartial (f x (makeTotal (foldr1 f xs))))
 (defOp (foldr1 f xs))"

AndLNil [rule_format] : "andL(Nil') = True'"

AndLCons [rule_format] :
"ALL b1. ALL bs. andL(X_Cons b1 bs) = b1 && andL(bs)"

OrLNil [rule_format] : "orL(Nil') = False'"

OrLCons [rule_format] :
"ALL b1. ALL bs. orL(X_Cons b1 bs) = b1 || orL(bs)"

AnyDef [rule_format] :
"ALL p. ALL xs. X_any p xs = orL(X_map p xs)"

AllDef [rule_format] :
"ALL p. ALL xs. X_all p xs = andL(X_map p xs)"

ConcatDef [rule_format] :
"ALL xxs.
 concat'(xxs) =
 X_foldr (X_curry (uncurryOp X__XPlusXPlus__X)) Nil' xxs"

ConcatMapDef [rule_format] :
"ALL g. ALL xs. concatMap g xs = concat'(X_map g xs)"

MaximunNil [rule_format] : "~ defOp (maximum(Nil'))"

MaximumDef [rule_format] :
"ALL ds. maximum(ds) = foldl1 X_maxX2 ds"

MinimunNil [rule_format] : "~ defOp (minimum(Nil'))"

MinimumDef [rule_format] :
"ALL ds. minimum(ds) = foldl1 X_minX2 ds"

TakeWhileNil [rule_format] : "ALL p. X_takeWhile p Nil' = Nil'"

TakeWhileConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x = True' -->
 X_takeWhile p (X_Cons x xs) = X_Cons x (X_takeWhile p xs)"

TakeWhileConsF [rule_format] :
"ALL p.
 ALL x. ALL xs. p x = False' --> X_takeWhile p (X_Cons x xs) = Nil'"

DropWhileNil [rule_format] : "ALL p. X_dropWhile p Nil' = Nil'"

DropWhileConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x = True' --> X_dropWhile p (X_Cons x xs) = X_dropWhile p xs"

DropWhileConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs. p x = False' --> X_dropWhile p (X_Cons x xs) = X_Cons x xs"

SpanNil [rule_format] : "ALL p. span p Nil' = (Nil', Nil')"

SpanConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x = True' -->
 span p (X_Cons x xs) =
 (let (ys, zs) = span p xs in (X_Cons x ys, zs))"

SpanConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x = False' -->
 span p (X_Cons x xs) =
 (let (ys, zs) = span p xs in (Nil', X_Cons x xs))"

BreakDef [rule_format] :
"ALL p.
 ALL xs. break p xs = (let q = X__o__X (Not__X, p) in span q xs)"

SplitAtZero [rule_format] : "ALL xs. splitAt 0' xs = (Nil', xs)"

SplitAtNil [rule_format] :
"ALL X_n. splitAt X_n Nil' = (Nil', Nil')"

SplitAt [rule_format] :
"ALL X_n.
 ALL nx.
 ALL x.
 ALL xs.
 defOp (pre(X_n)) & makePartial nx = pre(X_n) -->
 splitAt X_n (X_Cons x xs) =
 (let (ys, zs) = splitAt nx xs in (X_Cons x ys, zs))"

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
declare ILE01 [simp]
declare ILO01 [simp]
declare ILO02 [simp]
declare ILO03 [simp]
declare ILO04 [simp]
declare ILO05 [simp]
declare ILO06 [simp]
declare ILO11 [simp]
declare ILO12 [simp]
declare ILO13 [simp]
declare ILO14 [simp]
declare ILO15 [simp]
declare ILO16 [simp]
declare ILO17 [simp]
declare ILO18 [simp]
declare InitNil [simp]
declare InitConsNil [simp]
declare LastNil [simp]
declare LastConsNil [simp]
declare LastConsCons [simp]
declare NullNil [simp]
declare NullCons [simp]
declare ReverseNil [simp]
declare Foldr1Nil [simp]
declare Foldr1ConsNil [simp]
declare Foldl1Nil [simp]
declare Foldl1ConsNil [simp]
declare AndLNil [simp]
declare OrLNil [simp]
declare MaximunNil [simp]
declare MinimunNil [simp]
declare TakeWhileNil [simp]
declare TakeWhileConsF [simp]
declare DropWhileNil [simp]
declare DropWhileConsT [simp]
declare DropWhileConsF [simp]
declare SpanNil [simp]
declare SplitAtZero [simp]
declare SplitAtNil [simp]

theorem SpanThm :
"ALL p. ALL xs. span p xs = (X_takeWhile p xs, X_dropWhile p xs)"
apply(auto)
apply(case_tac xs)
apply(auto)
apply(induct_tac List)
apply(case_tac "p a")
apply(simp add: TakeWhileConsF DropWhileConsF SpanConsF)
apply(case_tac "p aa")
apply(simp add: TakeWhileConsT DropWhileConsT SpanConsT TakeWhileConsF DropWhileConsF SpanConsF TakeWhileNil DropWhileNil SpanNil)+
apply(simp only: Let_def)
apply(simp add: split_def)
apply(case_tac "p a")
apply(simp add: TakeWhileConsT DropWhileConsT SpanConsT TakeWhileConsF DropWhileConsF SpanConsF TakeWhileNil DropWhileNil SpanNil)+
done

ML "Header.record \"SpanThm\""

theorem BreakThm :
"ALL p. ALL xs. break p xs = span (X__o__X (Not__X, p)) xs"
apply(auto)
apply(case_tac xs)
apply(auto)
apply(simp add: BreakDef)
apply(simp add: Let_def)
apply(simp add: BreakDef)
done

ML "Header.record \"BreakThm\""

end
