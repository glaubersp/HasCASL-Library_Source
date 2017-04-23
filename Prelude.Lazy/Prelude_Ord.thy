theory Prelude_Ord
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
        \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
        \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
        \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"DiffSymDef\",
        \"DiffTDef\", \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\",
        \"IUE1\", \"IUE2\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\",
        \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IOE04\", \"IOE05\",
        \"IOE06\", \"LeIrreflexivity\", \"LeTTransitive\", \"LeTTotal\",
        \"GeDef\", \"LeqDef\", \"GeqDef\", \"EqTSOrdRel\", \"EqFSOrdRel\",
        \"EqTOrdRel\", \"EqFOrdRel\", \"EqTOrdTSubstE\", \"EqTOrdFSubstE\",
        \"EqTOrdTSubstD\", \"EqTOrdFSubstD\", \"LeTGeFEqFRel\",
        \"LeFGeTEqTRel\", \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\",
        \"MaxYDef\", \"MaxXDef\", \"MinXDef\", \"MinYDef\", \"IOO13\",
        \"IOO14\", \"IOO15\", \"IBO5\", \"IOE01\", \"IOE02\", \"IOE03\",
        \"IOE07\", \"IOE08\", \"IOE09\", \"LeTAsymmetry\",
        \"GeIrreflexivity\", \"GeTAsymmetry\", \"GeTTransitive\",
        \"GeTTotal\", \"LeqReflexivity\", \"LeqTTransitive\",
        \"LeqTTotal\", \"GeqReflexivity\", \"GeqTTransitive\",
        \"GeqTTotal\", \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\",
        \"LeqFGetFRel\", \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\",
        \"GeqFLeqFRel\", \"LeqTGeFRel\", \"LeqFGeTRel\", \"GeTLeFEqFRel\",
        \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
        \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
        \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
        \"MaxSym\", \"MinSym\", \"TO1\", \"TO3\", \"TO4\", \"TO5\",
        \"TO6\", \"IUO01\", \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\",
        \"IUO06\", \"IUO07\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\",
        \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\",
        \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\",
        \"IOO32\", \"IOO33\", \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\",
        \"IBO10\", \"IBO11\", \"IBO12\"]"

typedecl Bool
typedecl Unit
typedecl X_Nat

datatype Ordering = EQ | GT | LT

consts
X__XAmpXAmp__X :: "bool => bool => bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a partial => 'a partial => bool" ("(_/ ==''/ _)" [54,54] 52)
X__XGtXEq__X :: "'a partial => 'a partial => bool" ("(_/ >=''/ _)" [54,54] 52)
X__XGt__X :: "'a partial => 'a partial => bool" ("(_/ >''/ _)" [54,54] 52)
X__XLtXEq__X :: "'a partial => 'a partial => bool" ("(_/ <=''/ _)" [54,54] 52)
X__XLt__X :: "'a partial => 'a partial => bool" ("(_/ <''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a partial => 'a partial => bool" ("(_/ '/=/ _)" [54,54] 52)
X__XVBarXVBar__X :: "bool => bool => bool" ("(_/ ||/ _)" [54,54] 52)
X_max :: "'a partial => 'a partial => 'a partial"
X_min :: "'a partial => 'a partial => 'a partial"
compare :: "'a partial => 'a partial => Ordering partial"
notH__X :: "bool => bool" ("(notH/ _)" [56] 56)
otherwiseH :: "bool"

axioms
NotFalse [rule_format] : "notH False"

NotTrue [rule_format] : "~ notH True"

AndFalse [rule_format] : "ALL (x :: bool). ~ False && x"

AndTrue [rule_format] : "ALL (x :: bool). True && x = x"

AndSym [rule_format] :
"ALL (x :: bool). ALL (y :: bool). x && y = y && x"

OrDef [rule_format] :
"ALL (x :: bool).
 ALL (y :: bool). x || y = notH (notH x && notH y)"

OtherwiseDef [rule_format] : "otherwiseH"

NotFalse1 [rule_format] : "ALL (x :: bool). notH x = (~ x)"

NotTrue1 [rule_format] : "ALL (x :: bool). ~ notH x = x"

notNot1 [rule_format] : "ALL (x :: bool). (~ x) = notH x"

notNot2 [rule_format] : "ALL (x :: bool). (~ ~ x) = (~ notH x)"

EqualTDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x = y --> x ==' y"

EqualSymDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL (x :: 'a partial). x ==' x"

EqualTransT [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & y ==' z --> x ==' z"

DiffDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x /= y = notH (x ==' y)"

DiffSymDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x /= y = y /= x"

DiffTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x /= y = notH (x ==' y)"

DiffFDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x /= y) = x ==' y"

TE1 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). ~ x ==' y --> ~ x = y"

TE2 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). notH (x ==' y) = (~ x ==' y)"

TE3 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ notH (x ==' y)) = x ==' y"

TE4 [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (~ x ==' y)"

IUE1 [rule_format] : "makePartial () ==' makePartial ()"

IUE2 [rule_format] : "~ makePartial () /= makePartial ()"

IBE1 [rule_format] : "makePartial () ==' makePartial ()"

IBE2 [rule_format] : "undefinedOp ==' undefinedOp"

IBE3 [rule_format] : "~ undefinedOp ==' makePartial ()"

IBE4 [rule_format] : "~ makePartial () ==' undefinedOp"

IBE5 [rule_format] : "makePartial () /= undefinedOp"

IBE6 [rule_format] : "undefinedOp /= makePartial ()"

IBE7 [rule_format] : "notH (makePartial () ==' undefinedOp)"

IBE8 [rule_format] : "~ notH notH (makePartial () ==' undefinedOp)"

IOE04 [rule_format] : "~ makePartial LT ==' makePartial EQ"

IOE05 [rule_format] : "~ makePartial LT ==' makePartial GT"

IOE06 [rule_format] : "~ makePartial EQ ==' makePartial GT"

LeIrreflexivity [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y --> ~ x <' y"

LeTTransitive [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x <' y & y <' z --> x <' z"

LeTTotal [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x <' y | y <' x) | x ==' y"

GeDef [rule_format] :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >' y = y <' x"

LeqDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=' y = (x <' y) || (x ==' y)"

GeqDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=' y = (x >' y) || (x ==' y)"

EqTSOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y = (~ x <' y & ~ x >' y)"

EqFSOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (x <' y | x >' y)"

EqTOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y = (x <=' y & x >=' y)"

EqFOrdRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x ==' y) = (x <=' y | x >=' y)"

EqTOrdTSubstE [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & y <' z --> x <' z"

EqTOrdFSubstE [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & ~ y <' z --> ~ x <' z"

EqTOrdTSubstD [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & z <' y --> z <' x"

EqTOrdFSubstD [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). x ==' y & ~ z <' y --> ~ z <' x"

LeTGeFEqFRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <' y = (~ x >' y & ~ x ==' y)"

LeFGeTEqTRel [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <' y) = (x >' y | x ==' y)"

CmpLTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial LT = x <' y"

CmpEQDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). compare x y ==' makePartial GT = x >' y"

MaxYDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_max x y ==' y = x <=' y"

MaxXDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_max x y ==' x = y <=' x"

MinXDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_min x y ==' x = x <=' y"

MinYDef [rule_format] :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_min x y ==' y = y <=' x"

IOO13 [rule_format] : "makePartial LT <' makePartial EQ"

IOO14 [rule_format] : "makePartial EQ <' makePartial GT"

IOO15 [rule_format] : "makePartial LT <' makePartial GT"

IBO5 [rule_format] : "undefinedOp <' makePartial ()"

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
declare IOE04 [simp]
declare IOE05 [simp]
declare IOE06 [simp]
declare LeIrreflexivity [simp]
declare CmpLTDef [simp]
declare CmpEQDef [simp]
declare CmpGTDef [simp]
declare MaxYDef [simp]
declare MaxXDef [simp]
declare MinXDef [simp]
declare MinYDef [simp]
declare IOO13 [simp]
declare IOO14 [simp]
declare IOO15 [simp]
declare IBO5 [simp]

theorem IOE01 : "makePartial LT ==' makePartial LT"
by (auto)

setup "Header.record \"IOE01\""

theorem IOE02 : "makePartial EQ ==' makePartial EQ"
by (auto)

setup "Header.record \"IOE02\""

theorem IOE03 : "makePartial GT ==' makePartial GT"
by (auto)

setup "Header.record \"IOE03\""

theorem IOE07 : "makePartial LT /= makePartial EQ"
apply(simp add: DiffDef)
done

setup "Header.record \"IOE07\""

theorem IOE08 : "makePartial LT /= makePartial GT"
apply(simp add: DiffDef)
done

setup "Header.record \"IOE08\""

theorem IOE09 : "makePartial EQ /= makePartial GT"
apply(simp add: DiffDef)
done

setup "Header.record \"IOE09\""

lemma LeIrreflContra : " x <' x ==> False"
by (auto)

theorem LeTAsymmetry :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <' y --> ~ y <' x"
apply(auto)
apply(rule ccontr)
apply(simp add: notNot2 NotTrue1)
apply(rule_tac x="x" in LeIrreflContra)
apply(rule_tac y = "y" in LeTTransitive)
by (auto)

setup "Header.record \"LeTAsymmetry\""

theorem GeIrreflexivity :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x ==' y --> ~ x >' y"
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqualSymDef LeTAsymmetry)
done

setup "Header.record \"GeIrreflexivity\""

theorem GeTAsymmetry :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >' y --> ~ y >' x"
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqualSymDef LeTAsymmetry)
done

setup "Header.record \"GeTAsymmetry\""

theorem GeTTransitive :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x >' y) && (y >' z) --> x >' z"
apply(auto)
apply(simp add: GeDef)
apply(rule_tac x="z" and y="y" and z="x" in  LeTTransitive)
apply(auto)
apply(case_tac  "y <' x")
apply(auto)
apply(case_tac  "y <' x")
by(auto)

setup "Header.record \"GeTTransitive\""

theorem GeTTotal :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). ((x >' y) || (y >' x)) || (x ==' y)"
apply(auto)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeFGeTEqTRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(simp add: EqualSymDef)
done

setup "Header.record \"GeTTotal\""

theorem LeqReflexivity : "ALL (x :: 'a partial). x <=' x"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
done

setup "Header.record \"LeqReflexivity\""

lemma EqualL1 [rule_format]:
"ALL a b ab bb.
 (x ==' z) & ~ (x ==' z) \<longrightarrow> False"
by(auto)

lemma EqualL2 [rule_format]:
"ALL a b aa ab ba bb.
(x ==' y) & (y ==' z) \<longrightarrow> ~ (x ==' z) \<longrightarrow> False"
apply(simp add: EqualL1)
apply(auto)
apply(rule EqualTransT)
by(auto)

lemma EqualL3 [rule_format]:
"ALL a b aa ab ba bb.
~ (x ==' y) | ~ (y ==' z) | ~ (x ==' z) \<longrightarrow> False \<longrightarrow> False"
by(auto)

lemma Le1E [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & (x <' z) \<longrightarrow> (y <' z)"
apply (auto)
apply(rule EqTOrdTSubstE)
by(auto)

lemma Le2 [rule_format]:
"ALL a b aa ab ba bb.
(x <' y) \<longrightarrow> ~ (x <' y) \<longrightarrow> False"
by auto

lemma Le3E [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & (x <' z) \<longrightarrow> ~ (y <' z) \<longrightarrow> False"
apply (auto)
apply(rule EqTOrdTSubstE)
by(auto)

lemma Le3D [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & (z <' x) \<longrightarrow> ~ (z <' y) \<longrightarrow> False"
apply (auto)
apply(rule EqTOrdTSubstD)
apply(auto)
done

lemma Le4E [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & ~ (x <' z) \<longrightarrow> ~ (y <' z)"
apply (auto)
apply(rule Le3E)
apply(auto)
apply(simp add: EqualSymDef)
done

lemma Le4D [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & ~ (z <' x) \<longrightarrow> ~ (z <' y)"
apply (auto)
apply(rule Le3D)
apply(auto)
apply(simp add: EqualSymDef)
done

lemma Le5 [rule_format]:
"ALL a b aa ab ba bb.
~ (x <' y) \<longrightarrow> (x <' y) \<longrightarrow> False"
by auto

lemma Le6E [rule_format]:
"ALL a b aa ab ba bb.
(y ==' x) & ~ (x <' z) \<longrightarrow> (y <' z) \<longrightarrow> False"
apply (auto)
apply(rule Le5)
apply(rule EqTOrdFSubstE)
apply(auto)
done

lemma Le7 [rule_format]:
"ALL a b aa ab ba bb.
x <' y & ~ x <' y \<longrightarrow> False"
by auto

lemma Le8 [rule_format]:
"ALL a b aa ab ba bb.
z ==' y & x <' y \<longrightarrow> x <' z"
apply auto
apply(rule EqTOrdTSubstD)
apply(rule conjI)
by(auto)

lemma Le9 [rule_format]:
"ALL a b aa ab ba bb.
x <' y & y ==' z \<longrightarrow> ~ x <' z \<longrightarrow> False"
apply auto
apply(rule Le8)
apply(auto)
apply (simp add: EqualSymDef)
done

lemma Le10 [rule_format]:
"ALL a b aa ab ba bb.
y <' z & x ==' y \<longrightarrow> ~ x <' z \<longrightarrow> False"
apply auto
apply(rule EqTOrdTSubstE)
apply(rule conjI)
by(auto)

lemma Le11 [rule_format]:
"ALL a b aa ab ba bb.
z <' y & y <' x \<longrightarrow> ~ z <' x \<longrightarrow> False"
apply(auto)
apply(rule LeTTransitive)
apply(auto)
done

lemma Le12 [rule_format]:
"ALL a b aa ab ba bb.
y <' x & y ==' z \<longrightarrow> ~ z <' x \<longrightarrow> False"
apply(auto)
apply(rule EqTOrdTSubstE)
apply(rule conjI)
apply(auto)
apply(simp add: EqualSymDef)
done

lemma Le13 [rule_format]:
"ALL a b aa ab ba bb.
x <' z & z <' y \<longrightarrow> ~ x <' y \<longrightarrow> False"
apply(auto)
apply(rule LeTTransitive)
apply(rule conjI)
apply(auto)
done

lemma Le14 [rule_format]:
"ALL a b aa ab ba bb.
~ x <' x"
by(auto)

lemma Le15 [rule_format]:
"ALL a b aa ab ba bb.
x <' z & z <' y \<longrightarrow> x <' y & y <' x \<longrightarrow> False"
apply(auto)
apply(simp add: LeTAsymmetry)
done

lemma Le16 [rule_format]:
"ALL a b aa ab ba bb.
x ==' y & z <' y \<longrightarrow> z <' x & ~ z <' x \<longrightarrow> False"
by(auto)

lemma Le17 [rule_format]:
"ALL a b aa ab ba bb.
z <' y & x ==' y \<longrightarrow> z <' x"
apply(auto)
apply(rule EqTOrdTSubstD)
apply(rule conjI)
apply(auto)
done

lemma Le18 [rule_format]:
"ALL a b aa ab ba bb.
x <' z & ~ x <' z \<longrightarrow> False"
by(auto)

lemma Le19 [rule_format]:
"ALL a b aa ab ba bb.
x ==' y & y <' z \<longrightarrow> ~ x <' z \<longrightarrow> False"
apply(auto)
apply(rule EqTOrdTSubstE)
apply(auto)
done

lemma Le20 [rule_format]:
"ALL a b aa ab ba bb.
x ==' y & z <' y \<longrightarrow> ~ z <' x \<longrightarrow> False"
apply(auto)
apply(rule EqTOrdTSubstD)
apply(auto)
done

theorem LeqTTransitive :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x <=' y) && (y <=' z) --> x <=' z"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "y <' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*Here we needed the first aux lemma*)
apply(rule Le18)
apply(rule conjI)
apply(rule LeTTransitive)
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(rule Le9)
apply(rule conjI)
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(rule Le19)
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(rule EqualL2)
by(auto)

setup "Header.record \"LeqTTransitive\""

theorem LeqTTotal :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x <=' y) && (y <=' x) = x ==' y"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(simp add: LeTAsymmetry)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef EqualL1)
done

setup "Header.record \"LeqTTotal\""

theorem GeqReflexivity : "ALL (x :: 'a partial). x >=' x"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(simp add: AndSym)
done

setup "Header.record \"GeqReflexivity\""

theorem GeqTTransitive :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x >=' y) && (y >=' z) --> x >=' z"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y >' z")
apply(auto)
apply(case_tac "x >' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*Here we needed the first aux lemma*)
apply(simp add: GeDef)
apply(rule Le18)
apply(rule conjI)
apply(rule LeTTransitive)
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x >' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(simp add: GeDef)
apply(rule Le10)
apply(rule conjI)
apply(simp add: EqualSymDef)+
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' z")
apply(auto)
apply(case_tac "x >' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(simp add: GeDef)
apply(rule Le20)
apply(rule conjI)
apply(simp add: EqualSymDef)+
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x >' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(rule EqualL2)
by(auto)

setup "Header.record \"GeqTTransitive\""

theorem GeqTTotal :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x >=' y) && (y >=' x) = x ==' y"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef EqualL1)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef EqualL1)
done

setup "Header.record \"GeqTTotal\""

theorem LeTGeTRel :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <' y = y >' x"
apply(auto)
apply(simp add: GeDef)+
done

setup "Header.record \"LeTGeTRel\""

theorem LeFGeFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <' y) = (~ y >' x)"
apply(auto)
apply(simp add: GeDef)+
done

setup "Header.record \"LeFGeFRel\""

theorem LeqTGetTRel :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x <=' y = y >=' x"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
done

setup "Header.record \"LeqTGetTRel\""

theorem LeqFGetFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=' y) = (~ y >=' x)"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
done

setup "Header.record \"LeqFGetFRel\""

theorem GeTLeTRel :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >' y = y <' x"
apply(auto)
apply(simp add: GeDef)+
done

setup "Header.record \"GeTLeTRel\""

theorem GeFLeFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >' y) = (~ y <' x)"
apply(auto)
apply(simp add: GeDef)+
done

setup "Header.record \"GeFLeFRel\""

theorem GeqTLeqTRel :
"ALL (x :: 'a partial). ALL (y :: 'a partial). x >=' y = y <=' x"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
done

setup "Header.record \"GeqTLeqTRel\""

theorem GeqFLeqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=' y) = (~ y <=' x)"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
done

setup "Header.record \"GeqFLeqFRel\""

theorem LeqTGeFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=' y = (~ x >' y)"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqualSymDef)
apply(simp add: GeDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(simp add: GeDef)
done

setup "Header.record \"LeqTGeFRel\""

theorem LeqFGeTRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=' y) = x >' y"
apply(auto)
apply(simp add: GeDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef)
apply(simp add: GeDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef LeTAsymmetry)
done

setup "Header.record \"LeqFGeTRel\""

theorem GeTLeFEqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >' y = (~ x <' y & ~ x ==' y)"
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(simp add: GeDef)
apply(simp add: EqualSymDef LeTAsymmetry)
apply(simp add: EqFSOrdRel)
done

setup "Header.record \"GeTLeFEqFRel\""

theorem GeFLeTEqTRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >' y) = (x <' y | x ==' y)"
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(simp add: GeDef LeTAsymmetry)
apply(simp add: GeDef)
apply(simp add: EqualSymDef)
done

setup "Header.record \"GeFLeTEqTRel\""

theorem GeqTLeFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=' y = (~ x <' y)"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef LeTAsymmetry)
done

setup "Header.record \"GeqTLeFRel\""

theorem GeqFLeTRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=' y) = x <' y"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef LeTAsymmetry)
apply(rule disjE)
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(case_tac "x ==' y")
by(auto)

setup "Header.record \"GeqFLeTRel\""

theorem LeqTLeTEqTRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <=' y = (x <' y | x ==' y)"
apply(auto)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: LeqDef OrDef LeTAsymmetry)+
done

setup "Header.record \"LeqTLeTEqTRel\""

theorem LeqFLeFEqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x <=' y) = (~ x <' y & ~ x ==' y)"
apply(auto)
apply(simp add: LeqDef OrDef)+
done

setup "Header.record \"LeqFLeFEqFRel\""

theorem GeqTGeTEqTRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >=' y = (x >' y | x ==' y)"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeqDef OrDef)+
apply(case_tac "x >' y")
apply(auto)
done

setup "Header.record \"GeqTGeTEqTRel\""

theorem GeqFGeFEqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (~ x >=' y) = (~ x >' y & ~ x ==' y)"
apply(auto)
apply(simp add: GeqDef OrDef)+
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeqDef OrDef)+
done

setup "Header.record \"GeqFGeFEqFRel\""

theorem LeTGeqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <' y = (~ x >=' y)"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef LeTAsymmetry)
apply(rule disjE)
by(auto)

setup "Header.record \"LeTGeqFRel\""

theorem GeTLeqFRel :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x >' y = (~ x <=' y)"
apply(auto)
apply(simp add: GeDef LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: LeTAsymmetry)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef LeTAsymmetry)
done

setup "Header.record \"GeTLeqFRel\""

theorem LeLeqDiff :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <' y = (x <=' y) && (x /= y)"
apply(auto)
apply(simp add: LeqDef OrDef)
apply(simp add: DiffDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeqDef OrDef)
apply(simp add: DiffDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
done

setup "Header.record \"LeLeqDiff\""

theorem MaxSym :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_max x y ==' y = X_max y x ==' y"
by (auto)

setup "Header.record \"MaxSym\""

theorem MinSym :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). X_min x y ==' y = X_min y x ==' y"
by (auto)

setup "Header.record \"MinSym\""

theorem TO1 :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). (x ==' y | x <' y) = x <=' y"
apply(auto)
apply(simp add: LeqDef OrDef)+
apply(case_tac "x ==' y")
apply(auto)
done

setup "Header.record \"TO1\""

theorem TO3 :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). notH notH (x <' y) | notH (x <' y)"
by (auto)

setup "Header.record \"TO3\""

theorem TO4 :
"ALL (x :: 'a partial).
 ALL (y :: 'a partial). x <' y --> notH (x ==' y)"
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
done

setup "Header.record \"TO4\""

theorem TO5 :
"ALL (w :: 'a partial).
 ALL (x :: 'a partial).
 ALL (y :: 'a partial).
 ALL (z :: 'a partial). (x <' y & y <' z) & z <' w --> x <' w"
apply(auto)
apply(rule_tac y="z" in LeTTransitive)
apply(auto)
apply(rule_tac y="y" in LeTTransitive)
by auto

setup "Header.record \"TO5\""

theorem TO6 :
"ALL (x :: 'a partial).
 ALL (z :: 'a partial). z <' x --> notH (x <' z)"
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(simp add: LeTAsymmetry)
done

setup "Header.record \"TO6\""

theorem IUO01 : "makePartial () <=' makePartial ()"
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IUO01\""

theorem IUO02 : "~ makePartial () <' makePartial ()"
by (auto)

setup "Header.record \"IUO02\""

theorem IUO03 : "makePartial () >=' makePartial ()"
apply(simp add: GeqDef OrDef)
apply(case_tac "makePartial () >' makePartial ()")
apply(auto)
done

setup "Header.record \"IUO03\""

theorem IUO04 : "~ makePartial () >' makePartial ()"
apply(simp add: GeDef)
done

setup "Header.record \"IUO04\""

theorem IUO05 :
"X_max (makePartial ()) (makePartial ()) ==' makePartial ()"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IUO05\""

theorem IUO06 :
"X_min (makePartial ()) (makePartial ()) ==' makePartial ()"
apply(simp add: MinXDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IUO06\""

theorem IUO07 :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"
by (auto)

setup "Header.record \"IUO07\""

theorem IOO16 : "makePartial LT <=' makePartial EQ"
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO16\""

theorem IOO17 : "makePartial EQ <=' makePartial GT"
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO17\""

theorem IOO18 : "makePartial LT <=' makePartial GT"
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO18\""

theorem IOO19 : "makePartial EQ >=' makePartial LT"
apply(simp add: GeqDef OrDef GeDef)
done

setup "Header.record \"IOO19\""

theorem IOO20 : "makePartial GT >=' makePartial EQ"
apply(simp add: GeqDef OrDef GeDef)
done

setup "Header.record \"IOO20\""

theorem IOO21 : "makePartial GT >=' makePartial LT"
apply(simp add: GeqDef OrDef GeDef)
done

setup "Header.record \"IOO21\""

theorem IOO22 : "makePartial EQ >' makePartial LT"
apply(simp add: GeDef OrDef)
done

setup "Header.record \"IOO22\""

theorem IOO23 : "makePartial GT >' makePartial EQ"
apply(simp add: GeDef OrDef)
done

setup "Header.record \"IOO23\""

theorem IOO24 : "makePartial GT >' makePartial LT"
apply(simp add: GeDef OrDef)
done

setup "Header.record \"IOO24\""

theorem IOO25 :
"X_max (makePartial LT) (makePartial EQ) ==' makePartial EQ"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO25\""

theorem IOO26 :
"X_max (makePartial EQ) (makePartial GT) ==' makePartial GT"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO26\""

theorem IOO27 :
"X_max (makePartial LT) (makePartial GT) ==' makePartial GT"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO27\""

theorem IOO28 :
"X_min (makePartial LT) (makePartial EQ) ==' makePartial LT"
apply(simp add: MinXDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO28\""

theorem IOO29 :
"X_min (makePartial EQ) (makePartial GT) ==' makePartial EQ"
apply(simp add: MinXDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO29\""

theorem IOO30 :
"X_min (makePartial LT) (makePartial GT) ==' makePartial LT"
apply(simp add: MinXDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IOO30\""

theorem IOO31 :
"compare (makePartial LT) (makePartial LT) ==' makePartial EQ"
by (auto)

setup "Header.record \"IOO31\""

theorem IOO32 :
"compare (makePartial EQ) (makePartial EQ) ==' makePartial EQ"
by (auto)

setup "Header.record \"IOO32\""

theorem IOO33 :
"compare (makePartial GT) (makePartial GT) ==' makePartial EQ"
by (auto)

setup "Header.record \"IOO33\""

theorem IBO6 : "~ undefinedOp >=' makePartial ()"
apply(simp add: GeqDef OrDef GeDef)
apply (case_tac "makePartial () <' undefinedOp")
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(simp add: GeDef)
done

setup "Header.record \"IBO6\""

theorem IBO7 : "makePartial () >=' undefinedOp"
apply(simp add: GeqDef OrDef GeDef)
done

setup "Header.record \"IBO7\""

theorem IBO8 : "~ makePartial () <' undefinedOp"
apply(simp add: LeFGeTEqTRel)
apply(simp add: GeDef)
done

setup "Header.record \"IBO8\""

theorem IBO9 :
"X_max undefinedOp (makePartial ()) ==' makePartial ()"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IBO9\""

theorem IBO10 :
"X_min undefinedOp (makePartial ()) ==' undefinedOp"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

setup "Header.record \"IBO10\""

theorem IBO11 :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"
by (auto)

setup "Header.record \"IBO11\""

theorem IBO12 :
"compare undefinedOp undefinedOp ==' makePartial EQ"
by (auto)

setup "Header.record \"IBO12\""

end
