theory Prelude_Ord
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
     \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
     \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
     \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"EqualPrefixDef\",
     \"DiffPrefixDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\",
     \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\",
     \"IBE4\", \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\",
     \"IUE2\", \"IOE04\", \"IOE05\", \"IOE06\", \"LeIrreflexivity\",
     \"LeTTransitive\", \"LeTTotal\", \"GeDef\", \"LeqDef\", \"GeqDef\",
     \"EqTSOrdRel\", \"EqFSOrdRel\", \"EqTOrdRel\", \"EqFOrdRel\",
     \"EqTOrdTSubstE\", \"EqTOrdFSubstE\", \"EqTOrdTSubstD\",
     \"EqTOrdFSubstD\", \"LeTGeFEqFRel\", \"LeFGeTEqTRel\",
     \"LePrefixDef\", \"LeqPrefixDef\", \"GePrefixDef\",
     \"GeqPrefixDef\", \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\",
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
     \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\", \"TO3\", \"TO4\",
     \"TO5\", \"TO6\", \"TO7\", \"IOO16\", \"IOO17\", \"IOO18\",
     \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\",
     \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\",
     \"IOO31\", \"IOO32\", \"IOO33\", \"IBO6\", \"IBO7\", \"IBO8\",
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\", \"IUO02\",
     \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\"]"

typedecl Unit
typedecl X_Nat

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
XLtXEqXEqXGt :: "'a => 'a => Bool"
XLtXGtXEqXGt :: "'a => 'a => Bool"
XLtXGtXGt :: "'a => 'a => Bool"
XLtXLtXEqXGt :: "'a => 'a => Bool"
XLtXLtXGt :: "'a => 'a => Bool"
XLtXSlashXEqXGt :: "'a => 'a => Bool"
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XGtXEq__X :: "'a => 'a => Bool" ("(_/ >=''/ _)" [54,54] 52)
X__XGt__X :: "'a => 'a => Bool" ("(_/ >''/ _)" [54,54] 52)
X__XLtXEq__X :: "'a => 'a => Bool" ("(_/ <=''/ _)" [54,54] 52)
X__XLt__X :: "'a => 'a => Bool" ("(_/ <''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X_max :: "'a => 'a => 'a"
X_min :: "'a => 'a => 'a"
compare :: "'a => 'a => Ordering"
otherwiseH :: "Bool"

axioms
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

IOE04 [rule_format] : "LT ==' EQ = False'"

IOE05 [rule_format] : "LT ==' GT = False'"

IOE06 [rule_format] : "EQ ==' GT = False'"

LeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <' y = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. x <' y = True' & y <' z = True' --> x <' z = True'"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <' y = True' | y <' x = True') | x ==' y = True'"

GeDef [rule_format] : "ALL x. ALL y. x >' y = y <' x"

LeqDef [rule_format] :
"ALL x. ALL y. x <=' y = (x <' y) || (x ==' y)"

GeqDef [rule_format] :
"ALL x. ALL y. x >=' y = (x >' y) || (x ==' y)"

EqTSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <' y = False' & x >' y = False')"

EqFSOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <' y = True' | x >' y = True')"

EqTOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = True' = (x <=' y = True' & x >=' y = True')"

EqFOrdRel [rule_format] :
"ALL x.
 ALL y. x ==' y = False' = (x <=' y = True' | x >=' y = True')"

EqTOrdTSubstE [rule_format] :
"ALL x.
 ALL y. ALL z. x ==' y = True' & y <' z = True' --> x <' z = True'"

EqTOrdFSubstE [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y <' z = False' --> x <' z = False'"

EqTOrdTSubstD [rule_format] :
"ALL x.
 ALL y. ALL z. x ==' y = True' & z <' y = True' --> z <' x = True'"

EqTOrdFSubstD [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & z <' y = False' --> z <' x = False'"

LeTGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <' y = True' = (x >' y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <' y = False' = (x >' y = True' | x ==' y = True')"

LePrefixDef [rule_format] : "ALL x. ALL y. XLtXLtXGt x y = x <' y"

LeqPrefixDef [rule_format] :
"ALL x. ALL y. XLtXLtXEqXGt x y = x <=' y"

GePrefixDef [rule_format] : "ALL x. ALL y. XLtXGtXGt x y = x >' y"

GeqPrefixDef [rule_format] :
"ALL x. ALL y. XLtXGtXEqXGt x y = x >=' y"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' LT = x <' y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' GT = x >' y"

MaxYDef [rule_format] : "ALL x. ALL y. X_max x y ==' y = x <=' y"

MaxXDef [rule_format] : "ALL x. ALL y. X_max x y ==' x = y <=' x"

MinXDef [rule_format] : "ALL x. ALL y. X_min x y ==' x = x <=' y"

MinYDef [rule_format] : "ALL x. ALL y. X_min x y ==' y = y <=' x"

IOO13 [rule_format] : "LT <' EQ = True'"

IOO14 [rule_format] : "EQ <' GT = True'"

IOO15 [rule_format] : "LT <' GT = True'"

IBO5 [rule_format] : "False' <' True' = True'"

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

theorem IOE01 : "LT ==' LT = True'"
by (auto)

ML "Header.record \"IOE01\""

theorem IOE02 : "EQ ==' EQ = True'"
by (auto)

ML "Header.record \"IOE02\""

theorem IOE03 : "GT ==' GT = True'"
by (auto)

ML "Header.record \"IOE03\""

theorem IOE07 : "LT /= EQ = True'"
apply(simp add: DiffDef)
done

ML "Header.record \"IOE07\""

theorem IOE08 : "LT /= GT = True'"
apply(simp add: DiffDef)
done

ML "Header.record \"IOE08\""

theorem IOE09 : "EQ /= GT = True'"
apply(simp add: DiffDef)
done

ML "Header.record \"IOE09\""

lemma LeIrreflContra : " x <' x = True' ==> False"
by auto

theorem LeTAsymmetry :
"ALL x. ALL y. x <' y = True' --> y <' x = False'"
apply(auto)
apply(rule ccontr)
apply(simp add: notNot2 NotTrue1)
thm LeIrreflContra
apply(rule_tac x="x" in LeIrreflContra)
apply(rule_tac y = "y" in LeTTransitive)
by auto

ML "Header.record \"LeTAsymmetry\""

theorem GeIrreflexivity :
"ALL x. ALL y. x ==' y = True' --> x >' y = False'"
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqualSymDef LeIrreflexivity)
done

ML "Header.record \"GeIrreflexivity\""

theorem GeTAsymmetry :
"ALL x. ALL y. x >' y = True' --> y >' x = False'"
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
done

ML "Header.record \"GeTAsymmetry\""

theorem GeTTransitive :
"ALL x.
 ALL y. ALL z. (x >' y) && (y >' z) = True' --> x >' z = True'"
apply(auto)
apply(simp add: GeDef)
apply(rule_tac x="z" and y="y" and z="x" in  LeTTransitive)
apply(auto)
apply(case_tac  "z <' y")
apply(auto)
apply(case_tac  "y <' x")
apply(auto)
apply(case_tac  "y <' x")
apply(auto)
done

ML "Header.record \"GeTTransitive\""

theorem GeTTotal :
"ALL x. ALL y. ((x >' y) || (y >' x)) || (x ==' y) = True'"
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

ML "Header.record \"GeTTotal\""

theorem LeqReflexivity : "ALL x. x <=' x = True'"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
done

ML "Header.record \"LeqReflexivity\""

lemma EqualL1 [rule_format]:
"ALL x z.
 ((x ==' z) = True') & ((x ==' z) = False') \<longrightarrow> False"
by auto

lemma EqualL2 [rule_format]:
"ALL x. ALL y. ALL z.
((x ==' y) = True') & ((y ==' z) = True') \<longrightarrow> ((x ==' z) = False')\<longrightarrow> False"
apply(simp add: EqualL1)
apply(simp add: notNot2 NotTrue1)
apply(auto)
apply(rule EqualTransT)
apply(auto)
done

lemma Le1E [rule_format]:
"ALL x y z.
(y ==' x) = True' & (x <' z) = True' \<longrightarrow> (y <' z) = True'"
apply (auto)
apply(rule EqTOrdTSubstE)
apply(auto)
done

lemma Le2 [rule_format]:
"ALL x y.
(x <' y) = True' \<longrightarrow> (x <' y) = False' \<longrightarrow> False"
by auto

lemma Le3E [rule_format]:
"ALL x y z.
(y ==' x) = True' & (x <' z) = True' \<longrightarrow> (y <' z) = False' \<longrightarrow> False"
apply (auto)
apply(rule Le2)
apply(rule EqTOrdTSubstE)
apply(auto)
done

lemma Le3D [rule_format]:
"ALL x y z.
(y ==' x) = True' & (z <' x) = True' \<longrightarrow> (z <' y) = False' \<longrightarrow> False"
apply (auto)
apply(rule Le2)
apply(rule EqTOrdTSubstD)
apply(auto)
done

lemma Le4E [rule_format]:
"ALL x y z.
(y ==' x) = True' & (x <' z) = False' \<longrightarrow> (y <' z) = False'"
apply (auto)
apply(rule EqTOrdFSubstE)
apply(auto)
done

lemma Le4D [rule_format]:
"ALL x y z.
(y ==' x) = True' & (z <' x) = False' \<longrightarrow> (z <' y) = False'"
apply (auto)
apply(rule EqTOrdFSubstD)
apply(auto)
done

lemma Le5 [rule_format]:
"ALL x y.
(x <' y) = False' \<longrightarrow> (x <' y) = True' \<longrightarrow> False"
by auto

lemma Le6E [rule_format]:
"ALL x y z.
(y ==' x) = True' & (x <' z) = False' \<longrightarrow> (y <' z) = True' \<longrightarrow> False"
apply (auto)
apply(rule Le5)
apply(rule EqTOrdFSubstE)
apply(auto)
done

lemma Le7 [rule_format]:
"ALL x y.
x <' y = True' & x <' y = False' \<longrightarrow> False"
by auto

theorem LeqTTransitive :
"ALL x.
 ALL y. ALL z. (x <=' y) && (y <=' z) = True' --> x <=' z = True'"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' z")
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*Here we needed the first aux lemma*)
apply(rule EqualL2)
apply(auto)
apply(simp add: NotFalse1 NotTrue1)
apply(case_tac "Not' (x <' z)")
apply(simp add: AndFalse)
apply(simp add: NotFalse1 NotTrue1)
apply(rule ccontr)
apply(simp add: notNot1 NotFalse1)
apply(erule Le2)
apply(rule Le4E)
apply(auto)
apply(simp add: EqualSymDef)
(*End of the proof of the first thm that needed an aux lemma*)
apply(case_tac "y <' z")
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*From now on I guess the proof must be verified. It seems that I inserted some loops in the proof. *)
apply(simp add: LeTGeFEqFRel)
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqTSOrdRel)
apply(simp add: EqFSOrdRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTGeFEqFRel LeFGeTEqTRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry LeIrreflexivity LeTTotal)
apply(simp add: GeDef)+
(*
apply(simp add: GeDef)
apply(simp add: GeDef)
*)
apply(simp add: EqualSymDef LeTGeFEqFRel LeFGeTEqTRel )
apply(simp add: GeDef)
(*The real proof seems to be in the next 3 lines.*)
apply(rule Le3E)
apply(auto)
apply(simp add: EqualSymDef)+
(*
apply(simp add: EqualSymDef)
apply(simp add: EqualSymDef)
apply(simp add: EqualSymDef)
*)
(*Verify until here.*)
(*The proof for the last goal.*)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x <' z")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(drule Le5)
apply(rule LeTTransitive)
apply(auto)
done

ML "Header.record \"LeqTTransitive\""

theorem LeqTTotal :
"ALL x. ALL y. (x <=' y) && (y <=' x) = x ==' y"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: EqualSymDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: LeTAsymmetry)
done

ML "Header.record \"LeqTTotal\""

theorem GeqReflexivity : "ALL x. x >=' x = True'"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: GeDef)
apply(simp add: OrDef)
done

ML "Header.record \"GeqReflexivity\""

theorem GeqTTransitive :
"ALL x.
 ALL y. ALL z. (x >=' y) && (y >=' z) = True' --> x >=' z = True'"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef GeDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "z <' y")
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "z <' x")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*Here we needed the first aux lemma*)
apply(rule EqualL2)
apply(auto)
apply(simp add: NotFalse1 NotTrue1)
apply(case_tac "Not' (z <' x)")
apply(simp add: AndFalse)
apply(simp add: NotFalse1 NotTrue1)
apply(rule ccontr)
apply(simp add: notNot1 NotFalse1)
apply(erule Le2)
apply(rule EqTOrdFSubstD)
apply(auto)
apply(simp add: EqualSymDef)
(*End of the proof of the first thm that needed an aux lemma*)
apply(case_tac "z <' y")
apply(auto)
apply(case_tac "y ==' z")
apply(auto)
apply(case_tac "z <' x")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
(*From now on I guess the proof must be verified. It seems that I inserted some loops in the proof. *)
apply(simp add: LeTGeFEqFRel)
apply(auto)
apply(simp add: LeFGeTEqTRel)
apply(simp add: EqTSOrdRel)
apply(simp add: EqFSOrdRel)
apply(auto)
apply(simp add: GeDef)+
apply(simp add: LeFGeTEqTRel LeTGeFEqFRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry LeIrreflexivity LeTTotal)
apply(simp add: GeDef)+
apply(simp add: EqualSymDef LeTGeFEqFRel LeFGeTEqTRel )
apply(simp add: GeDef)
(*The real proof seems to be in the next 3 lines.*)
apply(rule Le3D)
apply(auto)
apply(simp add: EqualSymDef)+
(*Verify until here.*)
apply(simp add: GeDef)+
apply(simp add: LeTAsymmetry)
apply(simp add: GeDef)+
(*The proof for the last goal.*)
apply(case_tac "z <' x")
apply(auto)
apply(case_tac "x ==' z")
apply(auto)
apply(drule Le5)
apply(rule LeTTransitive)
apply(auto)
done

ML "Header.record \"GeqTTransitive\""

theorem GeqTTotal :
"ALL x. ALL y. (x >=' y) && (y >=' x) = x ==' y"
apply(auto)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: EqualSymDef)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(simp add: EqualSymDef)
apply(case_tac "y >' x")
apply(auto)
done

ML "Header.record \"GeqTTotal\""

theorem LeTGeTRel :
"ALL x. ALL y. x <' y = True' = (y >' x = True')"
apply(auto)
apply(simp add: GeDef)
apply(simp add: GeDef)
done

ML "Header.record \"LeTGeTRel\""

theorem LeFGeFRel :
"ALL x. ALL y. x <' y = False' = (y >' x = False')"
apply(auto)
apply(simp add: GeDef)
apply(simp add: GeDef)
done

ML "Header.record \"LeFGeFRel\""

theorem LeqTGetTRel :
"ALL x. ALL y. x <=' y = True' = (y >=' x = True')"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
done

ML "Header.record \"LeqTGetTRel\""

theorem LeqFGetFRel :
"ALL x. ALL y. x <=' y = False' = (y >=' x = False')"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y >' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
done

ML "Header.record \"LeqFGetFRel\""

theorem GeTLeTRel :
"ALL x. ALL y. x >' y = True' = (y <' x = True')"
apply(auto)
apply(simp add: GeDef)
apply(simp add: GeDef)
done

ML "Header.record \"GeTLeTRel\""

theorem GeFLeFRel :
"ALL x. ALL y. x >' y = False' = (y <' x = False')"
apply(auto)
apply(simp add: GeDef)
apply(simp add: GeDef)
done

ML "Header.record \"GeFLeFRel\""

theorem GeqTLeqTRel :
"ALL x. ALL y. x >=' y = True' = (y <=' x = True')"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: GeDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
done

ML "Header.record \"GeqTLeqTRel\""

theorem GeqFLeqFRel :
"ALL x. ALL y. x >=' y = False' = (y <=' x = False')"
apply(auto)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
apply(simp add: GeqDef LeqDef)
apply(simp add: OrDef)
apply(case_tac "y <' x")
apply(auto)
apply(case_tac "y ==' x")
apply(auto)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef)
apply(simp add: GeDef)
done

ML "Header.record \"GeqFLeqFRel\""

theorem LeqTGeFRel :
"ALL x. ALL y. x <=' y = True' = (x >' y = False')"
apply(auto)
apply(simp add: GeDef LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqualSymDef LeIrreflexivity)
apply(simp add: LeTAsymmetry)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqFSOrdRel)
done

ML "Header.record \"LeqTGeFRel\""

theorem LeqFGeTRel :
"ALL x. ALL y. x <=' y = False' = (x >' y = True')"
apply(auto)
apply(simp add: GeDef LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: EqTSOrdRel)
apply(simp add: GeDef LeTAsymmetry)
done

ML "Header.record \"LeqFGeTRel\""

theorem GeTLeFEqFRel :
"ALL x.
 ALL y. x >' y = True' = (x <' y = False' & x ==' y = False')"
apply(auto)
apply(simp add: GeDef LeTAsymmetry)
apply(simp add: GeDef)
apply(simp add: EqFSOrdRel)
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqFSOrdRel)
done

ML "Header.record \"GeTLeFEqFRel\""

theorem GeFLeTEqTRel :
"ALL x.
 ALL y. x >' y = False' = (x <' y = True' | x ==' y = True')"
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(simp add: notNot1)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(simp add: GeDef)
apply(simp add: EqualSymDef LeIrreflexivity)
done

ML "Header.record \"GeFLeTEqTRel\""

theorem GeqTLeFRel :
"ALL x. ALL y. x >=' y = True' = (x <' y = False')"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef)
done

ML "Header.record \"GeqTLeFRel\""

theorem GeqFLeTRel :
"ALL x. ALL y. x >=' y = False' = (x <' y = True')"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: EqFSOrdRel)
apply(simp add: GeDef)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeDef)
apply(simp add: LeTAsymmetry)
done

ML "Header.record \"GeqFLeTRel\""

theorem LeqTLeTEqTRel :
"ALL x.
 ALL y. x <=' y = True' = (x <' y = True' | x ==' y = True')"
apply(auto)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeqDef OrDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"LeqTLeTEqTRel\""

theorem LeqFLeFEqFRel :
"ALL x.
 ALL y. x <=' y = False' = (x <' y = False' & x ==' y = False')"
apply(auto)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"LeqFLeFEqFRel\""

theorem GeqTGeTEqTRel :
"ALL x.
 ALL y. x >=' y = True' = (x >' y = True' | x ==' y = True')"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeqDef OrDef)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
done

ML "Header.record \"GeqTGeTEqTRel\""

theorem GeqFGeFEqFRel :
"ALL x.
 ALL y. x >=' y = False' = (x >' y = False' & x ==' y = False')"
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(simp add: GeqDef OrDef)
apply(case_tac "x >' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: GeqDef OrDef)
done

ML "Header.record \"GeqFGeFEqFRel\""

theorem LeTGeqFRel :
"ALL x. ALL y. x <' y = True' = (x >=' y = False')"
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(simp add: GeqDef)
apply(simp add: OrDef)
apply(simp add: GeqFGeFEqFRel)
apply(simp add: LeTGeFEqFRel)
done

ML "Header.record \"LeTGeqFRel\""

theorem GeTLeqFRel :
"ALL x. ALL y. x >' y = True' = (x <=' y = False')"
apply(auto)
apply(simp add: GeTLeFEqFRel)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(simp add: LeqFLeFEqFRel)
apply(simp add: GeTLeFEqFRel)
done

ML "Header.record \"GeTLeqFRel\""

theorem LeLeqDiff : "ALL x. ALL y. x <' y = (x <=' y) && (x /= y)"
apply(auto)
apply(simp add: LeqDef OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "x /= y")
apply(auto)
apply(simp add: DiffDef)
apply(simp add: LeTGeFEqFRel)
apply(simp add: DiffDef)
done

ML "Header.record \"LeLeqDiff\""

theorem MaxSym : "ALL x. ALL y. X_max x y ==' y = X_max y x ==' y"
by (auto)

ML "Header.record \"MaxSym\""

theorem MinSym : "ALL x. ALL y. X_min x y ==' y = X_min y x ==' y"
by (auto)

ML "Header.record \"MinSym\""

theorem TO1 :
"ALL x.
 ALL y. (x ==' y = True' | x <' y = True') = (x <=' y = True')"
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: LeqDef)
apply(simp add: OrDef)
apply(case_tac "x <' y")
apply(auto)
done

ML "Header.record \"TO1\""

theorem TO2 : "ALL x. ALL y. x ==' y = True' --> x <' y = False'"
by (auto)

ML "Header.record \"TO2\""

theorem TO3 :
"ALL x. ALL y. Not' Not' (x <' y) = True' | Not' (x <' y) = True'"
apply(auto)
apply(case_tac "x <' y")
apply(auto)
done

ML "Header.record \"TO3\""

theorem TO4 :
"ALL x. ALL y. x <' y = True' --> Not' (x ==' y) = True'"
apply(auto)
apply(case_tac "x ==' y")
apply(auto)
done

ML "Header.record \"TO4\""

theorem TO5 :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <' y = True' & y <' z = True') & z <' w = True' -->
 x <' w = True'"
apply auto
apply(rule_tac y="y" in LeTTransitive)
apply auto
apply(rule_tac y="z" in LeTTransitive)
by auto

ML "Header.record \"TO5\""

theorem TO6 :
"ALL x. ALL z. z <' x = True' --> Not' (x <' z) = True'"
apply auto
apply(case_tac "x <' z")
apply auto
apply (simp add: LeTAsymmetry)
done

ML "Header.record \"TO6\""

theorem TO7 : "ALL x. ALL y. x <' y = True' = (y >' x = True')"
apply auto
apply(simp add: GeDef)+
done

ML "Header.record \"TO7\""

theorem IOO16 : "LT <=' EQ = True'"
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO16\""

theorem IOO17 : "EQ <=' GT = True'"
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO17\""

theorem IOO18 : "LT <=' GT = True'"
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO18\""

theorem IOO19 : "EQ >=' LT = True'"
apply(simp add: GeqDef OrDef GeDef)
done

ML "Header.record \"IOO19\""

theorem IOO20 : "GT >=' EQ = True'"
apply(simp add: GeqDef OrDef GeDef)
done

ML "Header.record \"IOO20\""

theorem IOO21 : "GT >=' LT = True'"
apply(simp add: GeqDef OrDef GeDef)
done

ML "Header.record \"IOO21\""

theorem IOO22 : "EQ >' LT = True'"
apply(simp add: GeDef OrDef)
done

ML "Header.record \"IOO22\""

theorem IOO23 : "GT >' EQ = True'"
apply(simp add: GeDef OrDef)
done

ML "Header.record \"IOO23\""

theorem IOO24 : "GT >' LT = True'"
apply(simp add: GeDef OrDef)
done

ML "Header.record \"IOO24\""

theorem IOO25 : "X_max LT EQ ==' EQ = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO25\""

theorem IOO26 : "X_max EQ GT ==' GT = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO26\""

theorem IOO27 : "X_max LT GT ==' GT = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO27\""

theorem IOO28 : "X_min LT EQ ==' LT = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO28\""

theorem IOO29 : "X_min EQ GT ==' EQ = True'"
apply(simp add: MinXDef)
apply(simp add: LeqDef OrDef)
done


ML "Header.record \"IOO29\""

theorem IOO30 : "X_min LT GT ==' LT = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IOO30\""

theorem IOO31 : "compare LT LT ==' EQ = True'"
by (auto)

ML "Header.record \"IOO31\""

theorem IOO32 : "compare EQ EQ ==' EQ = True'"
by (auto)

ML "Header.record \"IOO32\""

theorem IOO33 : "compare GT GT ==' EQ = True'"
by (auto)

ML "Header.record \"IOO33\""

theorem IBO6 : "False' >=' True' = False'"
apply(simp add: GeqDef OrDef GeDef)
apply (case_tac "True' <' False'")
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(simp add: GeDef)
done

ML "Header.record \"IBO6\""

theorem IBO7 : "True' >=' False' = True'"
apply(simp add: GeqDef OrDef GeDef)
done

ML "Header.record \"IBO7\""

theorem IBO8 : "True' <' False' = False'"
apply(simp add: LeFGeTEqTRel)
apply(simp add: GeDef)
done

ML "Header.record \"IBO8\""

theorem IBO9 : "X_max False' True' ==' True' = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IBO9\""

theorem IBO10 : "X_min False' True' ==' False' = True'"
apply(simp add: MaxYDef)
apply(simp add: LeqDef OrDef)
done

ML "Header.record \"IBO10\""

theorem IBO11 : "compare True' True' ==' EQ = True'"
by (auto)

ML "Header.record \"IBO11\""

theorem IBO12 : "compare False' False' ==' EQ = True'"
by (auto)

ML "Header.record \"IBO12\""

theorem IUO01 : "() <=' () = True'"
apply (simp add: LeqDef OrDef)
done

ML "Header.record \"IUO01\""

theorem IUO02 : "() <' () = False'"
by (auto)

ML "Header.record \"IUO02\""

theorem IUO03 : "() >=' () = True'"
apply(simp add: GeqDef GeDef OrDef)
done

ML "Header.record \"IUO03\""

theorem IUO04 : "() >' () = False'"
apply(simp add: GeDef)
done

ML "Header.record \"IUO04\""

theorem IUO05 : "X_max () () ==' () = True'"
by (auto)

ML "Header.record \"IUO05\""

theorem IUO06 : "X_min () () ==' () = True'"
by (auto)

ML "Header.record \"IUO06\""

theorem IUO07 : "compare () () ==' EQ = True'"
by (auto)

ML "Header.record \"IUO07\""

end
