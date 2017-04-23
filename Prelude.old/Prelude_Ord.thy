theory Prelude_Ord
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"IOE01\", \"IOE02\", \"IOE03\", \"IOE07\", \"IOE08\", \"IOE09\",
     \"LeTAsymmetry\", \"LeqFDef\", \"LeqReflexivity\",
     \"LeqTTransitive\", \"LeqTTotal\", \"GeIrreflexivity\",
     \"GeTAsymmetry\", \"GeTTransitive\", \"GeTTotal\",
     \"GeqReflexivity\", \"GeqTTransitive\", \"GeqTTotal\",
     \"EqFSOrdRel\", \"EqFOrdRel\", \"LeTGeTRel\", \"LeTGeqFRel\",
     \"GeTLeqFRel\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\", \"TO3\",
     \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IOO16\", \"IOO17\",
     \"IOO18\", \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\",
     \"IOO24\", \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\",
     \"IOO30\", \"IOO31\", \"IOO32\", \"IOO33\", \"IBO6\", \"IBO7\",
     \"IBO8\", \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\",
     \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\",
     \"NotFalse\", \"NotTrue\", \"AndDef1\", \"AndDef2\", \"AndDef3\",
     \"AndDef4\", \"OrDef\", \"OtherwiseDef\", \"NotTrue1\",
     \"NotFalse2\", \"TB1\", \"EqualTDef\", \"SymDef\", \"EqualSym\",
     \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"DiffTDef\",
     \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IBE1\",
     \"IBE2\", \"IBE3\", \"IBE4\", \"IBE5\", \"IBE6\", \"IBE7\",
     \"IBE8\", \"IUE1\", \"IUE2\", \"IOE04\", \"IOE05\", \"IOE06\",
     \"LeIrreflexivity\", \"LeTTransitive\", \"LeTTotal\", \"LeqDef\",
     \"GeDef\", \"GeqTDef\", \"EqTSOrdRel\", \"EqTOrdRel\",
     \"LeqTGetTRel\", \"GeTLeTRel\", \"GeqTLeqTRel\", \"LeTGeFEqFRel\",
     \"LeqTGeFRel\", \"GeTLeFEqFRel\", \"GeqTLeFRel\", \"LeLtDef\",
     \"LeEqDef\", \"LeGtDef\", \"LqLtDef\", \"LqEqDef\", \"LqGtDef\",
     \"GeLtDef\", \"GeEqDef\", \"GeGtDef\", \"GqLtDef\", \"GqEqDef\",
     \"GqGtDef\", \"MaxYDef\", \"MaxXDef\", \"MinXDef\", \"MinYDef\",
     \"IOO13\", \"IOO14\", \"IOO15\", \"IBO5\"]"

typedecl Nat
typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
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

instance Bool:: type ..
instance Nat:: type ..
instance Ordering:: type ..
instance Unit:: type ..

axioms
NotFalse [rule_format] : "Not' False' = True'"

NotTrue [rule_format] : "Not' True' = False'"

AndDef1 [rule_format] : "False' && False' = False'"

AndDef2 [rule_format] : "False' && True' = False'"

AndDef3 [rule_format] : "True' && False' = False'"

AndDef4 [rule_format] : "True' && True' = True'"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

NotTrue1 [rule_format] : "ALL x. Not' x = True' = (x = False')"

NotFalse2 [rule_format] : "ALL x. Not' x = False' = (x = True')"

TB1 [rule_format] : "~ True' = False'"

EqualTDef [rule_format] : "ALL x. ALL y. x = y --> x ==' y = True'"

SymDef [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualSym [rule_format] : "ALL x. ALL y. x ==' y = y ==' x"

EqualReflex [rule_format] : "ALL x. x ==' x = True'"

EqualTransT [rule_format] :
"ALL x.
 ALL y.
 ALL z. x ==' y = True' & y ==' z = True' --> x ==' z = True'"

DiffDef [rule_format] : "ALL x. ALL y. x /= y = Not' (x ==' y)"

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

IBE3 [rule_format] : "True' ==' False' = False'"

IBE4 [rule_format] : "False' ==' True' = False'"

IBE5 [rule_format] : "True' /= False' = True'"

IBE6 [rule_format] : "False' /= True' = True'"

IBE7 [rule_format] : "Not' (True' ==' False') = True'"

IBE8 [rule_format] : "Not' Not' (True' ==' False') = False'"

IUE1 [rule_format] : "() ==' () = True'"

IUE2 [rule_format] : "() /= () = False'"

IOE04 [rule_format] : "LT ==' EQ = False'"

IOE05 [rule_format] : "LT ==' GT = False'"

IOE06 [rule_format] : "EQ ==' GT = False'"

LeIrreflexivity [rule_format] : "ALL x. x <' x = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. x <' y = True' & y <' z = True' --> x <' z = True'"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <' y = True' | y <' x = True') | x ==' y = True'"

LeqDef [rule_format] :
"ALL x. ALL y. x <=' y = (x <' y) || (x ==' y)"

GeDef [rule_format] : "ALL x. ALL y. x >' y = y <' x"

GeqTDef [rule_format] :
"ALL x. ALL y. x >=' y = (x >' y) || (x ==' y)"

EqTSOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = Not' (x <' y) && Not' (x >' y)"

EqTOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (x <=' y) && (x >=' y)"

LeqTGetTRel [rule_format] : "ALL x. ALL y. x <=' y = y >=' x"

GeTLeTRel [rule_format] : "ALL x. ALL y. x >' y = y <' x"

GeqTLeqTRel [rule_format] : "ALL x. ALL y. x >=' y = y <=' x"

LeTGeFEqFRel [rule_format] :
"ALL x. ALL y. x <' y = Not' (x >' y) && Not' (x ==' y)"

LeqTGeFRel [rule_format] : "ALL x. ALL y. x <=' y = Not' (x >' y)"

GeTLeFEqFRel [rule_format] :
"ALL x. ALL y. x >' y = Not' (x <' y) && Not' (x ==' y)"

GeqTLeFRel [rule_format] : "ALL x. ALL y. x >=' y = Not' (x <' y)"

LeLtDef [rule_format] :
"ALL x.
 ALL y. compare x y = LT = (x <' y = True' & x ==' y = False')"

LeEqDef [rule_format] :
"ALL x.
 ALL y. compare x y = EQ = (x <' y = False' & y <' x = False')"

LeGtDef [rule_format] :
"ALL x.
 ALL y. compare x y = GT = (x >' y = True' & x ==' y = False')"

LqLtDef [rule_format] :
"ALL x.
 ALL y. (compare x y = LT | compare x y = EQ) = (x <=' y = True')"

LqEqDef [rule_format] :
"ALL x.
 ALL y. compare x y = EQ = (x <=' y = True' & y <=' x = True')"

LqGtDef [rule_format] :
"ALL x. ALL y. compare x y = GT = (x <=' y = False')"

GeLtDef [rule_format] :
"ALL x.
 ALL y. compare x y = LT = (x >' y = False' & x ==' y = False')"

GeEqDef [rule_format] :
"ALL x.
 ALL y. compare x y = EQ = (x >' y = False' & y >' x = False')"

GeGtDef [rule_format] :
"ALL x.
 ALL y. compare x y = GT = (x >' y = True' & x ==' y = False')"

GqLtDef [rule_format] :
"ALL x. ALL y. compare x y = LT = (x >=' y = False')"

GqEqDef [rule_format] :
"ALL x.
 ALL y. compare x y = EQ = (x >=' y = True' & y >=' x = True')"

GqGtDef [rule_format] :
"ALL x.
 ALL y. (compare x y = GT | compare x y = EQ) = (x >=' y = True')"

MaxYDef [rule_format] :
"ALL x. ALL y. X_max x y = y = (x <=' y = True')"

MaxXDef [rule_format] :
"ALL x. ALL y. X_max x y = x = (x >' y = True')"

MinXDef [rule_format] :
"ALL x. ALL y. X_min x y = x = (x <=' y = True')"

MinYDef [rule_format] :
"ALL x. ALL y. X_min x y = y = (x >' y = True')"

IOO13 [rule_format] : "LT <' EQ = True'"

IOO14 [rule_format] : "EQ <' GT = True'"

IOO15 [rule_format] : "LT <' GT = True'"

IBO5 [rule_format] : "False' <' True' = True'"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndDef1 [simp]
declare AndDef2 [simp]
declare AndDef3 [simp]
declare AndDef4 [simp]
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
declare IOO13 [simp]
declare IOO14 [simp]
declare IOO15 [simp]
declare IBO5 [simp]

theorem IOE01 : "LT ==' LT = True'"
by auto

ML "Header.record \"IOE01\""

theorem IOE02 : "EQ ==' EQ = True'"
by auto

ML "Header.record \"IOE02\""

theorem IOE03 : "GT ==' GT = True'"
by auto

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

theorem LeTAsymmetry :
"ALL x. ALL y. x <' y = True' --> y <' x = False'"
apply(auto)
apply(simp add: LeTGeFEqFRel)
apply(case_tac "x >' y")
apply(case_tac "x ==' y")
apply(auto)
apply(case_tac "y >' x")
apply(case_tac "y ==' x")
apply(auto)
apply(simp add: EqTOrdRel)
apply(

ML "Header.record \"LeTAsymmetry\""

theorem LeqFDef :
"ALL x. ALL y. Not' (x <=' y) = Not' (x <' y) && Not' (x ==' y)"
by auto

ML "Header.record \"LeqFDef\""

theorem LeqReflexivity : "ALL x. x <=' x = True'"
by auto

ML "Header.record \"LeqReflexivity\""

theorem LeqTTransitive :
"ALL x.
 ALL y.
 ALL z. x <=' y = True' & y <=' z = True' --> x <=' z = True'"
by auto

ML "Header.record \"LeqTTransitive\""

theorem LeqTTotal :
"ALL x. ALL y. (x <=' y) && (y <=' x) = x ==' y"
by auto

ML "Header.record \"LeqTTotal\""

theorem GeIrreflexivity : "ALL x. x >' x = False'"
by auto

ML "Header.record \"GeIrreflexivity\""

theorem GeTAsymmetry :
"ALL x. ALL y. x >' y = True' --> y >' x = False'"
by auto

ML "Header.record \"GeTAsymmetry\""

theorem GeTTransitive :
"ALL x.
 ALL y. ALL z. x >' y = True' & y >' z = True' --> x >' z = True'"
by auto

ML "Header.record \"GeTTransitive\""

theorem GeTTotal :
"ALL x. ALL y. (x >' y = True' | y >' x = True') | x ==' y = True'"
by auto

ML "Header.record \"GeTTotal\""

theorem GeqReflexivity : "ALL x. x >=' x = True'"
by auto

ML "Header.record \"GeqReflexivity\""

theorem GeqTTransitive :
"ALL x.
 ALL y.
 ALL z. x >=' y = True' & y >=' z = True' --> x >=' z = True'"
by auto

ML "Header.record \"GeqTTransitive\""

theorem GeqTTotal :
"ALL x. ALL y. (x >=' y) && (y >=' x) = x ==' y"
by auto

ML "Header.record \"GeqTTotal\""

theorem EqFSOrdRel :
"ALL x. ALL y. Not' (x ==' y) = (x <' y) || (x >' y)"
by auto

ML "Header.record \"EqFSOrdRel\""

theorem EqFOrdRel :
"ALL x. ALL y. Not' (x ==' y) = (x <=' y) || (x >=' y)"
by auto

ML "Header.record \"EqFOrdRel\""

theorem LeTGeTRel : "ALL x. ALL y. x <' y = y >' x"
by auto

ML "Header.record \"LeTGeTRel\""

theorem LeTGeqFRel : "ALL x. ALL y. x <' y = Not' (x >=' y)"
by auto

ML "Header.record \"LeTGeqFRel\""

theorem GeTLeqFRel : "ALL x. ALL y. x >' y = Not' (x <=' y)"
by auto

ML "Header.record \"GeTLeqFRel\""

theorem MaxSym : "ALL x. ALL y. X_max x y = X_max y x"
by auto

ML "Header.record \"MaxSym\""

theorem MinSym : "ALL x. ALL y. X_min x y = X_min y x"
by auto

ML "Header.record \"MinSym\""

theorem TO1 :
"ALL x.
 ALL y. (x ==' y = True' | x <' y = True') = (x <=' y = True')"
by auto

ML "Header.record \"TO1\""

theorem TO2 : "ALL x. ALL y. x ==' y = True' --> x <' y = False'"
by auto

ML "Header.record \"TO2\""

theorem TO3 :
"ALL x. ALL y. Not' Not' (x <' y) = True' | Not' (x <' y) = True'"
by auto

ML "Header.record \"TO3\""

theorem TO4 :
"ALL x. ALL y. x <' y = True' --> Not' (x ==' y) = True'"
by auto

ML "Header.record \"TO4\""

theorem TO5 :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <' y = True' & y <' z = True') & z <' w = True' -->
 x <' w = True'"
apply(auto)
thm LeTTransitive
apply(rule_tac x="x" and y="y" and z ="w" in LeTTransitive)
apply(rule conjI)
apply(assumption)
apply(rule_tac x="y" and y="z" and z ="w" in LeTTransitive)
apply(rule conjI)
apply(assumption)
apply(assumption)
done

ML "Header.record \"TO5\""

theorem TO6 :
"ALL x. ALL z. z <' x = True' --> Not' (x <' z) = True'"
by auto

ML "Header.record \"TO6\""

theorem TO7 : "ALL x. ALL y. x <' y = True' = (y >' x = True')"
by auto

ML "Header.record \"TO7\""

theorem IOO16 : "LT <=' EQ = True'"
by auto

ML "Header.record \"IOO16\""

theorem IOO17 : "EQ <=' GT = True'"
by auto

ML "Header.record \"IOO17\""

theorem IOO18 : "LT <=' GT = True'"
by auto

ML "Header.record \"IOO18\""

theorem IOO19 : "EQ >=' LT = True'"
by auto

ML "Header.record \"IOO19\""

theorem IOO20 : "GT >=' EQ = True'"
by auto

ML "Header.record \"IOO20\""

theorem IOO21 : "GT >=' LT = True'"
by auto

ML "Header.record \"IOO21\""

theorem IOO22 : "EQ >' LT = True'"
by auto

ML "Header.record \"IOO22\""

theorem IOO23 : "GT >' EQ = True'"
by auto

ML "Header.record \"IOO23\""

theorem IOO24 : "GT >' LT = True'"
by auto

ML "Header.record \"IOO24\""

theorem IOO25 : "X_max LT EQ = EQ"
by auto

ML "Header.record \"IOO25\""

theorem IOO26 : "X_max EQ GT = GT"
by auto

ML "Header.record \"IOO26\""

theorem IOO27 : "X_max LT GT = GT"
by auto

ML "Header.record \"IOO27\""

theorem IOO28 : "X_min LT EQ = LT"
by auto

ML "Header.record \"IOO28\""

theorem IOO29 : "X_min EQ GT = EQ"
by auto

ML "Header.record \"IOO29\""

theorem IOO30 : "X_min LT GT = LT"
by auto

ML "Header.record \"IOO30\""

theorem IOO31 : "compare LT LT = EQ"
by auto

ML "Header.record \"IOO31\""

theorem IOO32 : "compare EQ EQ = EQ"
by auto

ML "Header.record \"IOO32\""

theorem IOO33 : "compare GT GT = EQ"
by auto

ML "Header.record \"IOO33\""

theorem IBO6 : "False' >=' True' = False'"
by auto

ML "Header.record \"IBO6\""

theorem IBO7 : "True' >=' False' = True'"
by auto

ML "Header.record \"IBO7\""

theorem IBO8 : "True' <' False' = False'"
by auto

ML "Header.record \"IBO8\""

theorem IBO9 : "X_max False' True' = True'"
by auto

ML "Header.record \"IBO9\""

theorem IBO10 : "X_min False' True' = False'"
by auto

ML "Header.record \"IBO10\""

theorem IBO11 : "compare True' True' = EQ"
by auto

ML "Header.record \"IBO11\""

theorem IBO12 : "compare False' False' = EQ"
by auto

ML "Header.record \"IBO12\""

theorem IUO01 : "() <=' () = True'"
by auto

ML "Header.record \"IUO01\""

theorem IUO02 : "() <' () = False'"
by auto

ML "Header.record \"IUO02\""

theorem IUO03 : "() >=' () = True'"
by auto

ML "Header.record \"IUO03\""

theorem IUO04 : "() >' () = False'"
by auto

ML "Header.record \"IUO04\""

theorem IUO05 : "() = ()"
by auto

ML "Header.record \"IUO05\""

theorem IUO06 : "() = ()"
by auto

ML "Header.record \"IUO06\""

theorem IUO07 : "compare () () = EQ"
apply(simp add: LeEqDef)
done

ML "Header.record \"IUO07\""

end
