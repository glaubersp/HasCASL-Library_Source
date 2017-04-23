theory Prelude_Bounded
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Ax1\", \"Ax2\", \"Ax3\", \"Ax4\", \"NotFalse\", \"NotTrue\",
     \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
     \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\",
     \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\", \"EqualTransT\",
     \"DiffDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\",
     \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\", \"IBE5\",
     \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\", \"IOE01\",
     \"IOE02\", \"IOE03\", \"IOE04\", \"IOE05\", \"IOE06\", \"IOE07\",
     \"IOE08\", \"IOE09\", \"LeIrreflexivity\", \"LeTAsymmetry\",
     \"LeTTransitive\", \"LeTTotal\", \"GeDef\", \"GeIrreflexivity\",
     \"GeTAsymmetry\", \"GeTTransitive\", \"GeTTotal\", \"LeqDef\",
     \"LeqReflexivity\", \"LeqTTransitive\", \"LeqTTotal\", \"GeqDef\",
     \"GeqReflexivity\", \"GeqTTransitive\", \"GeqTTotal\",
     \"EqTSOrdRel\", \"EqFSOrdRel\", \"EqTOrdRel\", \"EqFOrdRel\",
     \"LeTGeTRel\", \"LeFGeFRel\", \"LeqTGetTRel\", \"LeqFGetFRel\",
     \"GeTLeTRel\", \"GeFLeFRel\", \"GeqTLeqTRel\", \"GeqFLeqFRel\",
     \"LeTGeFEqFRel\", \"LeFGeTEqTRel\", \"LeqTGeFRel\", \"LeqFGeTRel\",
     \"GeTLeFEqFRel\", \"GeFLeTEqTRel\", \"GeqTLeFRel\", \"GeqFLeTRel\",
     \"LeqTLeTEqTRel\", \"LeqFLeFEqFRel\", \"GeqTGeTEqTRel\",
     \"GeqFGeFEqFRel\", \"LeTGeqFRel\", \"GeTLeqFRel\", \"LeLeqDiff\",
     \"LeLtDef\", \"LeEqDef\", \"LeGtDef\", \"LqLtDef\", \"LqEqDef\",
     \"LqGtDef\", \"GeLtDef\", \"GeEqDef\", \"GeGtDef\", \"GqLtDef\",
     \"GqEqDef\", \"GqGtDef\", \"MaxYDef\", \"MaxXDef\", \"MinXDef\",
     \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\", \"TO3\",
     \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IOO13\", \"IOO14\",
     \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\",
     \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\",
     \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\",
     \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\",
     \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\",
     \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\"]"

typedecl Nat
typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT

consts
notH__X :: "Bool => Bool" ("(notH/ _)" [56] 56)
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
maxBound :: "'a"
minBound :: "'a"
otherwiseH :: "Bool"

instance Bool:: type ..
instance Nat:: type ..
instance Ordering:: type ..
instance Unit:: type ..

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
"ALL x. ALL y. x ==' y = True' --> x <' y = False'"

LeTAsymmetry [rule_format] :
"ALL x. ALL y. x <' y = True' --> y <' x = False'"

LeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. x <' y = True' & y <' z = True' --> x <' z = True'"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <' y = True' | y <' x = True') | x ==' y = True'"

GeDef [rule_format] : "ALL x. ALL y. x >' y = y <' x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x >' y = False'"

GeTAsymmetry [rule_format] :
"ALL x. ALL y. x >' y = True' --> y >' x = False'"

GeTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x >' y) && (y >' z) = True' --> x >' z = True'"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >' y) || (y >' x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL x. ALL y. x <=' y = (x <' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <=' x = True'"

LeqTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x <=' y) && (y <=' z) = True' --> x <=' z = True'"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <=' y) && (y <=' x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >=' y = (x >' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >=' x = True'"

GeqTTransitive [rule_format] :
"ALL x.
 ALL y. ALL z. (x >=' y) && (y >=' z) = True' --> x >=' z = True'"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >=' y) && (y >=' x) = x ==' y"

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

LeTGeTRel [rule_format] :
"ALL x. ALL y. x <' y = True' = (y >' x = True')"

LeFGeFRel [rule_format] :
"ALL x. ALL y. x <' y = False' = (y >' x = False')"

LeqTGetTRel [rule_format] :
"ALL x. ALL y. x <=' y = True' = (y >=' x = True')"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. x <=' y = False' = (y >=' x = False')"

GeTLeTRel [rule_format] :
"ALL x. ALL y. x >' y = True' = (y <' x = True')"

GeFLeFRel [rule_format] :
"ALL x. ALL y. x >' y = False' = (y <' x = False')"

GeqTLeqTRel [rule_format] :
"ALL x. ALL y. x >=' y = True' = (y <=' x = True')"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. x >=' y = False' = (y <=' x = False')"

LeTGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <' y = True' = (x >' y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <' y = False' = (x >' y = True' | x ==' y = True')"

LeqTGeFRel [rule_format] :
"ALL x. ALL y. x <=' y = True' = (x >' y = False')"

LeqFGeTRel [rule_format] :
"ALL x. ALL y. x <=' y = False' = (x >' y = True')"

GeTLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >' y = True' = (x <' y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >' y = False' = (x <' y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL x. ALL y. x >=' y = True' = (x <' y = False')"

GeqFLeTRel [rule_format] :
"ALL x. ALL y. x >=' y = False' = (x <' y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL x.
 ALL y. x <=' y = True' = (x <' y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL x.
 ALL y. x <=' y = False' = (x <' y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL x.
 ALL y. x >=' y = True' = (x >' y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL x.
 ALL y. x >=' y = False' = (x >' y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL x. ALL y. x <' y = True' = (x >=' y = False')"

GeTLeqFRel [rule_format] :
"ALL x. ALL y. x >' y = True' = (x <=' y = False')"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <' y = (x <=' y) && (x /= y)"

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
"ALL x. ALL y. X_max x y = x = (y <=' x = True')"

MinXDef [rule_format] :
"ALL x. ALL y. X_min x y = x = (x <=' y = True')"

MinYDef [rule_format] :
"ALL x. ALL y. X_min x y = y = (y <=' x = True')"

MaxSym [rule_format] :
"ALL x. ALL y. X_max x y = y = (X_max y x = y)"

MinSym [rule_format] :
"ALL x. ALL y. X_min x y = y = (X_min y x = y)"

TO1 [rule_format] :
"ALL x.
 ALL y. (x ==' y = True' | x <' y = True') = (x <=' y = True')"

TO2 [rule_format] :
"ALL x. ALL y. x ==' y = True' --> x <' y = False'"

TO3 [rule_format] :
"ALL x. ALL y. Not' Not' (x <' y) = True' | Not' (x <' y) = True'"

TO4 [rule_format] :
"ALL x. ALL y. x <' y = True' --> Not' (x ==' y) = True'"

TO5 [rule_format] :
"ALL w.
 ALL x.
 ALL y.
 ALL z.
 (x <' y = True' & y <' z = True') & z <' w = True' -->
 x <' w = True'"

TO6 [rule_format] :
"ALL x. ALL z. z <' x = True' --> Not' (x <' z) = True'"

TO7 [rule_format] :
"ALL x. ALL y. x <' y = True' = (y >' x = True')"

IOO13 [rule_format] : "LT <' EQ = True'"

IOO14 [rule_format] : "EQ <' GT = True'"

IOO15 [rule_format] : "LT <' GT = True'"

IOO16 [rule_format] : "LT <=' EQ = True'"

IOO17 [rule_format] : "EQ <=' GT = True'"

IOO18 [rule_format] : "LT <=' GT = True'"

IOO19 [rule_format] : "EQ >=' LT = True'"

IOO20 [rule_format] : "GT >=' EQ = True'"

IOO21 [rule_format] : "GT >=' LT = True'"

IOO22 [rule_format] : "EQ >' LT = True'"

IOO23 [rule_format] : "GT >' EQ = True'"

IOO24 [rule_format] : "GT >' LT = True'"

IOO25 [rule_format] : "X_max LT EQ = EQ"

IOO26 [rule_format] : "X_max EQ GT = GT"

IOO27 [rule_format] : "X_max LT GT = GT"

IOO28 [rule_format] : "X_min LT EQ = LT"

IOO29 [rule_format] : "X_min EQ GT = EQ"

IOO30 [rule_format] : "X_min LT GT = LT"

IOO31 [rule_format] : "compare LT LT = EQ"

IOO32 [rule_format] : "compare EQ EQ = EQ"

IOO33 [rule_format] : "compare GT GT = EQ"

IBO5 [rule_format] : "False' <' True' = True'"

IBO6 [rule_format] : "False' >=' True' = False'"

IBO7 [rule_format] : "True' >=' False' = True'"

IBO8 [rule_format] : "True' <' False' = False'"

IBO9 [rule_format] : "X_max False' True' = True'"

IBO10 [rule_format] : "X_min False' True' = False'"

IBO11 [rule_format] : "compare True' True' = EQ"

IBO12 [rule_format] : "compare False' False' = EQ"

IUO01 [rule_format] : "() <=' () = True'"

IUO02 [rule_format] : "() <' () = False'"

IUO03 [rule_format] : "() >=' () = True'"

IUO04 [rule_format] : "() >' () = False'"

IUO05 [rule_format] : "() = ()"

IUO06 [rule_format] : "() = ()"

IUO07 [rule_format] : "compare () () = EQ"

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

theorem Ax1 : "minBound = False'"
by auto

ML "Header.record \"Ax1\""

theorem Ax2 : "maxBound = True'"
by auto

ML "Header.record \"Ax2\""

theorem Ax3 : "minBound = LT"
by auto

ML "Header.record \"Ax3\""

theorem Ax4 : "maxBound = GT"
by auto

ML "Header.record \"Ax4\""

end
