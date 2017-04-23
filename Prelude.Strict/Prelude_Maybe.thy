theory Prelude_Maybe
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
        \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
        \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
        \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"DiffSymDef\",
        \"DiffTDef\", \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\",
        \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\", \"IBE5\", \"IBE6\",
        \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\", \"IOE01\", \"IOE02\",
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
        \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO3\", \"TO4\",
        \"TO5\", \"IOO13\", \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\",
        \"IOO18\", \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\",
        \"IOO24\", \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\",
        \"IOO30\", \"IOO31\", \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\",
        \"IBO7\", \"IBO8\", \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\",
        \"IUO01\", \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\",
        \"IUO07\", \"MaybeJustDef\", \"MaybeNothingDef\", \"IME01\",
        \"IME03\", \"IMO01\", \"IMO02\", \"IME02\", \"IMO03\", \"IMO04\",
        \"IMO05\", \"IMO06\", \"IMO07\", \"IMO08\", \"IMO09\", \"IMO10\",
        \"IMO11\", \"IMO12\"]"

typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype 'a Maybe = X_Just 'a ("Just/'(_')" [3] 999) | Nothing

consts
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
maybe :: "'b => ('a => 'b) => 'a Maybe => 'b"
notH__X :: "Bool => Bool" ("(notH/ _)" [56] 56)
otherwiseH :: "Bool"

axioms
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
"ALL (x :: 'a). ALL (y :: 'a). x ==' y = True' --> x <' y = False'"

LeTAsymmetry [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <' y = True' --> y <' x = False'"

LeTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). x <' y = True' & y <' z = True' --> x <' z = True'"

LeTTotal [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). (x <' y = True' | y <' x = True') | x ==' y = True'"

GeDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >' y = y <' x"

GeIrreflexivity [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x ==' y = True' --> x >' y = False'"

GeTAsymmetry [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >' y = True' --> y >' x = False'"

GeTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (x >' y) && (y >' z) = True' --> x >' z = True'"

GeTTotal [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). ((x >' y) || (y >' x)) || (x ==' y) = True'"

LeqDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <=' y = (x <' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL (x :: 'a). x <=' x = True'"

LeqTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (x <=' y) && (y <=' z) = True' --> x <=' z = True'"

LeqTTotal [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). (x <=' y) && (y <=' x) = x ==' y"

GeqDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >=' y = (x >' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL (x :: 'a). x >=' x = True'"

GeqTTransitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). (x >=' y) && (y >=' z) = True' --> x >=' z = True'"

GeqTTotal [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). (x >=' y) && (y >=' x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = True' = (x <' y = False' & x >' y = False')"

EqFSOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = False' = (x <' y = True' | x >' y = True')"

EqTOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = True' = (x <=' y = True' & x >=' y = True')"

EqFOrdRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x ==' y = False' = (x <=' y = True' | x >=' y = True')"

EqTOrdTSubstE [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). x ==' y = True' & y <' z = True' --> x <' z = True'"

EqTOrdFSubstE [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & y <' z = False' --> x <' z = False'"

EqTOrdTSubstD [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a). x ==' y = True' & z <' y = True' --> z <' x = True'"

EqTOrdFSubstD [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 x ==' y = True' & z <' y = False' --> z <' x = False'"

LeTGeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <' y = True' = (x >' y = False' & x ==' y = False')"

LeFGeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <' y = False' = (x >' y = True' | x ==' y = True')"

LeTGeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <' y = True' = (y >' x = True')"

LeFGeFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <' y = False' = (y >' x = False')"

LeqTGetTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <=' y = True' = (y >=' x = True')"

LeqFGetFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <=' y = False' = (y >=' x = False')"

GeTLeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >' y = True' = (y <' x = True')"

GeFLeFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >' y = False' = (y <' x = False')"

GeqTLeqTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >=' y = True' = (y <=' x = True')"

GeqFLeqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x >=' y = False' = (y <=' x = False')"

LeqTGeFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <=' y = True' = (x >' y = False')"

LeqFGeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <=' y = False' = (x >' y = True')"

GeTLeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >' y = True' = (x <' y = False' & x ==' y = False')"

GeFLeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >' y = False' = (x <' y = True' | x ==' y = True')"

GeqTLeFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >=' y = True' = (x <' y = False')"

GeqFLeTRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >=' y = False' = (x <' y = True')"

LeqTLeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <=' y = True' = (x <' y = True' | x ==' y = True')"

LeqFLeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x <=' y = False' = (x <' y = False' & x ==' y = False')"

GeqTGeTEqTRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >=' y = True' = (x >' y = True' | x ==' y = True')"

GeqFGeFEqFRel [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 x >=' y = False' = (x >' y = False' & x ==' y = False')"

LeTGeqFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <' y = True' = (x >=' y = False')"

GeTLeqFRel [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x >' y = True' = (x <=' y = False')"

LeLeqDiff [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). x <' y = (x <=' y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' LT = x <' y"

CmpEQDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). compare x y ==' GT = x >' y"

MaxYDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_max x y ==' y = x <=' y"

MaxXDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_max x y ==' x = y <=' x"

MinXDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_min x y ==' x = x <=' y"

MinYDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_min x y ==' y = y <=' x"

MaxSym [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_max x y ==' y = X_max y x ==' y"

MinSym [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). X_min x y ==' y = X_min y x ==' y"

TO1 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 (x ==' y = True' | x <' y = True') = (x <=' y = True')"

TO3 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). notH notH (x <' y) = True' | notH (x <' y) = True'"

TO4 [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a). x <' y = True' --> notH (x ==' y) = True'"

TO5 [rule_format] :
"ALL (w :: 'a).
 ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (z :: 'a).
 (x <' y = True' & y <' z = True') & z <' w = True' -->
 x <' w = True'"

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

IOO25 [rule_format] : "X_max LT EQ ==' EQ = True'"

IOO26 [rule_format] : "X_max EQ GT ==' GT = True'"

IOO27 [rule_format] : "X_max LT GT ==' GT = True'"

IOO28 [rule_format] : "X_min LT EQ ==' LT = True'"

IOO29 [rule_format] : "X_min EQ GT ==' EQ = True'"

IOO30 [rule_format] : "X_min LT GT ==' LT = True'"

IOO31 [rule_format] : "compare LT LT ==' EQ = True'"

IOO32 [rule_format] : "compare EQ EQ ==' EQ = True'"

IOO33 [rule_format] : "compare GT GT ==' EQ = True'"

IBO5 [rule_format] : "False' <' True' = True'"

IBO6 [rule_format] : "False' >=' True' = False'"

IBO7 [rule_format] : "True' >=' False' = True'"

IBO8 [rule_format] : "True' <' False' = False'"

IBO9 [rule_format] : "X_max False' True' ==' True' = True'"

IBO10 [rule_format] : "X_min False' True' ==' False' = True'"

IBO11 [rule_format] : "compare True' True' ==' EQ = True'"

IBO12 [rule_format] : "compare False' False' ==' EQ = True'"

IUO01 [rule_format] : "() <=' () = True'"

IUO02 [rule_format] : "() <' () = False'"

IUO03 [rule_format] : "() >=' () = True'"

IUO04 [rule_format] : "() >' () = False'"

IUO05 [rule_format] : "X_max () () ==' () = True'"

IUO06 [rule_format] : "X_min () () ==' () = True'"

IUO07 [rule_format] : "compare () () ==' EQ = True'"

MaybeJustDef [rule_format] :
"ALL (f :: 'a => 'b).
 ALL (x :: 'a). ALL (y :: 'b). maybe y f (Just(x)) = f x"

MaybeNothingDef [rule_format] :
"ALL (f :: 'a => 'b). ALL (y :: 'b). maybe y f Nothing = y"

IME01 [rule_format] :
"ALL (x :: 'e).
 ALL (y :: 'e). Just(x) ==' Just(y) = True' = (x ==' y = True')"

IME03 [rule_format] : "ALL (x :: 'e). Just(x) ==' Nothing = False'"

IMO01 [rule_format] : "ALL (x :: 'o). Nothing <' Just(x) = True'"

IMO02 [rule_format] :
"ALL (x :: 'o). ALL (y :: 'o). Just(x) <' Just(y) = x <' y"

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
declare MaybeJustDef [simp]
declare MaybeNothingDef [simp]
declare IME03 [simp]
declare IMO01 [simp]
declare IMO02 [simp]

theorem IME02 : "Nothing ==' Nothing = True'"
by (auto)

setup "Header.record \"IME02\""

theorem IMO03 : "ALL (x :: 'o). Nothing >=' Just(x) = False'"
apply(rule allI)
apply(simp only: GeqDef)
apply(simp only: GeDef OrDef)
apply(case_tac "Just(x) <' Nothing")
apply(auto)
done

setup "Header.record \"IMO03\""

theorem IMO04 : "ALL (x :: 'o). Just(x) >=' Nothing = True'"
apply(rule allI)
apply(simp only: GeqDef)
apply(simp only: GeDef OrDef)
apply(case_tac "Nothing <' Just(x)")
apply(auto)
done

setup "Header.record \"IMO04\""

theorem IMO05 : "ALL (x :: 'o). Just(x) <' Nothing = False'"
apply(rule allI)
apply(case_tac "Just(x) <' Nothing")
apply(auto)
done

setup "Header.record \"IMO05\""

theorem IMO06 :
"ALL (x :: 'o).
 compare Nothing (Just(x)) ==' EQ = Nothing ==' Just(x)"
by (auto)

setup "Header.record \"IMO06\""

theorem IMO07 :
"ALL (x :: 'o).
 compare Nothing (Just(x)) ==' LT = Nothing <' Just(x)"
by (auto)

setup "Header.record \"IMO07\""

theorem IMO08 :
"ALL (x :: 'o).
 compare Nothing (Just(x)) ==' GT = Nothing >' Just(x)"
apply(rule allI)+
apply(simp add: GeDef)
done

setup "Header.record \"IMO08\""

theorem IMO09 :
"ALL (x :: 'o).
 Nothing <=' Just(x) = X_max Nothing (Just(x)) ==' Just(x)"
apply(rule allI)+
apply(simp add: LeqDef)
done

setup "Header.record \"IMO09\""

theorem IMO10 :
"ALL (x :: 'o).
 Just(x) <=' Nothing = X_max Nothing (Just(x)) ==' Nothing"
apply(rule allI)+
apply(simp add: LeqDef)
done

setup "Header.record \"IMO10\""

theorem IMO11 :
"ALL (x :: 'o).
 Nothing <=' Just(x) = X_min Nothing (Just(x)) ==' Nothing"
apply(rule allI)+
apply(simp add: LeqDef)
done

setup "Header.record \"IMO11\""

theorem IMO12 :
"ALL (x :: 'o).
 Just(x) <=' Nothing = X_min Nothing (Just(x)) ==' Just(x)"
apply(rule allI)+
apply(simp add: LeqDef)
done

setup "Header.record \"IMO12\""

end
