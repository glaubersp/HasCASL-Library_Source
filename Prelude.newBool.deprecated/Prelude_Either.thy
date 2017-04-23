theory Prelude_Either
imports "$HETS_LIB/Isabelle/MainHCPairs"
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
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"EitherLeftDef\",
     \"EitherRightDef\", \"IEE01\", \"IEE02\", \"IEE03\", \"IEO01\",
     \"IEO02\", \"IEO03\", \"IEO04\", \"IEO05\", \"IEO06\", \"IEO07\",
     \"IEO08\", \"IEO09\", \"IEO10\", \"IEO11\", \"IEO12\", \"IEO13\"]"

typedecl Bool
typedecl Unit
typedecl X_Nat

datatype Ordering = EQ | GT | LT
datatype ('a, 'b) Either = X_Left 'a ("Left''/'(_')" [3] 999) | X_Right 'b ("Right''/'(_')" [3] 999)

consts
Not__X :: "bool => bool" ("(Not''/ _)" [56] 56)
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
either :: "('a partial => 'c partial) => ('b partial => 'c partial) => ('a, 'b) Either partial => 'c partial"
otherwiseH :: "bool"

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
"ALL x. ALL y. x ==' y --> ~ x <' y"

LeTAsymmetry [rule_format] : "ALL x. ALL y. x <' y --> ~ y <' x"

LeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. x <' y & y <' z --> x <' z"

LeTTotal [rule_format] :
"ALL x. ALL y. (x <' y | y <' x) | x ==' y"

GeDef [rule_format] : "ALL x. ALL y. x >' y = y <' x"

GeIrreflexivity [rule_format] :
"ALL x. ALL y. x ==' y --> ~ x >' y"

GeTAsymmetry [rule_format] : "ALL x. ALL y. x >' y --> ~ y >' x"

GeTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >' y) && (y >' z) --> x >' z"

GeTTotal [rule_format] :
"ALL x. ALL y. ((x >' y) || (y >' x)) || (x ==' y)"

LeqDef [rule_format] :
"ALL x. ALL y. x <=' y = (x <' y) || (x ==' y)"

LeqReflexivity [rule_format] : "ALL x. x <=' x"

LeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x <=' y) && (y <=' z) --> x <=' z"

LeqTTotal [rule_format] :
"ALL x. ALL y. (x <=' y) && (y <=' x) = x ==' y"

GeqDef [rule_format] :
"ALL x. ALL y. x >=' y = (x >' y) || (x ==' y)"

GeqReflexivity [rule_format] : "ALL x. x >=' x"

GeqTTransitive [rule_format] :
"ALL x. ALL y. ALL z. (x >=' y) && (y >=' z) --> x >=' z"

GeqTTotal [rule_format] :
"ALL x. ALL y. (x >=' y) && (y >=' x) = x ==' y"

EqTSOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (~ x <' y & ~ x >' y)"

EqFSOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <' y | x >' y)"

EqTOrdRel [rule_format] :
"ALL x. ALL y. x ==' y = (x <=' y & x >=' y)"

EqFOrdRel [rule_format] :
"ALL x. ALL y. (~ x ==' y) = (x <=' y | x >=' y)"

EqTOrdTSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & y <' z --> x <' z"

EqTOrdFSubstE [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ y <' z --> ~ x <' z"

EqTOrdTSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & z <' y --> z <' x"

EqTOrdFSubstD [rule_format] :
"ALL x. ALL y. ALL z. x ==' y & ~ z <' y --> ~ z <' x"

LeTGeFEqFRel [rule_format] :
"ALL x. ALL y. x <' y = (~ x >' y & ~ x ==' y)"

LeFGeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x <' y) = (x >' y | x ==' y)"

LeTGeTRel [rule_format] : "ALL x. ALL y. x <' y = y >' x"

LeFGeFRel [rule_format] : "ALL x. ALL y. (~ x <' y) = (~ y >' x)"

LeqTGetTRel [rule_format] : "ALL x. ALL y. x <=' y = y >=' x"

LeqFGetFRel [rule_format] :
"ALL x. ALL y. (~ x <=' y) = (~ y >=' x)"

GeTLeTRel [rule_format] : "ALL x. ALL y. x >' y = y <' x"

GeFLeFRel [rule_format] : "ALL x. ALL y. (~ x >' y) = (~ y <' x)"

GeqTLeqTRel [rule_format] : "ALL x. ALL y. x >=' y = y <=' x"

GeqFLeqFRel [rule_format] :
"ALL x. ALL y. (~ x >=' y) = (~ y <=' x)"

LeqTGeFRel [rule_format] : "ALL x. ALL y. x <=' y = (~ x >' y)"

LeqFGeTRel [rule_format] : "ALL x. ALL y. (~ x <=' y) = x >' y"

GeTLeFEqFRel [rule_format] :
"ALL x. ALL y. x >' y = (~ x <' y & ~ x ==' y)"

GeFLeTEqTRel [rule_format] :
"ALL x. ALL y. (~ x >' y) = (x <' y | x ==' y)"

GeqTLeFRel [rule_format] : "ALL x. ALL y. x >=' y = (~ x <' y)"

GeqFLeTRel [rule_format] : "ALL x. ALL y. (~ x >=' y) = x <' y"

LeqTLeTEqTRel [rule_format] :
"ALL x. ALL y. x <=' y = (x <' y | x ==' y)"

LeqFLeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x <=' y) = (~ x <' y & ~ x ==' y)"

GeqTGeTEqTRel [rule_format] :
"ALL x. ALL y. x >=' y = (x >' y | x ==' y)"

GeqFGeFEqFRel [rule_format] :
"ALL x. ALL y. (~ x >=' y) = (~ x >' y & ~ x ==' y)"

LeTGeqFRel [rule_format] : "ALL x. ALL y. x <' y = (~ x >=' y)"

GeTLeqFRel [rule_format] : "ALL x. ALL y. x >' y = (~ x <=' y)"

LeLeqDiff [rule_format] :
"ALL x. ALL y. x <' y = (x <=' y) && (x /= y)"

CmpLTDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial LT = x <' y"

CmpEQDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial EQ = x ==' y"

CmpGTDef [rule_format] :
"ALL x. ALL y. compare x y ==' makePartial GT = x >' y"

MaxYDef [rule_format] : "ALL x. ALL y. X_max x y ==' y = x <=' y"

MaxXDef [rule_format] : "ALL x. ALL y. X_max x y ==' x = y <=' x"

MinXDef [rule_format] : "ALL x. ALL y. X_min x y ==' x = x <=' y"

MinYDef [rule_format] : "ALL x. ALL y. X_min x y ==' y = y <=' x"

MaxSym [rule_format] :
"ALL x. ALL y. X_max x y ==' y = X_max y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_min x y ==' y = X_min y x ==' y"

TO1 [rule_format] : "ALL x. ALL y. (x ==' y | x <' y) = x <=' y"

TO2 [rule_format] : "ALL x. ALL y. x ==' y --> ~ x <' y"

TO3 [rule_format] :
"ALL x. ALL y. Not' Not' (x <' y) | Not' (x <' y)"

TO4 [rule_format] : "ALL x. ALL y. x <' y --> Not' (x ==' y)"

TO5 [rule_format] :
"ALL w. ALL x. ALL y. ALL z. (x <' y & y <' z) & z <' w --> x <' w"

TO6 [rule_format] : "ALL x. ALL z. z <' x --> Not' (x <' z)"

TO7 [rule_format] : "ALL x. ALL y. x <' y = y >' x"

IUO01 [rule_format] : "makePartial () <=' makePartial ()"

IUO02 [rule_format] : "~ makePartial () <' makePartial ()"

IUO03 [rule_format] : "makePartial () >=' makePartial ()"

IUO04 [rule_format] : "~ makePartial () >' makePartial ()"

IUO05 [rule_format] :
"X_max (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO06 [rule_format] :
"X_min (makePartial ()) (makePartial ()) ==' makePartial ()"

IUO07 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IOO13 [rule_format] : "makePartial LT <' makePartial EQ"

IOO14 [rule_format] : "makePartial EQ <' makePartial GT"

IOO15 [rule_format] : "makePartial LT <' makePartial GT"

IOO16 [rule_format] : "makePartial LT <=' makePartial EQ"

IOO17 [rule_format] : "makePartial EQ <=' makePartial GT"

IOO18 [rule_format] : "makePartial LT <=' makePartial GT"

IOO19 [rule_format] : "makePartial EQ >=' makePartial LT"

IOO20 [rule_format] : "makePartial GT >=' makePartial EQ"

IOO21 [rule_format] : "makePartial GT >=' makePartial LT"

IOO22 [rule_format] : "makePartial EQ >' makePartial LT"

IOO23 [rule_format] : "makePartial GT >' makePartial EQ"

IOO24 [rule_format] : "makePartial GT >' makePartial LT"

IOO25 [rule_format] :
"X_max (makePartial LT) (makePartial EQ) ==' makePartial EQ"

IOO26 [rule_format] :
"X_max (makePartial EQ) (makePartial GT) ==' makePartial GT"

IOO27 [rule_format] :
"X_max (makePartial LT) (makePartial GT) ==' makePartial GT"

IOO28 [rule_format] :
"X_min (makePartial LT) (makePartial EQ) ==' makePartial LT"

IOO29 [rule_format] :
"X_min (makePartial EQ) (makePartial GT) ==' makePartial EQ"

IOO30 [rule_format] :
"X_min (makePartial LT) (makePartial GT) ==' makePartial LT"

IOO31 [rule_format] :
"compare (makePartial LT) (makePartial LT) ==' makePartial EQ"

IOO32 [rule_format] :
"compare (makePartial EQ) (makePartial EQ) ==' makePartial EQ"

IOO33 [rule_format] :
"compare (makePartial GT) (makePartial GT) ==' makePartial EQ"

IBO5 [rule_format] : "undefinedOp <' makePartial ()"

IBO6 [rule_format] : "~ undefinedOp >=' makePartial ()"

IBO7 [rule_format] : "makePartial () >=' undefinedOp"

IBO8 [rule_format] : "~ makePartial () <' undefinedOp"

IBO9 [rule_format] :
"X_max undefinedOp (makePartial ()) ==' makePartial ()"

IBO10 [rule_format] :
"X_min undefinedOp (makePartial ()) ==' undefinedOp"

IBO11 [rule_format] :
"compare (makePartial ()) (makePartial ()) ==' makePartial EQ"

IBO12 [rule_format] :
"compare undefinedOp undefinedOp ==' makePartial EQ"

EitherLeftDef [rule_format] :
"ALL f.
 ALL g.
 ALL x.
 either f g
 (restrictOp (makePartial (Left'(makeTotal x))) (defOp x)) =
 f x"

EitherRightDef [rule_format] :
"ALL f.
 ALL g.
 ALL y.
 either f g
 (restrictOp (makePartial (Right'(makeTotal y))) (defOp y)) =
 g y"

IEE01 [rule_format] :
"ALL x.
 ALL y.
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) =='
 restrictOp (makePartial (Left'(makeTotal y))) (defOp y) =
 x ==' y"

IEE02 [rule_format] :
"ALL w.
 ALL z.
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) =='
 restrictOp (makePartial (Right'(makeTotal w))) (defOp w) =
 z ==' w"

IEE03 [rule_format] :
"ALL x.
 ALL z.
 ~
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) =='
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"

IEO01 [rule_format] :
"ALL x.
 ALL z.
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) <'
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"

IEO02 [rule_format] :
"ALL x.
 ALL y.
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) <'
 restrictOp (makePartial (Left'(makeTotal y))) (defOp y) =
 x <' y"

IEO03 [rule_format] :
"ALL w.
 ALL z.
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <'
 restrictOp (makePartial (Right'(makeTotal w))) (defOp w) =
 z <' w"

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
declare EitherLeftDef [simp]
declare EitherRightDef [simp]
declare IEE01 [simp]
declare IEE02 [simp]
declare IEE03 [simp]
declare IEO01 [simp]
declare IEO02 [simp]
declare IEO03 [simp]

theorem IEO04 :
"ALL x.
 ALL z.
 ~
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) >='
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(simp only: GeqDef OrDef GeDef)
apply(case_tac "(restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <' restrictOp (makePartial (Left'(makeTotal x))) (defOp x))")
by(auto)

ML "Header.record \"IEO04\""

theorem IEO05 :
"ALL x.
 ALL z.
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) >='
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x)"
apply(simp only: GeqDef OrDef GeDef)
apply(case_tac "(restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <' restrictOp (makePartial (Left'(makeTotal x))) (defOp x))")
by(auto)

ML "Header.record \"IEO05\""

theorem IEO06 :
"ALL x.
 ALL z.
 ~
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <'
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x)"
by auto

ML "Header.record \"IEO06\""

theorem IEO07 :
"ALL x.
 ALL z.
 compare (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' makePartial EQ =
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) =='
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO07\""

theorem IEO08 :
"ALL x.
 ALL z.
 compare (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' makePartial LT =
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) <'
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO08\""

theorem IEO09 :
"ALL x.
 ALL z.
 compare (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' makePartial GT =
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) >'
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(rule allI)+
apply(simp add: GeDef)
done

ML "Header.record \"IEO09\""

theorem IEO10 :
"ALL x.
 ALL z.
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) <='
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) =
 X_max (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO10\""

theorem IEO11 :
"ALL x.
 ALL z.
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <='
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) =
 X_max (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' restrictOp (makePartial (Left'(makeTotal x))) (defOp x)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO11\""

theorem IEO12 :
"ALL x.
 ALL z.
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) <='
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) =
 X_min (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' restrictOp (makePartial (Left'(makeTotal x))) (defOp x)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO12\""

theorem IEO13 :
"ALL x.
 ALL z.
 restrictOp (makePartial (Right'(makeTotal z))) (defOp z) <='
 restrictOp (makePartial (Left'(makeTotal x))) (defOp x) =
 X_min (restrictOp (makePartial (Left'(makeTotal x))) (defOp x))
 (restrictOp (makePartial (Right'(makeTotal z))) (defOp z))
 ==' restrictOp (makePartial (Right'(makeTotal z))) (defOp z)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"IEO13\""

end
