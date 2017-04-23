theory LazyPrelude_ListNoNumbers_E4
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Comp1\", \"IdDef\", \"FlipDef\", \"FstDef\", \"SndDef\",
     \"CurryDef\", \"UncurryDef\", \"NotFalse\", \"NotTrue\",
     \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
     \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\",
     \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\", \"EqualTransT\",
     \"DiffDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\",
     \"TE2\", \"TE3\", \"TE4\", \"IUE1\", \"IUE2\", \"IBE1\", \"IBE2\",
     \"IBE3\", \"IBE4\", \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\",
     \"IOE01\", \"IOE02\", \"IOE03\", \"IOE04\", \"IOE05\", \"IOE06\",
     \"IOE07\", \"IOE08\", \"IOE09\", \"LeIrreflexivity\",
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
     \"CmpLTDef\", \"CmpEQDef\", \"CmpGTDef\", \"MaxYDef\", \"MaxXDef\",
     \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO2\",
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IUO01\", \"IUO02\",
     \"IUO03\", \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"IOO13\",
     \"IOO14\", \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\",
     \"IOO20\", \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\",
     \"IOO26\", \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\",
     \"IOO32\", \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\",
     \"IBO9\", \"IBO10\", \"IBO11\", \"IBO12\", \"NotDefHead\",
     \"HeadDef\", \"NotDefTail\", \"TailDef\", \"FoldrNil\",
     \"FoldrCons\", \"FoldlNil\", \"FoldlCons\", \"MapNil\",
     \"MapCons\", \"XPlusXPlusNil\", \"XPlusXPlusCons\", \"FilterNil\",
     \"FilterConsT\", \"FilterConsF\", \"ZipNil\", \"ZipConsNil\",
     \"ZipConsCons\", \"UnzipNil\", \"UnzipCons\", \"ILE02\", \"ILO05\",
     \"ILO06\", \"ILO07\", \"ILE01\", \"ILO01\", \"ILO02\", \"ILO03\",
     \"ILO04\", \"ILO08\", \"ILO09\", \"ILO10\", \"ILO11\", \"ILO12\",
     \"ILO13\", \"ILO14\", \"ILO15\", \"ILO16\", \"ILO17\", \"ILO18\",
     \"ILO19\", \"ILO20\", \"ILO21\", \"ILO22\", \"FoldlDecomp\",
     \"MapDecomp\", \"MapFunctor\", \"FilterProm\"]"

typedecl Bool
typedecl ('a1) DList
typedecl Unit
typedecl X_Nat

datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons "'a partial" "'a List partial" | X_Nil ("Nil''")

consts
Not__X :: "bool => bool" ("(Not''/ _)" [56] 56)
X__XAmpXAmp__X :: "bool => bool => bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a partial => 'a partial => bool" ("(_/ ==''/ _)" [54,54] 52)
X__XGtXEq__X :: "'a partial => 'a partial => bool" ("(_/ >=''/ _)" [54,54] 52)
X__XGt__X :: "'a partial => 'a partial => bool" ("(_/ >''/ _)" [54,54] 52)
X__XLtXEq__X :: "'a partial => 'a partial => bool" ("(_/ <=''/ _)" [54,54] 52)
X__XLt__X :: "'a partial => 'a partial => bool" ("(_/ <''/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List partial => 'a List partial => 'a List partial" ("(_/ ++''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a partial => 'a partial => bool" ("(_/ '/=/ _)" [54,54] 52)
X__XVBarXVBar__X :: "bool => bool => bool" ("(_/ ||/ _)" [54,54] 52)
X__o__X :: "('b partial => 'c partial) * ('a partial => 'b partial) => 'a partial => 'c partial"
X_curry :: "('a partial * 'b partial => 'c partial) => 'a partial => 'b partial => 'c partial"
X_filter :: "('a partial => bool) => 'a List partial => 'a List partial"
X_flip :: "('a partial => 'b partial => 'c partial) => 'b partial => 'a partial => 'c partial"
X_foldl :: "('a partial => 'b partial => 'a partial) => 'a partial => 'b List partial => 'a partial"
X_foldr :: "('a partial => 'b partial => 'b partial) => 'b partial => 'a List partial => 'b partial"
X_fst :: "'a partial => 'b partial => 'a partial" ("fst''/'(_,/ _')" [3,3] 999)
X_head :: "'a List partial => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a partial => 'a partial" ("id''/'(_')" [3] 999)
X_map :: "('a partial => 'b partial) => 'a List partial => 'b List partial"
X_max :: "'a partial => 'a partial => 'a partial"
X_min :: "'a partial => 'a partial => 'a partial"
X_snd :: "'a partial => 'b partial => 'b partial" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List partial => 'a List partial" ("tail/'(_')" [3] 999)
X_unzip :: "('a * 'b) List partial => 'a List partial * 'b List partial" ("unzip/'(_')" [3] 999)
X_zip :: "'a List partial => 'b List partial => ('a * 'b) List partial"
compare :: "'a partial => 'a partial => Ordering partial"
otherwiseH :: "bool"
uncurry :: "('a partial => 'b partial => 'c partial) => 'a partial * 'b partial => 'c partial"

axioms
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

NotDefHead [rule_format] : "~ defOp (head(makePartial Nil'))"

HeadDef [rule_format] :
"ALL x. ALL xs. head(makePartial (X_Cons x xs)) = x"

NotDefTail [rule_format] : "~ defOp (tail(makePartial Nil'))"

TailDef [rule_format] :
"ALL x. ALL xs. tail(makePartial (X_Cons x xs)) = xs"

FoldrNil [rule_format] :
"ALL f. ALL s. X_foldr f s (makePartial Nil') = s"

FoldrCons [rule_format] :
"ALL f.
 ALL s.
 ALL x.
 ALL xs.
 X_foldr f s (makePartial (X_Cons x xs)) = f x (X_foldr f s xs)"

FoldlNil [rule_format] :
"ALL g. ALL t. X_foldl g t (makePartial Nil') = t"

FoldlCons [rule_format] :
"ALL g.
 ALL t.
 ALL z.
 ALL zs.
 X_foldl g t (makePartial (X_Cons z zs)) = X_foldl g (g t z) zs"

MapNil [rule_format] :
"ALL h. X_map h (makePartial Nil') = makePartial Nil'"

MapCons [rule_format] :
"ALL h.
 ALL x.
 ALL xs.
 X_map h (makePartial (X_Cons x xs)) =
 makePartial (X_Cons (h x) (X_map h xs))"

XPlusXPlusNil [rule_format] : "ALL l. makePartial Nil' ++' l = l"

XPlusXPlusCons [rule_format] :
"ALL l.
 ALL x.
 ALL xs.
 makePartial (X_Cons x xs) ++' l =
 makePartial (X_Cons x (xs ++' l))"

FilterNil [rule_format] :
"ALL p. X_filter p (makePartial Nil') = makePartial Nil'"

FilterConsT [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 p x -->
 X_filter p (makePartial (X_Cons x xs)) =
 makePartial (X_Cons x (X_filter p xs))"

FilterConsF [rule_format] :
"ALL p.
 ALL x.
 ALL xs.
 ~ p x --> X_filter p (makePartial (X_Cons x xs)) = X_filter p xs"

ZipNil [rule_format] :
"ALL l. X_zip (makePartial Nil') l = makePartial Nil'"

ZipConsNil [rule_format] :
"ALL l.
 ALL x.
 ALL xs.
 l = makePartial Nil' -->
 X_zip (makePartial (X_Cons x xs)) l = makePartial Nil'"

ZipConsCons [rule_format] :
"ALL l.
 ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 l = makePartial (X_Cons y ys) -->
 X_zip (makePartial (X_Cons x xs)) l =
 makePartial
 (X_Cons
  (restrictOp (makePartial (makeTotal x, makeTotal y))
   (defOp x & defOp y))
  (X_zip xs ys))"

UnzipNil [rule_format] :
"mapSnd makeTotal (mapFst makeTotal (unzip(makePartial Nil'))) =
 (Nil', Nil')"

UnzipCons [rule_format] :
"ALL ps.
 ALL x.
 ALL z.
 mapSnd makeTotal
 (mapFst makeTotal
  (unzip(makePartial
         (X_Cons
          (restrictOp (makePartial (makeTotal x, makeTotal z))
           (defOp x & defOp z))
          ps)))) =
 (let (ys, zs) = unzip(ps) in (X_Cons x ys, X_Cons z zs))"

ILE02 [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys.
 makePartial (X_Cons x xs) ==' makePartial (X_Cons y ys) =
 (x ==' y) && (xs ==' ys)"

ILO05 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 z <' w --> makePartial (X_Cons z zs) <' makePartial (X_Cons w ws)"

ILO06 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 z ==' w -->
 makePartial (X_Cons z zs) <' makePartial (X_Cons w ws) = zs <' ws"

ILO07 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 ~ z <' w & ~ z ==' w -->
 ~ makePartial (X_Cons z zs) <' makePartial (X_Cons w ws)"

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
declare NotDefHead [simp]
declare HeadDef [simp]
declare NotDefTail [simp]
declare TailDef [simp]
declare FoldrNil [simp]
declare FoldrCons [simp]
declare FoldlNil [simp]
declare FoldlCons [simp]
declare MapNil [simp]
declare XPlusXPlusNil [simp]
declare FilterNil [simp]
declare FilterConsF [simp]
declare ZipNil [simp]
declare UnzipNil [simp]
declare ILE02 [simp]
declare ILO05 [simp]
declare ILO06 [simp]

theorem ILE01 : "makePartial Nil' ==' makePartial Nil'"
by (auto)

ML "Header.record \"ILE01\""

theorem ILO01 : "~ makePartial Nil' <' makePartial Nil'"
by (auto)

ML "Header.record \"ILO01\""

theorem ILO02 : "makePartial Nil' <=' makePartial Nil'"
by (auto)

ML "Header.record \"ILO02\""

theorem ILO03 : "~ makePartial Nil' >' makePartial Nil'"
by (auto)

ML "Header.record \"ILO03\""

theorem ILO04 : "makePartial Nil' >=' makePartial Nil'"
by (auto)

ML "Header.record \"ILO04\""

theorem ILO08 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons z zs) <=' makePartial (X_Cons w ws) =
 (makePartial (X_Cons z zs) <' makePartial (X_Cons w ws)) ||
 (makePartial (X_Cons z zs) ==' makePartial (X_Cons w ws))"
apply(rule allI)+
apply(simp only: LeqDef)
done

ML "Header.record \"ILO08\""

theorem ILO09 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons z zs) >' makePartial (X_Cons w ws) =
 makePartial (X_Cons w ws) <' makePartial (X_Cons z zs)"
apply(rule allI)+
apply(simp only: GeTLeTRel)
done

ML "Header.record \"ILO09\""

theorem ILO10 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons z zs) >=' makePartial (X_Cons w ws) =
 (makePartial (X_Cons z zs) >' makePartial (X_Cons w ws)) ||
 (makePartial (X_Cons z zs) ==' makePartial (X_Cons w ws))"
apply(rule allI)+
apply(simp only: GeqDef)
done

ML "Header.record \"ILO10\""

theorem ILO11 :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial EQ =
 makePartial Nil' ==' makePartial Nil'"
by (auto)

ML "Header.record \"ILO11\""

theorem ILO12 :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial LT =
 makePartial Nil' <' makePartial Nil'"
by (auto)

ML "Header.record \"ILO12\""

theorem ILO13 :
"compare (makePartial Nil') (makePartial Nil') ==' makePartial GT =
 makePartial Nil' >' makePartial Nil'"
by (auto)

ML "Header.record \"ILO13\""

theorem ILO14 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial EQ =
 makePartial (X_Cons z zs) ==' makePartial (X_Cons w ws)"
by (auto)

ML "Header.record \"ILO14\""

theorem ILO15 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial LT =
 makePartial (X_Cons z zs) <' makePartial (X_Cons w ws)"
apply(rule allI)+
apply(simp only: CmpLTDef)
done

ML "Header.record \"ILO15\""

theorem ILO16 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 compare (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial GT =
 makePartial (X_Cons z zs) >' makePartial (X_Cons w ws)"
apply(rule allI)+
apply(simp only: CmpGTDef)
done

ML "Header.record \"ILO16\""

theorem ILO17 :
"X_max (makePartial Nil') (makePartial Nil') ==' makePartial Nil' =
 makePartial Nil' <=' makePartial Nil'"
by (auto)

ML "Header.record \"ILO17\""

theorem ILO18 :
"X_min (makePartial Nil') (makePartial Nil') ==' makePartial Nil' =
 makePartial Nil' <=' makePartial Nil'"
by (auto)

ML "Header.record \"ILO18\""

theorem ILO19 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons z zs) <=' makePartial (X_Cons w ws) =
 X_max (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial (X_Cons w ws)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO19\""

theorem ILO20 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons w ws) <=' makePartial (X_Cons z zs) =
 X_max (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial (X_Cons z zs)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO20\""

theorem ILO21 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons z zs) <=' makePartial (X_Cons w ws) =
 X_min (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial (X_Cons z zs)"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO21\""

theorem ILO22 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 makePartial (X_Cons w ws) <=' makePartial (X_Cons z zs) =
 X_min (makePartial (X_Cons z zs)) (makePartial (X_Cons w ws)) =='
 makePartial (X_Cons w ws)"
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
apply(case_tac "(ab, bb) ++' (aa, ba)")
apply(auto)
oops

ML "Header.record \"FoldlDecomp\""

theorem MapDecomp :
"ALL f.
 ALL xs. ALL zs. X_map f (xs ++' zs) = X_map f xs ++' X_map f zs"
apply(auto)
apply(induct_tac a)
apply(auto)
apply(case_tac b)
apply(auto)
oops

ML "Header.record \"MapDecomp\""

theorem MapFunctor :
"ALL f.
 ALL g. ALL xs. X_map (X__o__X (g, f)) xs = X_map g (X_map f xs)"
apply(auto)
apply(induct_tac a)
apply(case_tac b)
apply(auto)
oops

ML "Header.record \"MapFunctor\""

theorem FilterProm :
"ALL f.
 ALL p.
 ALL xs.
 X_filter p (X_map f xs) =
 X_map f (X_filter (id o defOp o X__o__X (bool2partial o p, f)) xs)"
apply(auto)
apply(induct_tac a)
apply(auto)
apply(case_tac "p(f a)")
oops

ML "Header.record \"FilterProm\""

end
