theory Prelude_ListNoNumbers_E4
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"Comp1\", \"IdDef\", \"FlipDef\", \"FstDef\", \"SndDef\",
     \"CurryDef\", \"UncurryDef\", \"NotFalse\", \"NotTrue\",
     \"AndFalse\", \"AndTrue\", \"AndSym\", \"OrDef\", \"OtherwiseDef\",
     \"NotFalse1\", \"NotTrue1\", \"notNot1\", \"notNot2\",
     \"EqualTDef\", \"EqualSymDef\", \"EqualReflex\", \"EqualTransT\",
     \"DiffDef\", \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\",
     \"TE2\", \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE3\", \"IBE4\",
     \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\",
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
     \"TO3\", \"TO4\", \"TO5\", \"TO6\", \"TO7\", \"IOO13\", \"IOO14\",
     \"IOO15\", \"IOO16\", \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\",
     \"IOO21\", \"IOO22\", \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\",
     \"IOO27\", \"IOO28\", \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\",
     \"IOO33\", \"IBO5\", \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\",
     \"IBO10\", \"IBO11\", \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\",
     \"IUO04\", \"IUO05\", \"IUO06\", \"IUO07\", \"NotDefHead\",
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

typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XGtXEq__X :: "'a => 'a => Bool" ("(_/ >=''/ _)" [54,54] 52)
X__XGt__X :: "'a => 'a => Bool" ("(_/ >''/ _)" [54,54] 52)
X__XLtXEq__X :: "'a => 'a => Bool" ("(_/ <=''/ _)" [54,54] 52)
X__XLt__X :: "'a => 'a => Bool" ("(_/ <''/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X_curry :: "('a * 'b => 'c) => 'a => 'b => 'c"
X_filter :: "('a => Bool) => 'a List => 'a List"
X_flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
X_foldl :: "('a => 'b => 'a) => 'a => 'b List => 'a"
X_foldr :: "('a => 'b => 'b) => 'b => 'a List => 'b"
X_fst :: "'a => 'b => 'a" ("fst''/'(_,/ _')" [3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a => 'a" ("id''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_max :: "'a => 'a => 'a"
X_min :: "'a => 'a => 'a"
X_snd :: "'a => 'b => 'b" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List"
compare :: "'a => 'a => Ordering"
otherwiseH :: "Bool"
uncurry :: "('a => 'b => 'c) => 'a * 'b => 'c"

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

MaxSym [rule_format] :
"ALL x. ALL y. X_max x y ==' y = X_max y x ==' y"

MinSym [rule_format] :
"ALL x. ALL y. X_min x y ==' y = X_min y x ==' y"

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

ILE02 [rule_format] :
"ALL x.
 ALL xs.
 ALL y.
 ALL ys. X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

ILO05 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. z <' w = True' --> X_Cons z zs <' X_Cons w ws = True'"

ILO06 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. z ==' w = True' --> X_Cons z zs <' X_Cons w ws = zs <' ws"

ILO07 [rule_format] :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 z <' w = False' & z ==' w = False' -->
 X_Cons z zs <' X_Cons w ws = False'"

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

theorem ILE01 : "Nil' ==' Nil' = True'"
by (auto)

ML "Header.record \"ILE01\""

theorem ILO01 : "Nil' <' Nil' = False'"
by (auto)

ML "Header.record \"ILO01\""

theorem ILO02 : "Nil' <=' Nil' = True'"
by (auto)

ML "Header.record \"ILO02\""

theorem ILO03 : "Nil' >' Nil' = False'"
by (auto)

ML "Header.record \"ILO03\""

theorem ILO04 : "Nil' >=' Nil' = True'"
by (auto)

ML "Header.record \"ILO04\""

theorem ILO08 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <=' X_Cons w ws =
 (X_Cons z zs <' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"
apply(rule allI)+
apply(simp only: LeqDef)
done

ML "Header.record \"ILO08\""

theorem ILO09 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs. X_Cons z zs >' X_Cons w ws = X_Cons w ws <' X_Cons z zs"
apply(rule allI)+
apply(case_tac "X_Cons z zs >' X_Cons w ws")
apply(simp only: GeFLeFRel)
apply(simp only: GeTLeTRel)
done

ML "Header.record \"ILO09\""

theorem ILO10 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs >=' X_Cons w ws =
 (X_Cons z zs >' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"
apply(rule allI)+
apply(simp only: GeqDef)
done

ML "Header.record \"ILO10\""

theorem ILO11 : "compare Nil' Nil' ==' EQ = Nil' ==' Nil'"
by (auto)

ML "Header.record \"ILO11\""

theorem ILO12 : "compare Nil' Nil' ==' LT = Nil' <' Nil'"
by (auto)

ML "Header.record \"ILO12\""

theorem ILO13 : "compare Nil' Nil' ==' GT = Nil' >' Nil'"
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
 X_Cons z zs <' X_Cons w ws"
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
 X_Cons z zs >' X_Cons w ws"
apply(rule allI)+
apply(simp only: CmpGTDef)
done

ML "Header.record \"ILO16\""

theorem ILO17 : "X_max Nil' Nil' ==' Nil' = Nil' <=' Nil'"
by (auto)

ML "Header.record \"ILO17\""

theorem ILO18 : "X_min Nil' Nil' ==' Nil' = Nil' <=' Nil'"
by (auto)

ML "Header.record \"ILO18\""

theorem ILO19 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <=' X_Cons w ws =
 X_max (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO19\""

theorem ILO20 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <=' X_Cons z zs =
 X_max (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO20\""

theorem ILO21 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons z zs <=' X_Cons w ws =
 X_min (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"
apply(rule allI)+
apply(simp add: LeqDef)
done

ML "Header.record \"ILO21\""

theorem ILO22 :
"ALL w.
 ALL ws.
 ALL z.
 ALL zs.
 X_Cons w ws <=' X_Cons z zs =
 X_min (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"
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
 X_filter p (X_map f xs) = X_map f (X_filter (X__o__X (p, f)) xs)"
apply(auto)
apply(induct_tac xs)
apply(auto)
apply(case_tac "p(f a)")
apply(auto)
apply(simp add: MapCons)
apply(simp add: FilterConsT)
apply(simp add: MapCons)
apply(simp add: FilterConsT)
done

ML "Header.record \"FilterProm\""

end
