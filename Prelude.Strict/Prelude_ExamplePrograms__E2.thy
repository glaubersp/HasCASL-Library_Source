theory Prelude_ExamplePrograms__E2
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
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
        \"MinXDef\", \"MinYDef\", \"MaxSym\", \"MinSym\", \"TO1\", \"TO3\",
        \"TO4\", \"TO5\", \"IOO13\", \"IOO14\", \"IOO15\", \"IOO16\",
        \"IOO17\", \"IOO18\", \"IOO19\", \"IOO20\", \"IOO21\", \"IOO22\",
        \"IOO23\", \"IOO24\", \"IOO25\", \"IOO26\", \"IOO27\", \"IOO28\",
        \"IOO29\", \"IOO30\", \"IOO31\", \"IOO32\", \"IOO33\", \"IBO5\",
        \"IBO6\", \"IBO7\", \"IBO8\", \"IBO9\", \"IBO10\", \"IBO11\",
        \"IBO12\", \"IUO01\", \"IUO02\", \"IUO03\", \"IUO04\", \"IUO05\",
        \"IUO06\", \"IUO07\", \"NotDefHead\", \"HeadDef\", \"NotDefTail\",
        \"TailDef\", \"FoldrNil\", \"FoldrCons\", \"FoldlNil\",
        \"FoldlCons\", \"MapNil\", \"MapCons\", \"XPlusXPlusNil\",
        \"XPlusXPlusCons\", \"FilterNil\", \"FilterConsT\",
        \"FilterConsF\", \"ZipNil\", \"ZipConsNil\", \"ZipConsCons\",
        \"UnzipNil\", \"UnzipCons\", \"ILE01\", \"ILE02\", \"ILO01\",
        \"ILO02\", \"ILO03\", \"ILO04\", \"ILO05\", \"ILO06\", \"ILO07\",
        \"ILO08\", \"ILO09\", \"ILO10\", \"ILO11\", \"ILO12\", \"ILO13\",
        \"ILO14\", \"ILO15\", \"ILO16\", \"ILO17\", \"ILO18\", \"ILO19\",
        \"ILO20\", \"ILO21\", \"ILO22\", \"FoldlDecomp\", \"MapDecomp\",
        \"MapFunctor\", \"FilterProm\", \"InitNil\", \"InitConsNil\",
        \"InitConsCons\", \"LastNil\", \"LastConsNil\", \"LastConsCons\",
        \"NullNil\", \"NullCons\", \"ReverseNil\", \"ReverseCons\",
        \"Foldr1Nil\", \"Foldr1ConsNil\", \"Foldr1ConsCons\",
        \"Foldl1Nil\", \"Foldl1ConsNil\", \"Foldl1ConsCons\", \"ScanlNil\",
        \"ScanlCons\", \"Scanl1Nil\", \"Scanl1Cons\", \"ScanrNil\",
        \"ScanrCons\", \"Scanr1Nil\", \"Scanr1ConsNil\",
        \"Scanr1ConsCons\", \"ScanlProperty\", \"ScanrProperty\",
        \"AndLNil\", \"AndLCons\", \"OrLNil\", \"OrLCons\", \"AnyDef\",
        \"AllDef\", \"ConcatDef\", \"ConcatMapDef\", \"MaximunNil\",
        \"MaximumDef\", \"MinimunNil\", \"MinimumDef\", \"TakeWhileNil\",
        \"TakeWhileConsT\", \"TakeWhileConsF\", \"DropWhileNil\",
        \"DropWhileConsT\", \"DropWhileConsF\", \"SpanNil\", \"SpanConsT\",
        \"SpanConsF\", \"SpanThm\", \"BreakDef\", \"BreakThm\",
        \"InsertNil\", \"InsertCons1\", \"InsertCons2\", \"DeleteNil\",
        \"DeleteConsT\", \"DeleteConsF\", \"SelectT\", \"SelectF\",
        \"Partition\", \"PartitionProp\", \"PartialTest\",
        \"QuickSortNil\", \"QuickSortCons\", \"InsertionSortNil\",
        \"InsertionSortConsCons\", \"InsertionSortConsNil\", \"Program01\",
        \"Program02\", \"Program03\", \"Program04\"]"

typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")
datatype Ordering = EQ | GT | LT
datatype 'a List = X_Cons 'a "'a List" | X_Nil ("Nil''")

consts
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
X_all :: "('a => Bool) => 'a List => Bool"
X_andL :: "Bool List => Bool" ("andL/'(_')" [3] 999)
X_any :: "('a => Bool) => 'a List => Bool"
X_concat :: "'a List List => 'a List" ("concat''/'(_')" [3] 999)
X_curry :: "('a * 'b => 'c) => 'a => 'b => 'c"
X_dropWhile :: "('a => Bool) => 'a List => 'a List"
X_filter :: "('a => Bool) => 'a List => 'a List"
X_flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
X_foldl :: "('a => 'b => 'a) => 'a => 'b List => 'a partial"
X_foldr :: "('a => 'b => 'b) => 'b => 'a List => 'b partial"
X_fst :: "'a => 'b => 'a" ("fst''/'(_,/ _')" [3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a => 'a" ("id''/'(_')" [3] 999)
X_init :: "'a List => 'a List partial" ("init/'(_')" [3] 999)
X_insert :: "'d => 'd List => 'd List"
X_insertionSort :: "'a List => 'a List" ("insertionSort/'(_')" [3] 999)
X_last :: "'a List => 'a partial" ("last''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_max :: "'a => 'a => 'a"
X_maximum :: "'d List => 'd partial" ("maximum/'(_')" [3] 999)
X_min :: "'a => 'a => 'a"
X_minimum :: "'d List => 'd partial" ("minimum/'(_')" [3] 999)
X_null :: "'a List => Bool" ("null''/'(_')" [3] 999)
X_orL :: "Bool List => Bool" ("orL/'(_')" [3] 999)
X_quickSort :: "'a List => 'a List" ("quickSort/'(_')" [3] 999)
X_reverse :: "'a List => 'a List" ("reverse/'(_')" [3] 999)
X_snd :: "'a => 'b => 'b" ("snd''/'(_,/ _')" [3,3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_takeWhile :: "('a => Bool) => 'a List => 'a List"
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List"
break :: "('a => Bool) => 'a List => 'a List * 'a List"
compare :: "'a => 'a => Ordering"
concatMap :: "('a => 'b List) => 'a List => 'b List"
delete :: "'e => 'e List => 'e List"
foldl1 :: "('a => 'a => 'a) => 'a List => 'a partial"
foldr1 :: "('a => 'a => 'a) => 'a List => 'a partial"
notH__X :: "Bool => Bool" ("(notH/ _)" [56] 56)
otherwiseH :: "Bool"
partition :: "('a => Bool) => 'a List => 'a List * 'a List"
scanl :: "('a => 'b => 'a) => 'a => 'b List => 'a List"
scanl1 :: "('a => 'a => 'a) => 'a List => 'a List"
scanr :: "('a => 'b => 'b) => 'b => 'a List => 'b List"
scanr1 :: "('a => 'a => 'a) => 'a List => 'a List"
select :: "('a => Bool) => 'a => 'a List * 'a List => 'a List * 'a List"
span :: "('a => Bool) => 'a List => 'a List * 'a List"
uncurry :: "('a => 'b => 'c) => 'a * 'b => 'c"

axioms
Comp1 [rule_format] :
"ALL (f :: 'b => 'c).
 ALL (g :: 'a => 'b). ALL (y :: 'a). X__o__X (f, g) y = f (g y)"

IdDef [rule_format] : "ALL (x :: 'a). id'(x) = x"

FlipDef [rule_format] :
"ALL (f :: 'a => 'b => 'c).
 ALL (x :: 'a). ALL (y :: 'b). X_flip f y x = f x y"

FstDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'b). fst'(x, y) = x"

SndDef [rule_format] :
"ALL (x :: 'a). ALL (y :: 'b). snd'(x, y) = y"

CurryDef [rule_format] :
"ALL (g :: 'a * 'b => 'c).
 ALL (x :: 'a). ALL (y :: 'b). X_curry g x y = g (x, y)"

UncurryDef [rule_format] :
"ALL (f :: 'a => 'b => 'c).
 ALL (x :: 'a). ALL (y :: 'b). uncurry f (x, y) = f x y"

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

NotDefHead [rule_format] : "~ defOp (head(Nil'))"

HeadDef [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List). head(X_Cons x xs) = makePartial x"

NotDefTail [rule_format] : "~ defOp (tail(Nil'))"

TailDef [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List). tail(X_Cons x xs) = makePartial xs"

FoldrNil [rule_format] :
"ALL (f :: 'a => 'b => 'b).
 ALL (s :: 'b). X_foldr f s Nil' = makePartial s"

FoldrCons [rule_format] :
"ALL (f :: 'a => 'b => 'b).
 ALL (s :: 'b).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 X_foldr f s (X_Cons x xs) =
 restrictOp (makePartial (f x (makeTotal (X_foldr f s xs))))
 (defOp (X_foldr f s xs))"

FoldlNil [rule_format] :
"ALL (g :: 'a => 'b => 'a).
 ALL (t :: 'a). X_foldl g t Nil' = makePartial t"

FoldlCons [rule_format] :
"ALL (g :: 'a => 'b => 'a).
 ALL (t :: 'a).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_foldl g t (X_Cons z zs) = X_foldl g (g t z) zs"

MapNil [rule_format] : "ALL (h :: 'a => 'b). X_map h Nil' = Nil'"

MapCons [rule_format] :
"ALL (h :: 'a => 'b).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 X_map h (X_Cons x xs) = X_Cons (h x) (X_map h xs)"

XPlusXPlusNil [rule_format] : "ALL (l :: 'a List). Nil' ++' l = l"

XPlusXPlusCons [rule_format] :
"ALL (l :: 'a List).
 ALL (x :: 'a).
 ALL (xs :: 'a List). X_Cons x xs ++' l = X_Cons x (xs ++' l)"

FilterNil [rule_format] :
"ALL (p :: 'a => Bool). X_filter p Nil' = Nil'"

FilterConsT [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = True' -->
 X_filter p (X_Cons x xs) = X_Cons x (X_filter p xs)"

FilterConsF [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = False' --> X_filter p (X_Cons x xs) = X_filter p xs"

ZipNil [rule_format] : "ALL (l :: 'a List). X_zip Nil' l = Nil'"

ZipConsNil [rule_format] :
"ALL (l :: 'a List).
 ALL (x :: 'a).
 ALL (xs :: 'a List). l = Nil' --> X_zip (X_Cons x xs) l = Nil'"

ZipConsCons [rule_format] :
"ALL (l :: 'a List).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (y :: 'a).
 ALL (ys :: 'a List).
 l = X_Cons y ys -->
 X_zip (X_Cons x xs) l = X_Cons (x, y) (X_zip xs ys)"

UnzipNil [rule_format] : "unzip(Nil') = (Nil', Nil')"

UnzipCons [rule_format] :
"ALL (ps :: ('a * 'b) List).
 ALL (x :: 'a).
 ALL (z :: 'b).
 unzip(X_Cons (x, z) ps) =
 (let (ys, zs) = unzip(ps) in (X_Cons x ys, X_Cons z zs))"

ILE01 [rule_format] : "Nil' ==' Nil' = True'"

ILE02 [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (y :: 'a).
 ALL (ys :: 'a List).
 X_Cons x xs ==' X_Cons y ys = (x ==' y) && (xs ==' ys)"

ILO01 [rule_format] : "Nil' <' Nil' = False'"

ILO02 [rule_format] : "Nil' <=' Nil' = True'"

ILO03 [rule_format] : "Nil' >' Nil' = False'"

ILO04 [rule_format] : "Nil' >=' Nil' = True'"

ILO05 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 z <' w = True' --> X_Cons z zs <' X_Cons w ws = True'"

ILO06 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 z ==' w = True' --> X_Cons z zs <' X_Cons w ws = zs <' ws"

ILO07 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 z <' w = False' & z ==' w = False' -->
 X_Cons z zs <' X_Cons w ws = False'"

ILO08 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons z zs <=' X_Cons w ws =
 (X_Cons z zs <' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO09 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons z zs >' X_Cons w ws = X_Cons w ws <' X_Cons z zs"

ILO10 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons z zs >=' X_Cons w ws =
 (X_Cons z zs >' X_Cons w ws) || (X_Cons z zs ==' X_Cons w ws)"

ILO11 [rule_format] : "compare Nil' Nil' ==' EQ = Nil' ==' Nil'"

ILO12 [rule_format] : "compare Nil' Nil' ==' LT = Nil' <' Nil'"

ILO13 [rule_format] : "compare Nil' Nil' ==' GT = Nil' >' Nil'"

ILO14 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 compare (X_Cons z zs) (X_Cons w ws) ==' EQ =
 X_Cons z zs ==' X_Cons w ws"

ILO15 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 compare (X_Cons z zs) (X_Cons w ws) ==' LT =
 X_Cons z zs <' X_Cons w ws"

ILO16 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 compare (X_Cons z zs) (X_Cons w ws) ==' GT =
 X_Cons z zs >' X_Cons w ws"

ILO17 [rule_format] : "X_max Nil' Nil' ==' Nil' = Nil' <=' Nil'"

ILO18 [rule_format] : "X_min Nil' Nil' ==' Nil' = Nil' <=' Nil'"

ILO19 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons z zs <=' X_Cons w ws =
 X_max (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

ILO20 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons w ws <=' X_Cons z zs =
 X_max (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO21 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons z zs <=' X_Cons w ws =
 X_min (X_Cons z zs) (X_Cons w ws) ==' X_Cons z zs"

ILO22 [rule_format] :
"ALL (w :: 'b).
 ALL (ws :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 X_Cons w ws <=' X_Cons z zs =
 X_min (X_Cons z zs) (X_Cons w ws) ==' X_Cons w ws"

FoldlDecomp [rule_format] :
"ALL (e :: 'a).
 ALL (i :: 'a => 'b => 'a).
 ALL (ts :: 'b List).
 ALL (ys :: 'b List).
 X_foldl i e (ys ++' ts) =
 restrictOp (X_foldl i (makeTotal (X_foldl i e ys)) ts)
 (defOp (X_foldl i e ys))"

MapDecomp [rule_format] :
"ALL (f :: 'a => 'b).
 ALL (xs :: 'a List).
 ALL (zs :: 'a List).
 X_map f (xs ++' zs) = X_map f xs ++' X_map f zs"

MapFunctor [rule_format] :
"ALL (f :: 'a => 'b).
 ALL (g :: 'b => 'c).
 ALL (xs :: 'a List).
 X_map (X__o__X (g, f)) xs = X_map g (X_map f xs)"

FilterProm [rule_format] :
"ALL (f :: 'a => 'b).
 ALL (p :: 'b => Bool).
 ALL (xs :: 'a List).
 X_filter p (X_map f xs) = X_map f (X_filter (X__o__X (p, f)) xs)"

InitNil [rule_format] : "~ defOp (init(Nil'))"

InitConsNil [rule_format] :
"ALL (x :: 'a). init(X_Cons x Nil') = makePartial Nil'"

InitConsCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 init(X_Cons x xs) =
 restrictOp (makePartial (X_Cons x (makeTotal (init(xs)))))
 (defOp (init(xs)))"

LastNil [rule_format] : "~ defOp (last'(Nil'))"

LastConsNil [rule_format] :
"ALL (x :: 'a). last'(X_Cons x Nil') = makePartial x"

LastConsCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List). last'(X_Cons x xs) = last'(xs)"

NullNil [rule_format] : "null'(Nil') = True'"

NullCons [rule_format] :
"ALL (x :: 'a). ALL (xs :: 'a List). null'(X_Cons x xs) = False'"

ReverseNil [rule_format] : "reverse(Nil') = Nil'"

ReverseCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 reverse(X_Cons x xs) = reverse(xs) ++' X_Cons x Nil'"

Foldr1Nil [rule_format] :
"ALL (f :: 'a => 'a => 'a). ~ defOp (foldr1 f Nil')"

Foldr1ConsNil [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a). foldr1 f (X_Cons x Nil') = makePartial x"

Foldr1ConsCons [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 foldr1 f (X_Cons x xs) =
 restrictOp (makePartial (f x (makeTotal (foldr1 f xs))))
 (defOp (foldr1 f xs))"

Foldl1Nil [rule_format] :
"ALL (f :: 'a => 'a => 'a). ~ defOp (foldl1 f Nil')"

Foldl1ConsNil [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a). foldl1 f (X_Cons x Nil') = makePartial x"

Foldl1ConsCons [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 foldl1 f (X_Cons x xs) =
 restrictOp (makePartial (f x (makeTotal (foldr1 f xs))))
 (defOp (foldr1 f xs))"

ScanlNil [rule_format] :
"ALL (g :: 'a => 'b => 'a).
 ALL (q :: 'a).
 ALL (ys :: 'b List). ys = Nil' --> scanl g q ys = X_Cons q Nil'"

ScanlCons [rule_format] :
"ALL (g :: 'a => 'b => 'a).
 ALL (q :: 'a).
 ALL (ys :: 'b List).
 ALL (z :: 'b).
 ALL (zs :: 'b List).
 ys = X_Cons z zs --> scanl g q ys = X_Cons q (scanl g (g q z) zs)"

Scanl1Nil [rule_format] :
"ALL (f :: 'a => 'a => 'a). scanl1 f Nil' = Nil'"

Scanl1Cons [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a).
 ALL (xs :: 'a List). scanl1 f (X_Cons x xs) = scanl f x xs"

ScanrNil [rule_format] :
"ALL (h :: 'a => 'b => 'b).
 ALL (z :: 'b). scanr h z Nil' = X_Cons z Nil'"

ScanrCons [rule_format] :
"ALL (h :: 'a => 'b => 'b).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (y :: 'b).
 ALL (ys :: 'b List).
 ALL (z :: 'b).
 X_Cons y ys = scanr h z xs -->
 scanr h z (X_Cons x xs) = X_Cons (h x y) (X_Cons y ys)"

Scanr1Nil [rule_format] :
"ALL (f :: 'a => 'a => 'a). scanr1 f Nil' = Nil'"

Scanr1ConsNil [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (x :: 'a). scanr1 f (X_Cons x Nil') = X_Cons x Nil'"

Scanr1ConsCons [rule_format] :
"ALL (f :: 'a => 'a => 'a).
 ALL (q :: 'a).
 ALL (qs :: 'a List).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 X_Cons q qs = scanr1 f xs -->
 scanr1 f (X_Cons x xs) = X_Cons (f x q) (X_Cons q qs)"

ScanlProperty [rule_format] :
"ALL (g :: 'a => 'b => 'a).
 ALL (x :: 'a).
 ALL (ys :: 'b List). last'(scanl g x ys) = X_foldl g x ys"

ScanrProperty [rule_format] :
"ALL (h :: 'a => 'b => 'b).
 ALL (xs :: 'a List).
 ALL (y :: 'b). head(scanr h y xs) = X_foldr h y xs"

AndLNil [rule_format] : "andL(Nil') = True'"

AndLCons [rule_format] :
"ALL (b1 :: Bool).
 ALL (bs :: Bool List). andL(X_Cons b1 bs) = b1 && andL(bs)"

OrLNil [rule_format] : "orL(Nil') = False'"

OrLCons [rule_format] :
"ALL (b1 :: Bool).
 ALL (bs :: Bool List). orL(X_Cons b1 bs) = b1 || orL(bs)"

AnyDef [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List). X_any p xs = orL(X_map p xs)"

AllDef [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List). X_all p xs = andL(X_map p xs)"

ConcatDef [rule_format] :
"ALL (xxs :: 'a List List).
 makePartial (concat'(xxs)) =
 X_foldr (X_curry (uncurryOp X__XPlusXPlus__X)) Nil' xxs"

ConcatMapDef [rule_format] :
"ALL (g :: 'a => 'b List).
 ALL (xs :: 'a List). concatMap g xs = concat'(X_map g xs)"

MaximunNil [rule_format] : "~ defOp (maximum(Nil'))"

MaximumDef [rule_format] :
"ALL (ds :: 'd List). maximum(ds) = foldl1 X_max ds"

MinimunNil [rule_format] : "~ defOp (minimum(Nil'))"

MinimumDef [rule_format] :
"ALL (ds :: 'd List). minimum(ds) = foldl1 X_min ds"

TakeWhileNil [rule_format] :
"ALL (p :: 'a => Bool). X_takeWhile p Nil' = Nil'"

TakeWhileConsT [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = True' -->
 X_takeWhile p (X_Cons x xs) = X_Cons x (X_takeWhile p xs)"

TakeWhileConsF [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = False' --> X_takeWhile p (X_Cons x xs) = Nil'"

DropWhileNil [rule_format] :
"ALL (p :: 'a => Bool). X_dropWhile p Nil' = Nil'"

DropWhileConsT [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = True' --> X_dropWhile p (X_Cons x xs) = X_dropWhile p xs"

DropWhileConsF [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = False' --> X_dropWhile p (X_Cons x xs) = X_Cons x xs"

SpanNil [rule_format] :
"ALL (p :: 'a => Bool). span p Nil' = (Nil', Nil')"

SpanConsT [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = True' -->
 span p (X_Cons x xs) =
 (let (ys, zs) = span p xs in (X_Cons x ys, zs))"

SpanConsF [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 p x = False' -->
 span p (X_Cons x xs) =
 (let (ys, zs) = span p xs in (Nil', X_Cons x xs))"

SpanThm [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List).
 span p xs = (X_takeWhile p xs, X_dropWhile p xs)"

BreakDef [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List).
 break p xs = (let q = X__o__X (notH__X, p) in span q xs)"

BreakThm [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List). break p xs = span (X__o__X (notH__X, p)) xs"

InsertNil [rule_format] :
"ALL (q :: 'd). X_insert q Nil' = X_Cons q Nil'"

InsertCons1 [rule_format] :
"ALL (q :: 'd).
 ALL (r :: 'd).
 ALL (rs :: 'd List).
 q <=' r = True' -->
 X_insert q (X_Cons r rs) = X_Cons q (X_Cons r rs)"

InsertCons2 [rule_format] :
"ALL (q :: 'd).
 ALL (r :: 'd).
 ALL (rs :: 'd List).
 q >' r = True' -->
 X_insert q (X_Cons r rs) = X_Cons r (X_insert q rs)"

DeleteNil [rule_format] : "ALL (s :: 'e). delete s Nil' = Nil'"

DeleteConsT [rule_format] :
"ALL (s :: 'e).
 ALL (t :: 'e).
 ALL (ts :: 'e List).
 s ==' t = True' --> delete s (X_Cons t ts) = ts"

DeleteConsF [rule_format] :
"ALL (s :: 'e).
 ALL (t :: 'e).
 ALL (ts :: 'e List).
 s ==' t = False' -->
 delete s (X_Cons t ts) = X_Cons t (delete s ts)"

SelectT [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (ys :: 'a List).
 p x = True' --> select p x (xs, ys) = (X_Cons x xs, ys)"

SelectF [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (ys :: 'a List).
 p x = False' --> select p x (xs, ys) = (xs, X_Cons x ys)"

Partition [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List).
 makePartial (partition p xs) = X_foldr (select p) (Nil', Nil') xs"

PartitionProp [rule_format] :
"ALL (p :: 'a => Bool).
 ALL (xs :: 'a List).
 partition p xs =
 (X_filter p xs, X_filter (X__o__X (notH__X, p)) xs)"

PartialTest [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 makePartial (X_Cons x xs) =
 restrictOp
 (makePartial
  (X_Cons (makeTotal (head(X_Cons x xs)))
   (makeTotal (tail(X_Cons x xs)))))
 (defOp (head(X_Cons x xs)) & defOp (tail(X_Cons x xs)))"

QuickSortNil [rule_format] : "quickSort(Nil') = Nil'"

QuickSortCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 quickSort(X_Cons x xs) =
 (quickSort(X_filter (% y. y <' x) xs) ++' X_Cons x Nil') ++'
 quickSort(X_filter (% y. y >=' x) xs)"

InsertionSortNil [rule_format] : "insertionSort(Nil') = Nil'"

InsertionSortConsCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 insertionSort(X_Cons x xs) = X_insert x (insertionSort(xs))"

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
declare Scanl1Nil [simp]
declare Scanl1Cons [simp]
declare ScanrNil [simp]
declare Scanr1Nil [simp]
declare Scanr1ConsNil [simp]
declare ScanlProperty [simp]
declare ScanrProperty [simp]
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
declare DeleteNil [simp]
declare DeleteConsT [simp]
declare SelectT [simp]
declare SelectF [simp]
declare QuickSortNil [simp]
declare InsertionSortNil [simp]

theorem InsertionSortConsNil :
"ALL (x :: 'a). insertionSort(X_Cons x Nil') = X_Cons x Nil'"
apply(auto)
apply(simp add: InsertionSortConsCons)
apply(simp add: InsertNil)
done

setup "Header.record \"InsertionSortConsNil\""

theorem Program01 :
"andL(X_Cons True' (X_Cons True' (X_Cons True' Nil'))) = True'"
apply(simp add: AndLCons AndLNil)
done

setup "Header.record \"Program01\""

theorem Program02 :
"quickSort(X_Cons True' (X_Cons False' Nil')) =
 X_Cons False' (X_Cons True' Nil')"
apply(simp only: QuickSortCons)
apply(case_tac "(%y. y <' True') False'")
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
apply(case_tac "(%y. y >=' True') False'")
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp add: LeFGeTEqTRel)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortCons)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
apply(simp only: IBO5)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortCons)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
apply(case_tac "(%y. y >=' True') False'")
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortCons)
apply(simp only: FilterNil FilterConsT FilterConsF)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
apply(simp add: LeFGeTEqTRel)
done

setup "Header.record \"Program02\""

theorem Program03 :
"insertionSort(X_Cons True' (X_Cons False' Nil')) =
 X_Cons False' (X_Cons True' Nil')"
apply(simp only: InsertionSortConsCons)
apply(simp only: InsertionSortNil)
apply(simp only: InsertNil)
apply(case_tac "True' >' False'")
apply(simp only: GeFLeTEqTRel)
apply(simp add: LeqTLeTEqTRel)
apply(simp only: InsertCons2)
apply(simp only: InsertNil)
done

setup "Header.record \"Program03\""

theorem Program04 :
"ALL (xs :: 'a List). insertionSort(xs) = quickSort(xs)"
apply(auto)
apply(case_tac xs)
prefer 2
apply(simp only: InsertionSortNil QuickSortNil)
(* general case*)
(*
apply(auto)
apply(simp only: InsertionSortConsCons)
apply(simp only: QuickSortCons)
apply(induct_tac List)
apply(case_tac "y <' a")
apply(simp)
apply(simp only: FilterConsF)
apply(case_tac "aa >=' a")
apply(simp only: FilterConsF)
apply(simp only:InsertionSortConsCons)
apply(induct_tac Lista)
apply(case_tac "(ab <' a)")
apply(simp only: FilterConsF)
apply(case_tac "ab >=' a")
apply(simp only: FilterConsF)
apply(simp only:InsertionSortConsCons)
oops

apply(simp only: LeFGeTEqTRel)
apply(simp only: GeqFGeFEqFRel)
apply (erule disjE)


apply(simp only:  LeqFGeTRel InsertCons2)


apply(induct_tac List)
apply(case_tac "quickSort(List)")
apply(auto)
apply(case_tac "a <='' aa")
apply(simp only:  LeqFGeTRel InsertCons2)
apply(simp only: QuickSortCons)
apply(induct_tac List)
apply(case_tac "ab <'' a")
apply(simp only: FilterConsT FilterConsF)
apply(case_tac "ab >='' a")
apply(simp only: FilterConsT FilterConsF)
apply(simp only: FilterConsT)
apply(case_tac "quickSort(X_filter (%y. y <'' a) Listb)")
apply(simp only: XPlusXPlusCons)+





apply(case_tac List)
(*Cons x Nil*)
prefer 2
apply(simp only: InsertionSortConsNil)
apply(simp only: QuickSortCons)
apply(simp only: FilterNil)
apply(simp only: QuickSortNil)
apply(simp only: XPlusXPlusNil)
apply(simp only: XPlusXPlusCons)
apply(simp only: XPlusXPlusNil)
(*Cons x xx*)
apply(induct_tac Lista)
apply(simp only: QuickSortCons)
apply(simp only: QuickSortCons)
apply(simp only: InsertionSortConsCons)
apply(case_tac "(insertionSort(Lista))")
apply(simp only: InsertionSortConsCons)
apply(case_tac "aa <'' a")
apply(case_tac "aa >='' a")
apply(simp only: FilterConsF)
apply(simp only: GeqFLeTRel)
apply(simp add: IBE3)
apply(auto)
*)
oops

setup "Header.record \"Program04\""

end
