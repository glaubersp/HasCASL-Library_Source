theory Prelude_SortingPrograms__E3
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"ga_monotonicity\", \"ga_monotonicity_1\", \"ga_monotonicity_2\",
        \"ga_monotonicity_3\", \"ga_monotonicity_4\",
        \"ga_monotonicity_5\", \"ga_monotonicity_6\",
        \"ga_monotonicity_7\", \"ga_monotonicity_8\",
        \"ga_monotonicity_9\", \"ga_monotonicity_10\",
        \"ga_monotonicity_11\", \"ga_monotonicity_12\",
        \"ga_monotonicity_13\", \"ga_monotonicity_14\",
        \"ga_monotonicity_15\", \"ga_monotonicity_16\",
        \"ga_monotonicity_17\", \"ga_monotonicity_18\",
        \"ga_monotonicity_19\", \"ga_monotonicity_20\",
        \"ga_monotonicity_21\", \"ga_monotonicity_22\",
        \"ga_monotonicity_23\", \"ga_monotonicity_24\",
        \"ga_monotonicity_25\", \"ga_monotonicity_26\",
        \"ga_monotonicity_27\", \"ga_monotonicity_28\",
        \"ga_monotonicity_29\", \"ga_monotonicity_30\",
        \"ga_monotonicity_31\", \"ga_monotonicity_32\",
        \"ga_monotonicity_33\", \"ga_monotonicity_34\",
        \"ga_monotonicity_35\", \"ga_monotonicity_36\",
        \"ga_monotonicity_37\", \"ga_monotonicity_38\",
        \"ga_monotonicity_39\", \"ga_monotonicity_40\",
        \"ga_monotonicity_41\", \"ga_monotonicity_42\",
        \"ga_monotonicity_43\", \"ga_monotonicity_44\",
        \"ga_monotonicity_45\", \"ga_monotonicity_46\",
        \"ga_monotonicity_47\", \"ga_monotonicity_48\",
        \"ga_monotonicity_49\", \"ga_monotonicity_50\",
        \"ga_monotonicity_51\", \"ga_monotonicity_52\",
        \"ga_monotonicity_53\", \"ga_monotonicity_54\",
        \"ga_monotonicity_55\", \"ga_monotonicity_56\",
        \"ga_monotonicity_57\", \"ga_monotonicity_58\",
        \"ga_monotonicity_59\", \"ga_monotonicity_60\",
        \"ga_monotonicity_61\", \"ga_monotonicity_62\",
        \"ga_monotonicity_63\", \"ga_monotonicity_64\",
        \"ga_monotonicity_65\", \"ga_monotonicity_66\",
        \"ga_monotonicity_67\", \"ga_monotonicity_68\",
        \"ga_monotonicity_69\", \"ga_monotonicity_70\",
        \"ga_monotonicity_71\", \"ga_monotonicity_72\",
        \"ga_monotonicity_73\", \"ga_monotonicity_74\",
        \"ga_monotonicity_75\", \"ga_monotonicity_76\",
        \"ga_monotonicity_77\", \"ga_monotonicity_78\",
        \"ga_monotonicity_79\", \"ga_monotonicity_80\",
        \"ga_monotonicity_81\", \"ga_monotonicity_82\",
        \"ga_monotonicity_83\", \"ga_monotonicity_84\",
        \"ga_monotonicity_85\", \"ga_monotonicity_86\",
        \"ga_monotonicity_87\", \"ga_monotonicity_88\",
        \"ga_monotonicity_89\", \"ga_monotonicity_90\",
        \"ga_subt_reflexive\", \"ga_subt_transitive\",
        \"ga_subt_inj_proj\", \"ga_inj_transitive\",
        \"ga_subt_Int_XLt_Rat\", \"ga_subt_Nat_XLt_Int\",
        \"ga_subt_Pos_XLt_Nat\", \"GenSortT1\", \"GenSortT2\",
        \"GenSortF\", \"SplitInsertionSort\", \"JoinInsertionSort\",
        \"InsertionSort\", \"SplitQuickSort\", \"JoinQuickSort\",
        \"QuickSort\", \"SplitSelectionSort\", \"JoinSelectionSort\",
        \"SelectionSort\", \"SplitMergeSort\", \"MergeNil\",
        \"MergeConsNil\", \"MergeConsConsT\", \"MergeConsConsF\",
        \"JoinMergeSort\", \"MergeSort\", \"ElemNil\", \"ElemCons\",
        \"IsOrderedNil\", \"IsOrderedCons\", \"IsOrderedConsCons\",
        \"PermutationNil\", \"PermutationConsCons\", \"PermutationCons\",
        \"Theorem01\", \"Theorem02\", \"Theorem03\", \"Theorem04\",
        \"Theorem05\", \"Theorem06\", \"Theorem07\", \"Theorem08\",
        \"Theorem09\", \"Theorem10\", \"Theorem11\", \"Theorem12\",
        \"Theorem13\", \"Theorem14\"]"

typedecl Bool
typedecl ('a1) List
typedecl Ordering
typedecl Pos
typedecl Rat
typedecl Unit
typedecl X_Int
typedecl X_Nat

datatype ('a, 'b) Split = X_Split 'b "'a List List"

consts
EQ :: "Ordering"
GT :: "Ordering"
LT :: "Ordering"
X0X1 :: "X_Int" ("0''")
X0X2 :: "X_Nat" ("0''''")
X0X3 :: "Rat" ("0'_3")
X1X1 :: "X_Int" ("1''")
X1X2 :: "X_Nat" ("1''''")
X1X3 :: "Pos" ("1'_3")
X1X4 :: "Rat" ("1'_4")
X2X1 :: "X_Int" ("2''")
X2X2 :: "X_Nat" ("2''''")
X2X3 :: "Rat" ("2'_3")
X3X1 :: "X_Int" ("3''")
X3X2 :: "X_Nat" ("3''''")
X3X3 :: "Rat" ("3'_3")
X4X1 :: "X_Int" ("4''")
X4X2 :: "X_Nat" ("4''''")
X4X3 :: "Rat" ("4'_3")
X5X1 :: "X_Int" ("5''")
X5X2 :: "X_Nat" ("5''''")
X5X3 :: "Rat" ("5'_3")
X6X1 :: "X_Int" ("6''")
X6X2 :: "X_Nat" ("6''''")
X6X3 :: "Rat" ("6'_3")
X7X1 :: "X_Int" ("7''")
X7X2 :: "X_Nat" ("7''''")
X7X3 :: "Rat" ("7'_3")
X8X1 :: "X_Int" ("8''")
X8X2 :: "X_Nat" ("8''''")
X8X3 :: "Rat" ("8'_3")
X9X1 :: "X_Int" ("9''")
X9X2 :: "X_Nat" ("9''''")
X9X3 :: "Rat" ("9'_3")
XMinus__XX1 :: "X_Int => X_Int" ("(-''/ _)" [56] 56)
XMinus__XX2 :: "Rat => Rat" ("(-''''/ _)" [56] 56)
X_Cons :: "'a => 'a List => 'a List"
X_False :: "Bool" ("False''")
X_Nil :: "'a List" ("Nil''")
X_True :: "Bool" ("True''")
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XAtXAt__X :: "X_Nat => X_Nat => X_Nat" ("(_/ @@/ _)" [54,54] 52)
X__XCaret__XX1 :: "X_Int => X_Nat => X_Int" ("(_/ ^''/ _)" [54,54] 52)
X__XCaret__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ ^''''/ _)" [54,54] 52)
X__XCaret__XX3 :: "Rat => X_Int => Rat partial" ("(_/ ^'_3/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XExclam :: "X_Nat => X_Nat" ("(_/ !'')" [58] 58)
X__XGtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ >=''/ _)" [44,44] 42)
X__XGtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >=''''/ _)" [44,44] 42)
X__XGtXEq__XX3 :: "Rat => Rat => bool" ("(_/ >='_3/ _)" [44,44] 42)
X__XGtXEq__XX4 :: "'a => 'a => Bool" ("(_/ >='_4/ _)" [54,54] 52)
X__XGt__XX1 :: "X_Int => X_Int => bool" ("(_/ >''/ _)" [44,44] 42)
X__XGt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ >''''/ _)" [44,44] 42)
X__XGt__XX3 :: "Rat => Rat => bool" ("(_/ >'_3/ _)" [44,44] 42)
X__XGt__XX4 :: "'a => 'a => Bool" ("(_/ >'_4/ _)" [54,54] 52)
X__XLtXEq__XX1 :: "X_Int => X_Int => bool" ("(_/ <=''/ _)" [44,44] 42)
X__XLtXEq__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <=''''/ _)" [44,44] 42)
X__XLtXEq__XX3 :: "Rat => Rat => bool" ("(_/ <='_3/ _)" [44,44] 42)
X__XLtXEq__XX4 :: "'a => 'a => Bool" ("(_/ <='_4/ _)" [54,54] 52)
X__XLt__XX1 :: "X_Int => X_Int => bool" ("(_/ <''/ _)" [44,44] 42)
X__XLt__XX2 :: "X_Nat => X_Nat => bool" ("(_/ <''''/ _)" [44,44] 42)
X__XLt__XX3 :: "Rat => Rat => bool" ("(_/ <'_3/ _)" [44,44] 42)
X__XLt__XX4 :: "'a => 'a => Bool" ("(_/ <'_4/ _)" [54,54] 52)
X__XMinusXExclam__X :: "X_Nat => X_Nat => X_Nat" ("(_/ -!/ _)" [54,54] 52)
X__XMinusXQuest__X :: "X_Nat => X_Nat => X_Nat partial" ("(_/ -?/ _)" [54,54] 52)
X__XMinus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ -''/ _)" [54,54] 52)
X__XMinus__XX2 :: "X_Nat => X_Nat => X_Int" ("(_/ -''''/ _)" [54,54] 52)
X__XMinus__XX3 :: "Rat => Rat => Rat" ("(_/ -'_3/ _)" [54,54] 52)
X__XMinus__XX4 :: "'a => 'a => 'a" ("(_/ -'_4/ _)" [54,54] 52)
X__XPlusXPlus__X :: "'a List => 'a List => 'a List" ("(_/ ++''/ _)" [54,54] 52)
X__XPlus__XX1 :: "X_Int => X_Int => X_Int" ("(_/ +''/ _)" [54,54] 52)
X__XPlus__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ +''''/ _)" [54,54] 52)
X__XPlus__XX3 :: "X_Nat => Pos => Pos" ("(_/ +'_3/ _)" [54,54] 52)
X__XPlus__XX4 :: "Pos => X_Nat => Pos" ("(_/ +'_4/ _)" [54,54] 52)
X__XPlus__XX5 :: "Rat => Rat => Rat" ("(_/ +'_5/ _)" [54,54] 52)
X__XPlus__XX6 :: "'a => 'a => 'a" ("(_/ +'_6/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XSlashXQuest__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ '/?''/ _)" [54,54] 52)
X__XSlashXQuest__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ '/?''''/ _)" [54,54] 52)
X__XSlash__XX1 :: "X_Int => Pos => Rat" ("(_/ '/''/ _)" [54,54] 52)
X__XSlash__XX2 :: "Rat => Rat => Rat partial" ("(_/ '/''''/ _)" [54,54] 52)
X__XSlash__XX3 :: "'a => 'a => 'a" ("(_/ '/'_3/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
X__Xx__XX1 :: "X_Int => X_Int => X_Int" ("(_/ *''/ _)" [54,54] 52)
X__Xx__XX2 :: "X_Nat => X_Nat => X_Nat" ("(_/ *''''/ _)" [54,54] 52)
X__Xx__XX3 :: "Pos => Pos => Pos" ("(_/ *'_3/ _)" [54,54] 52)
X__Xx__XX4 :: "Rat => Rat => Rat" ("(_/ *'_4/ _)" [54,54] 52)
X__Xx__XX5 :: "'a => 'a => 'a" ("(_/ *'_5/ _)" [54,54] 52)
X__div__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ div''/ _)" [54,54] 52)
X__div__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ div''''/ _)" [54,54] 52)
X__div__XX3 :: "'a => 'a => 'a" ("(_/ div'_3/ _)" [54,54] 52)
X__dvd__X :: "X_Nat => X_Nat => bool" ("(_/ dvd''/ _)" [44,44] 42)
X__elem__X :: "'a => 'a List => bool" ("(_/ elem/ _)" [44,44] 42)
X__mod__XX1 :: "X_Int => X_Int => X_Nat partial" ("(_/ mod''/ _)" [54,54] 52)
X__mod__XX2 :: "X_Nat => X_Nat => X_Nat partial" ("(_/ mod''''/ _)" [54,54] 52)
X__mod__XX3 :: "'a => 'a => 'a" ("(_/ mod'_3/ _)" [54,54] 52)
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"
X__quot__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ quot''/ _)" [54,54] 52)
X__quot__XX2 :: "'a => 'a => 'a" ("(_/ quot''''/ _)" [54,54] 52)
X__rem__XX1 :: "X_Int => X_Int => X_Int partial" ("(_/ rem''/ _)" [54,54] 52)
X__rem__XX2 :: "'a => 'a => 'a" ("(_/ rem''''/ _)" [54,54] 52)
X_absX1 :: "X_Int => X_Nat" ("abs''/'(_')" [3] 999)
X_absX2 :: "Rat => Rat" ("abs''''/'(_')" [3] 999)
X_absX3 :: "'a => 'a" ("abs'_3/'(_')" [3] 999)
X_all :: "('a => Bool) => 'a List => Bool"
X_andL :: "Bool List => Bool" ("andL/'(_')" [3] 999)
X_any :: "('a => Bool) => 'a List => Bool"
X_concat :: "'a List List => 'a List" ("concat''/'(_')" [3] 999)
X_curry :: "('a * 'b => 'c) => 'a => 'b => 'c"
X_drop :: "X_Int => 'a List => 'a List"
X_dropWhile :: "('a => Bool) => 'a List => 'a List"
X_evenX1 :: "X_Int => bool" ("even''/'(_')" [3] 999)
X_evenX2 :: "X_Nat => bool" ("even''''/'(_')" [3] 999)
X_filter :: "('a => Bool) => 'a List => 'a List"
X_flip :: "('a => 'b => 'c) => 'b => 'a => 'c"
X_foldl :: "('a => 'b => 'a) => 'a => 'b List => 'a partial"
X_foldr :: "('a => 'b => 'b) => 'b => 'a List => 'b partial"
X_fromInteger :: "X_Int => 'a" ("fromInteger/'(_')" [3] 999)
X_fst :: "'a => 'b => 'a" ("fst''/'(_,/ _')" [3,3] 999)
X_gn_inj :: "'a => 'b" ("gn'_inj/'(_')" [3] 999)
X_gn_proj :: "'a => 'b partial" ("gn'_proj/'(_')" [3] 999)
X_gn_subt :: "'a => 'b => bool" ("gn'_subt/'(_,/ _')" [3,3] 999)
X_head :: "'a List => 'a partial" ("head/'(_')" [3] 999)
X_id :: "'a => 'a" ("id''/'(_')" [3] 999)
X_init :: "'a List => 'a List partial" ("init/'(_')" [3] 999)
X_insert :: "'d => 'd List => 'd List"
X_insertionSort :: "'a List => 'a List" ("insertionSort/'(_')" [3] 999)
X_isOrdered :: "'a List => bool" ("isOrdered/'(_')" [3] 999)
X_joinInsertionSort :: "('a, 'a) Split => 'a List" ("joinInsertionSort/'(_')" [3] 999)
X_joinMergeSort :: "('a, unit) Split => 'a List" ("joinMergeSort/'(_')" [3] 999)
X_joinQuickSort :: "('b, 'b) Split => 'b List" ("joinQuickSort/'(_')" [3] 999)
X_joinSelectionSort :: "('b, 'b) Split => 'b List" ("joinSelectionSort/'(_')" [3] 999)
X_last :: "'a List => 'a partial" ("last''/'(_')" [3] 999)
X_length :: "'a List => X_Int" ("length''/'(_')" [3] 999)
X_map :: "('a => 'b) => 'a List => 'b List"
X_maxX1 :: "X_Int => X_Int => X_Int" ("max''/'(_,/ _')" [3,3] 999)
X_maxX2 :: "X_Nat => X_Nat => X_Nat" ("max''''/'(_,/ _')" [3,3] 999)
X_maxX3 :: "Rat => Rat => Rat" ("max'_3/'(_,/ _')" [3,3] 999)
X_maxX4 :: "'a => 'a => 'a"
X_maximum :: "'d List => 'd partial" ("maximum/'(_')" [3] 999)
X_mergeSort :: "'a List => 'a List" ("mergeSort/'(_')" [3] 999)
X_minX1 :: "X_Int => X_Int => X_Int" ("min''/'(_,/ _')" [3,3] 999)
X_minX2 :: "X_Nat => X_Nat => X_Nat" ("min''''/'(_,/ _')" [3,3] 999)
X_minX3 :: "Rat => Rat => Rat" ("min'_3/'(_,/ _')" [3,3] 999)
X_minX4 :: "'a => 'a => 'a"
X_minimum :: "'d List => 'd partial" ("minimum/'(_')" [3] 999)
X_negate :: "'a => 'a" ("negate/'(_')" [3] 999)
X_null :: "'a List => Bool" ("null''/'(_')" [3] 999)
X_oddX1 :: "X_Int => bool" ("odd''/'(_')" [3] 999)
X_oddX2 :: "X_Nat => bool" ("odd''''/'(_')" [3] 999)
X_orL :: "Bool List => Bool" ("orL/'(_')" [3] 999)
X_permutation :: "'a List => 'a List => bool" ("permutation/'(_,/ _')" [3,3] 999)
X_pre :: "X_Nat => X_Nat partial" ("pre/'(_')" [3] 999)
X_product :: "'c List => 'c" ("product/'(_')" [3] 999)
X_quickSort :: "'a List => 'a List" ("quickSort/'(_')" [3] 999)
X_recip :: "'a => 'a" ("recip/'(_')" [3] 999)
X_reverse :: "'a List => 'a List" ("reverse/'(_')" [3] 999)
X_selectionSort :: "'a List => 'a List" ("selectionSort/'(_')" [3] 999)
X_sign :: "X_Int => X_Int" ("sign/'(_')" [3] 999)
X_signum :: "'a => 'a" ("signum/'(_')" [3] 999)
X_snd :: "'a => 'b => 'b" ("snd''/'(_,/ _')" [3,3] 999)
X_splitInsertionSort :: "'b List => ('b, 'b) Split" ("splitInsertionSort/'(_')" [3] 999)
X_splitMergeSort :: "'b List => ('b, unit) Split" ("splitMergeSort/'(_')" [3] 999)
X_splitQuickSort :: "'a List => ('a, 'a) Split" ("splitQuickSort/'(_')" [3] 999)
X_splitSelectionSort :: "'a List => ('a, 'a) Split" ("splitSelectionSort/'(_')" [3] 999)
X_sum :: "'c List => 'c" ("sum/'(_')" [3] 999)
X_tail :: "'a List => 'a List partial" ("tail/'(_')" [3] 999)
X_take :: "X_Int => 'a List => 'a List"
X_takeWhile :: "('a => Bool) => 'a List => 'a List"
X_toInteger :: "'a => X_Int" ("toInteger/'(_')" [3] 999)
X_unzip :: "('a * 'b) List => 'a List * 'b List" ("unzip/'(_')" [3] 999)
X_zip :: "'a List => 'b List => ('a * 'b) List"
break :: "('a => Bool) => 'a List => 'a List * 'a List"
compare :: "'a => 'a => Ordering"
concatMap :: "('a => 'b List) => 'a List => 'b List"
delete :: "'e => 'e List => 'e List"
divMod :: "'a => 'a => 'a * 'a"
foldl1 :: "('a => 'a => 'a) => 'a List => 'a partial"
foldr1 :: "('a => 'a => 'a) => 'a List => 'a partial"
genSort :: "('a List => ('a, 'b) Split) => (('a, 'b) Split => 'a List) => 'a List => 'a List"
merge :: "'a List => 'a List => 'a List"
notH__X :: "Bool => Bool" ("(notH/ _)" [56] 56)
otherwiseH :: "Bool"
partition :: "('a => Bool) => 'a List => 'a List * 'a List"
quotRem :: "'a => 'a => 'a * 'a"
scanl :: "('a => 'b => 'a) => 'a => 'b List => 'a List"
scanl1 :: "('a => 'a => 'a) => 'a List => 'a List"
scanr :: "('a => 'b => 'b) => 'b => 'a List => 'b List"
scanr1 :: "('a => 'a => 'a) => 'a List => 'a List"
select :: "('a => Bool) => 'a => 'a List * 'a List => 'a List * 'a List"
span :: "('a => Bool) => 'a List => 'a List * 'a List"
splitAt :: "X_Int => 'a List => 'a List * 'a List"
sucX1 :: "X_Nat => X_Nat" ("suc''/'(_')" [3] 999)
sucX2 :: "X_Nat => Pos" ("suc''''/'(_')" [3] 999)
uncurry :: "('a => 'b => 'c) => 'a * 'b => 'c"

axioms
ga_monotonicity [rule_format] :
"(X_gn_inj :: (X_Int => X_Int) => X_Int => Rat) XMinus__XX1 =
 (X_gn_inj :: (Rat => Rat) => X_Int => Rat) XMinus__XX2"

ga_monotonicity_1 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 0' =
 (X_gn_inj :: X_Nat => X_Int) 0''"

ga_monotonicity_2 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 0' = (X_gn_inj :: Rat => Rat) 0_3"

ga_monotonicity_3 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 0'' = (X_gn_inj :: Rat => Rat) 0_3"

ga_monotonicity_4 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 1' =
 (X_gn_inj :: X_Nat => X_Int) 1''"

ga_monotonicity_5 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 1' = (X_gn_inj :: Pos => X_Int) 1_3"

ga_monotonicity_6 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 1' = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_7 [rule_format] :
"(X_gn_inj :: X_Nat => X_Nat) 1'' = (X_gn_inj :: Pos => X_Nat) 1_3"

ga_monotonicity_8 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 1'' = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_9 [rule_format] :
"(X_gn_inj :: Pos => Rat) 1_3 = (X_gn_inj :: Rat => Rat) 1_4"

ga_monotonicity_10 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 2' =
 (X_gn_inj :: X_Nat => X_Int) 2''"

ga_monotonicity_11 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 2' = (X_gn_inj :: Rat => Rat) 2_3"

ga_monotonicity_12 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 2'' = (X_gn_inj :: Rat => Rat) 2_3"

ga_monotonicity_13 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 3' =
 (X_gn_inj :: X_Nat => X_Int) 3''"

ga_monotonicity_14 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 3' = (X_gn_inj :: Rat => Rat) 3_3"

ga_monotonicity_15 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 3'' = (X_gn_inj :: Rat => Rat) 3_3"

ga_monotonicity_16 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 4' =
 (X_gn_inj :: X_Nat => X_Int) 4''"

ga_monotonicity_17 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 4' = (X_gn_inj :: Rat => Rat) 4_3"

ga_monotonicity_18 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 4'' = (X_gn_inj :: Rat => Rat) 4_3"

ga_monotonicity_19 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 5' =
 (X_gn_inj :: X_Nat => X_Int) 5''"

ga_monotonicity_20 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 5' = (X_gn_inj :: Rat => Rat) 5_3"

ga_monotonicity_21 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 5'' = (X_gn_inj :: Rat => Rat) 5_3"

ga_monotonicity_22 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 6' =
 (X_gn_inj :: X_Nat => X_Int) 6''"

ga_monotonicity_23 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 6' = (X_gn_inj :: Rat => Rat) 6_3"

ga_monotonicity_24 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 6'' = (X_gn_inj :: Rat => Rat) 6_3"

ga_monotonicity_25 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 7' =
 (X_gn_inj :: X_Nat => X_Int) 7''"

ga_monotonicity_26 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 7' = (X_gn_inj :: Rat => Rat) 7_3"

ga_monotonicity_27 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 7'' = (X_gn_inj :: Rat => Rat) 7_3"

ga_monotonicity_28 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 8' =
 (X_gn_inj :: X_Nat => X_Int) 8''"

ga_monotonicity_29 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 8' = (X_gn_inj :: Rat => Rat) 8_3"

ga_monotonicity_30 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 8'' = (X_gn_inj :: Rat => Rat) 8_3"

ga_monotonicity_31 [rule_format] :
"(X_gn_inj :: X_Int => X_Int) 9' =
 (X_gn_inj :: X_Nat => X_Int) 9''"

ga_monotonicity_32 [rule_format] :
"(X_gn_inj :: X_Int => Rat) 9' = (X_gn_inj :: Rat => Rat) 9_3"

ga_monotonicity_33 [rule_format] :
"(X_gn_inj :: X_Nat => Rat) 9'' = (X_gn_inj :: Rat => Rat) 9_3"

ga_monotonicity_34 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__Xx__XX2)"

ga_monotonicity_35 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => Pos * Pos => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => X_Int)
 (uncurryOp X__Xx__XX3)"

ga_monotonicity_36 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_37 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__Xx__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_38 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => Pos * Pos => X_Nat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => X_Nat)
 (uncurryOp X__Xx__XX3)"

ga_monotonicity_39 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_40 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__Xx__XX2) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_41 [rule_format] :
"(X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Rat)
 (uncurryOp X__Xx__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => Pos * Pos => Rat)
 (uncurryOp X__Xx__XX4)"

ga_monotonicity_42 [rule_format] :
"(X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__Xx__XX3) =
 (X_gn_inj :: (Pos * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_43 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__Xx__XX4) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__Xx__XX5)"

ga_monotonicity_44 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX2)"

ga_monotonicity_45 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * Pos => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => X_Int)
 (uncurryOp X__XPlus__XX3)"

ga_monotonicity_46 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => Pos * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => X_Int)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_47 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_48 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XPlus__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_49 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * Pos => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => X_Nat)
 (uncurryOp X__XPlus__XX3)"

ga_monotonicity_50 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => Pos * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_51 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_52 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX2) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Nat)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_53 [rule_format] :
"(X_gn_inj :: (X_Nat * Pos => Pos) => Pos * Pos => Pos)
 (uncurryOp X__XPlus__XX3) =
 (X_gn_inj :: (Pos * X_Nat => Pos) => Pos * Pos => Pos)
 (uncurryOp X__XPlus__XX4)"

ga_monotonicity_54 [rule_format] :
"(X_gn_inj :: (X_Nat * Pos => Pos) => X_Nat * Pos => Rat)
 (uncurryOp X__XPlus__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * Pos => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_55 [rule_format] :
"(X_gn_inj :: (Pos * X_Nat => Pos) => Pos * X_Nat => Rat)
 (uncurryOp X__XPlus__XX4) =
 (X_gn_inj :: (Rat * Rat => Rat) => Pos * X_Nat => Rat)
 (uncurryOp X__XPlus__XX5)"

ga_monotonicity_56 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XPlus__XX5) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XPlus__XX6)"

ga_monotonicity_57 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX2)"

ga_monotonicity_58 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X__XMinus__XX3)"

ga_monotonicity_59 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XMinus__XX1) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => X_Int)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_60 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XMinus__XX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X__XMinus__XX3)"

ga_monotonicity_61 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX2) =
 (X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_62 [rule_format] :
"(X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XMinus__XX3) =
 (X_gn_inj :: (Rat * Rat => Rat) => Rat * Rat => Rat)
 (uncurryOp X__XMinus__XX4)"

ga_monotonicity_63 [rule_format] :
"(X_gn_inj :: (X_Int * Pos => Rat) => X_Int * Pos => Rat)
 (uncurryOp X__XSlash__XX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * Pos => Rat)
 (uncurryOp X__XSlash__XX3)"

ga_monotonicity_64 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__XSlashXQuest__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__XSlashXQuest__XX2)"

ga_monotonicity_65 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX2)"

ga_monotonicity_66 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLt__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLt__XX3)"

ga_monotonicity_67 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLt__XX3)"

ga_monotonicity_68 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX2)"

ga_monotonicity_69 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLtXEq__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XLtXEq__XX3)"

ga_monotonicity_70 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XLtXEq__XX3)"

ga_monotonicity_71 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX2)"

ga_monotonicity_72 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGt__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGt__XX3)"

ga_monotonicity_73 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGt__XX3)"

ga_monotonicity_74 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX2)"

ga_monotonicity_75 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGtXEq__XX1) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Int * X_Int => bool)
 (uncurryOp X__XGtXEq__XX3)"

ga_monotonicity_76 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX2) =
 (X_gn_inj :: (Rat * Rat => bool) => X_Nat * X_Nat => bool)
 (uncurryOp X__XGtXEq__XX3)"

ga_monotonicity_77 [rule_format] :
"(X_gn_inj :: (X_Int * X_Nat => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XCaret__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X__XCaret__XX2)"

ga_monotonicity_78 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__div__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Int partial)
 (uncurryOp X__div__XX2)"

ga_monotonicity_79 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Nat partial) => X_Nat * X_Nat => X_Nat partial)
 (uncurryOp X__mod__XX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat partial) => X_Nat * X_Nat => X_Nat partial)
 (uncurryOp X__mod__XX2)"

ga_monotonicity_80 [rule_format] :
"(X_gn_inj :: (X_Int => X_Nat) => X_Int => Rat) X_absX1 =
 (X_gn_inj :: (Rat => Rat) => X_Int => Rat) X_absX2"

ga_monotonicity_81 [rule_format] :
"(X_gn_inj :: (Rat => Rat) => Rat => Rat) X_absX2 =
 (X_gn_inj :: (Rat => Rat) => Rat => Rat) X_absX3"

ga_monotonicity_82 [rule_format] :
"(X_gn_inj :: (X_Int => bool) => X_Nat => bool) X_evenX1 =
 (X_gn_inj :: (X_Nat => bool) => X_Nat => bool) X_evenX2"

ga_monotonicity_83 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_maxX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_maxX2)"

ga_monotonicity_84 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X_maxX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X_maxX3)"

ga_monotonicity_85 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_maxX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_maxX3)"

ga_monotonicity_86 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_minX1) =
 (X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => X_Int)
 (uncurryOp X_minX2)"

ga_monotonicity_87 [rule_format] :
"(X_gn_inj :: (X_Int * X_Int => X_Int) => X_Int * X_Int => Rat)
 (uncurryOp X_minX1) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Int * X_Int => Rat)
 (uncurryOp X_minX3)"

ga_monotonicity_88 [rule_format] :
"(X_gn_inj :: (X_Nat * X_Nat => X_Nat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_minX2) =
 (X_gn_inj :: (Rat * Rat => Rat) => X_Nat * X_Nat => Rat)
 (uncurryOp X_minX3)"

ga_monotonicity_89 [rule_format] :
"(X_gn_inj :: (X_Int => bool) => X_Nat => bool) X_oddX1 =
 (X_gn_inj :: (X_Nat => bool) => X_Nat => bool) X_oddX2"

ga_monotonicity_90 [rule_format] :
"(X_gn_inj :: (X_Nat => X_Nat) => X_Nat => X_Nat) sucX1 =
 (X_gn_inj :: (X_Nat => Pos) => X_Nat => X_Nat) sucX2"

ga_subt_reflexive [rule_format] :
"ALL (x :: 'a). ALL (y :: 'a). gn_subt(x, y)"

ga_subt_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c). gn_subt(x, y) & gn_subt(y, z) --> gn_subt(x, z)"

ga_subt_inj_proj [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 gn_subt(x, y) -->
 y = (X_gn_inj :: 'a => 'b) x =
 (makePartial x = (X_gn_proj :: 'b => 'a partial) y)"

ga_inj_transitive [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'b).
 ALL (z :: 'c).
 gn_subt(x, y) & gn_subt(y, z) & y = (X_gn_inj :: 'a => 'b) x -->
 z = (X_gn_inj :: 'a => 'c) x = (z = (X_gn_inj :: 'b => 'c) y)"

ga_subt_Int_XLt_Rat [rule_format] :
"ALL (x :: X_Int). ALL (y :: Rat). gn_subt(x, y)"

ga_subt_Nat_XLt_Int [rule_format] :
"ALL (x :: X_Nat). ALL (y :: X_Int). gn_subt(x, y)"

ga_subt_Pos_XLt_Nat [rule_format] :
"ALL (x :: Pos). ALL (y :: X_Nat). gn_subt(x, y)"

GenSortT1 [rule_format] :
"ALL (join :: ('a, 'b) Split => 'a List).
 ALL (r :: 'b).
 ALL (X_split :: 'a List => ('a, 'b) Split).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (xxs :: 'a List List).
 ALL (y :: 'a).
 ALL (ys :: 'a List).
 xs = X_Cons x (X_Cons y ys) & X_split xs = X_Split r xxs -->
 genSort X_split join xs =
 join (X_Split r (X_map (genSort X_split join) xxs))"

GenSortT2 [rule_format] :
"ALL (join :: ('a, 'b) Split => 'a List).
 ALL (r :: 'b).
 ALL (X_split :: 'a List => ('a, 'b) Split).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (xxs :: 'a List List).
 ALL (y :: 'a).
 xs = X_Cons x (X_Cons y Nil') & X_split xs = X_Split r xxs -->
 genSort X_split join xs =
 join (X_Split r (X_map (genSort X_split join) xxs))"

GenSortF [rule_format] :
"ALL (join :: ('a, 'b) Split => 'a List).
 ALL (X_split :: 'a List => ('a, 'b) Split).
 ALL (x :: 'a).
 ALL (xs :: 'a List).
 xs = X_Cons x Nil' | xs = Nil' --> genSort X_split join xs = xs"

SplitInsertionSort [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 splitInsertionSort(X_Cons x xs) = X_Split x (X_Cons xs Nil')"

JoinInsertionSort [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 joinInsertionSort(X_Split x (X_Cons xs Nil')) = X_insert x xs"

InsertionSort [rule_format] :
"ALL (xs :: 'a List).
 insertionSort(xs) =
 genSort X_splitInsertionSort X_joinInsertionSort xs"

SplitQuickSort [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 splitQuickSort(X_Cons x xs) =
 (let (ys, zs) = partition (% t. x <_4 t) xs
  in X_Split x (X_Cons ys (X_Cons zs Nil')))"

JoinQuickSort [rule_format] :
"ALL (x :: 'a).
 ALL (ys :: 'a List).
 ALL (zs :: 'a List).
 joinQuickSort(X_Split x (X_Cons ys (X_Cons zs Nil'))) =
 ys ++' X_Cons x zs"

QuickSort [rule_format] :
"ALL (xs :: 'a List).
 quickSort(xs) = genSort X_splitQuickSort X_joinQuickSort xs"

SplitSelectionSort [rule_format] :
"ALL (xs :: 'a List).
 makePartial (splitSelectionSort(xs)) =
 restrictOp
 (makePartial
  (let x = minimum(xs)
   in X_Split (makeTotal x) (X_Cons (delete (makeTotal x) xs) Nil')))
 (defOp x)"

JoinSelectionSort [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 joinSelectionSort(X_Split x (X_Cons xs Nil')) = X_Cons x xs"

SelectionSort [rule_format] :
"ALL (xs :: 'a List).
 selectionSort(xs) =
 genSort X_splitSelectionSort X_joinSelectionSort xs"

SplitMergeSort [rule_format] :
"ALL (X_n :: X_Nat).
 ALL (xs :: 'a List).
 defOp (length'(xs) div' (X_gn_inj :: X_Nat => X_Int) 2'') &
 makePartial ((X_gn_inj :: X_Nat => X_Int) X_n) =
 length'(xs) div' (X_gn_inj :: X_Nat => X_Int) 2'' -->
 splitMergeSort(xs) =
 (let (ys, zs) = splitAt ((X_gn_inj :: X_Nat => X_Int) X_n) xs
  in X_Split () (X_Cons ys (X_Cons zs Nil')))"

MergeNil [rule_format] :
"ALL (xs :: 'a List).
 ALL (ys :: 'a List). xs = Nil' --> merge xs ys = ys"

MergeConsNil [rule_format] :
"ALL (v :: 'a).
 ALL (vs :: 'a List).
 ALL (xs :: 'a List).
 ALL (ys :: 'a List).
 xs = X_Cons v vs & ys = Nil' --> merge xs ys = xs"

MergeConsConsT [rule_format] :
"ALL (v :: 'a).
 ALL (vs :: 'a List).
 ALL (w :: 'a).
 ALL (ws :: 'a List).
 ALL (xs :: 'a List).
 ALL (ys :: 'a List).
 (xs = X_Cons v vs & ys = X_Cons w ws) & v <_4 w = True' -->
 merge xs ys = X_Cons v (merge vs ys)"

MergeConsConsF [rule_format] :
"ALL (v :: 'a).
 ALL (vs :: 'a List).
 ALL (w :: 'a).
 ALL (ws :: 'a List).
 ALL (xs :: 'a List).
 ALL (ys :: 'a List).
 (xs = X_Cons v vs & ys = X_Cons w ws) & v <_4 w = False' -->
 merge xs ys = X_Cons w (merge xs ws)"

JoinMergeSort [rule_format] :
"ALL (ys :: 'a List).
 ALL (zs :: 'a List).
 joinMergeSort(X_Split () (X_Cons ys (X_Cons zs Nil'))) =
 merge ys zs"

MergeSort [rule_format] :
"ALL (xs :: 'a List).
 mergeSort(xs) = genSort X_splitMergeSort X_joinMergeSort xs"

ElemNil [rule_format] : "ALL (x :: 'a). ~ x elem Nil'"

ElemCons [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (ys :: 'a List). (x elem X_Cons y ys) = (x = y | x elem ys)"

IsOrderedNil [rule_format] : "isOrdered(Nil')"

IsOrderedCons [rule_format] :
"ALL (x :: 'a). isOrdered(X_Cons x Nil')"

IsOrderedConsCons [rule_format] :
"ALL (x :: 'a).
 ALL (y :: 'a).
 ALL (ys :: 'a List).
 isOrdered(X_Cons x (X_Cons y ys)) =
 (x <=_4 y = True' & isOrdered(X_Cons y ys))"

PermutationNil [rule_format] : "permutation(Nil', Nil')"

PermutationConsCons [rule_format] :
"ALL (x :: 'a).
 ALL (xs :: 'a List).
 ALL (y :: 'a).
 ALL (ys :: 'a List).
 permutation(X_Cons x xs, X_Cons y ys) =
 (x = y & permutation(xs, ys) |
  x elem ys & permutation(xs, X_Cons y (delete x ys)))"

declare ga_subt_reflexive [simp]
declare ga_subt_Int_XLt_Rat [simp]
declare ga_subt_Nat_XLt_Int [simp]
declare ga_subt_Pos_XLt_Nat [simp]
declare JoinInsertionSort [simp]
declare JoinQuickSort [simp]
declare JoinSelectionSort [simp]
declare JoinMergeSort [simp]
declare ElemNil [simp]
declare IsOrderedNil [simp]
declare IsOrderedCons [simp]
declare PermutationNil [simp]

theorem PermutationCons :
"ALL (x :: 'a).
 ALL (y :: 'a). permutation(X_Cons x Nil', X_Cons y Nil') = (x = y)"
apply(auto)
apply(simp add: PermutationConsCons)+
done

setup "Header.record \"PermutationCons\""

theorem Theorem01 :
"ALL (xs :: 'a List). insertionSort(xs) = quickSort(xs)"
apply(auto)
oops

setup "Header.record \"Theorem01\""

theorem Theorem02 :
"ALL (xs :: 'a List). insertionSort(xs) = mergeSort(xs)"
oops

setup "Header.record \"Theorem02\""

theorem Theorem03 :
"ALL (xs :: 'a List). insertionSort(xs) = selectionSort(xs)"
oops

setup "Header.record \"Theorem03\""

theorem Theorem04 :
"ALL (xs :: 'a List). quickSort(xs) = mergeSort(xs)"
oops

setup "Header.record \"Theorem04\""

theorem Theorem05 :
"ALL (xs :: 'a List). quickSort(xs) = selectionSort(xs)"
oops

setup "Header.record \"Theorem05\""

theorem Theorem06 :
"ALL (xs :: 'a List). mergeSort(xs) = selectionSort(xs)"
oops

setup "Header.record \"Theorem06\""

theorem Theorem07 :
"ALL (xs :: 'a List). isOrdered(insertionSort(xs))"
oops

setup "Header.record \"Theorem07\""

theorem Theorem08 : "ALL (xs :: 'a List). isOrdered(quickSort(xs))"
oops

setup "Header.record \"Theorem08\""

theorem Theorem09 : "ALL (xs :: 'a List). isOrdered(mergeSort(xs))"
oops

setup "Header.record \"Theorem09\""

theorem Theorem10 :
"ALL (xs :: 'a List). isOrdered(selectionSort(xs))"
oops

setup "Header.record \"Theorem10\""

theorem Theorem11 :
"ALL (xs :: 'a List). permutation(xs, insertionSort(xs))"
oops

setup "Header.record \"Theorem11\""

theorem Theorem12 :
"ALL (xs :: 'a List). permutation(xs, quickSort(xs))"
oops

setup "Header.record \"Theorem12\""

theorem Theorem13 :
"ALL (xs :: 'a List). permutation(xs, mergeSort(xs))"
oops

setup "Header.record \"Theorem13\""

theorem Theorem14 :
"ALL (xs :: 'a List). permutation(xs, selectionSort(xs))"
oops

setup "Header.record \"Theorem14\""

end
