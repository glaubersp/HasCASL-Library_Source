theory Prelude_Eq
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
        \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
        \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
        \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"IBE3\",
        \"DiffSymDef\", \"DiffTDef\", \"DiffFDef\", \"TE1\", \"TE2\",
        \"TE3\", \"TE4\", \"IBE1\", \"IBE2\", \"IBE4\", \"IBE5\", \"IBE6\",
        \"IBE7\", \"IBE8\", \"IUE1\", \"IUE2\"]"

typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")

consts
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
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

IBE3 [rule_format] : "False' ==' True' = False'"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare EqualReflex [simp]
declare IBE3 [simp]

theorem DiffSymDef :
"ALL (x :: 'a). ALL (y :: 'a). x /= y = y /= x"
apply(auto)
apply(simp add: DiffDef)
apply(simp add: EqualSymDef)
done

setup "Header.record \"DiffSymDef\""

theorem DiffTDef :
"ALL (x :: 'a).
 ALL (y :: 'a). x /= y = True' = (notH (x ==' y) = True')"
apply(auto)
apply(simp add: DiffDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: DiffDef)
done

setup "Header.record \"DiffTDef\""

theorem DiffFDef :
"ALL (x :: 'a). ALL (y :: 'a). x /= y = False' = (x ==' y = True')"
apply(auto)
apply(simp add: DiffDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: DiffDef)
done

setup "Header.record \"DiffFDef\""

theorem TE1 :
"ALL (x :: 'a). ALL (y :: 'a). x ==' y = False' --> ~ x = y"
by (auto)

setup "Header.record \"TE1\""

theorem TE2 :
"ALL (x :: 'a).
 ALL (y :: 'a). notH (x ==' y) = True' = (x ==' y = False')"
apply auto
apply(case_tac "x ==' y")
apply auto
done

setup "Header.record \"TE2\""

theorem TE3 :
"ALL (x :: 'a).
 ALL (y :: 'a). notH (x ==' y) = False' = (x ==' y = True')"
apply auto
apply(case_tac "x ==' y")
apply auto
done

setup "Header.record \"TE3\""

theorem TE4 :
"ALL (x :: 'a).
 ALL (y :: 'a). (~ x ==' y = True') = (x ==' y = False')"
apply auto
apply(case_tac "x ==' y")
apply auto
done

setup "Header.record \"TE4\""

theorem IBE1 : "True' ==' True' = True'"
by (auto)

setup "Header.record \"IBE1\""

theorem IBE2 : "False' ==' False' = True'"
by (auto)

setup "Header.record \"IBE2\""

theorem IBE4 : "True' ==' False' = False'"
apply(simp add: EqualSymDef)
done

setup "Header.record \"IBE4\""

theorem IBE5 : "True' /= False' = True'"
apply(simp add: DiffDef)
apply(simp add: IBE4)
done

setup "Header.record \"IBE5\""

theorem IBE6 : "False' /= True' = True'"
apply(simp add: DiffDef)
done

setup "Header.record \"IBE6\""

theorem IBE7 : "notH (True' ==' False') = True'"
apply(simp add: IBE4)
done

setup "Header.record \"IBE7\""

theorem IBE8 : "notH notH (True' ==' False') = False'"
apply(simp add: IBE4)
done

setup "Header.record \"IBE8\""

theorem IUE1 : "() ==' () = True'"
by (auto)

setup "Header.record \"IUE1\""

theorem IUE2 : "() /= () = False'"
apply(simp add: DiffDef)
done

setup "Header.record \"IUE2\""

end
