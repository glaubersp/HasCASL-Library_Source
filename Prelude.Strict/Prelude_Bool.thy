theory Prelude_Bool
imports "$HETS_ISABELLE_LIB/MainHC"
uses "$HETS_ISABELLE_LIB/prelude"
begin

setup "Header.initialize
       [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
        \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
        \"notNot1\", \"notNot2\"]"

datatype Bool = X_False ("False''") | X_True ("True''")

consts
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
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

declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]

theorem NotFalse1 :
"ALL (x :: Bool). notH x = True' = (x = False')"
apply auto
apply(case_tac x)
apply auto
done

setup "Header.record \"NotFalse1\""

theorem NotTrue1 : "ALL (x :: Bool). notH x = False' = (x = True')"
apply auto
apply(case_tac x)
apply auto
done

setup "Header.record \"NotTrue1\""

theorem notNot1 :
"ALL (x :: Bool). (~ x = True') = (notH x = True')"
apply auto
apply(case_tac x)
apply auto
done

setup "Header.record \"notNot1\""

theorem notNot2 :
"ALL (x :: Bool). (~ x = False') = (notH x = False')"
apply auto
apply(case_tac x)
apply auto
done

setup "Header.record \"notNot2\""

end
