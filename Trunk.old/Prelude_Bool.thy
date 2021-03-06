theory Prelude_Bool
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
     \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
     \"notNot1\", \"notNot2\"]"

datatype Bool = X_False ("False''") | X_True ("True''")

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
otherwiseH :: "Bool"

axioms
NotFalse [rule_format] : "Not' False' = True'"

NotTrue [rule_format] : "Not' True' = False'"

AndFalse [rule_format] : "ALL x. False' && x = False'"

AndTrue [rule_format] : "ALL x. True' && x = x"

AndSym [rule_format] : "ALL x. ALL y. x && y = y && x"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]

theorem NotFalse1 : "ALL x. Not' x = True' = (x = False')"
apply auto
apply(case_tac x)
apply auto
done

ML "Header.record \"NotFalse1\""

theorem NotTrue1 : "ALL x. Not' x = False' = (x = True')"
apply auto
apply(case_tac x)
apply auto
done

ML "Header.record \"NotTrue1\""

theorem notNot1 : "ALL x. (~ x = True') = (Not' x = True')"
apply(auto)
apply(case_tac x)
apply(auto)
done

ML "Header.record \"notNot1\""

theorem notNot2 : "ALL x. (~ x = False') = (Not' x = False')"
apply(auto)
apply(case_tac x)
apply(auto)
done

ML "Header.record \"notNot2\""

end
