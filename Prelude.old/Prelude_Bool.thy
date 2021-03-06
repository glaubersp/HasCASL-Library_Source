theory Prelude_Bool
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"NotTrue1\", \"NotFalse2\", \"TB1\", \"NotFalse\", \"NotTrue\",
     \"AndDef1\", \"AndDef2\", \"AndDef3\", \"AndDef4\", \"OrDef\",
     \"OtherwiseDef\"]"

datatype Bool = X_False ("False''") | X_True ("True''")

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XVBarXVBar__X :: "Bool => Bool => Bool" ("(_/ ||/ _)" [54,54] 52)
otherwiseH :: "Bool"

instance Bool:: type ..

axioms
NotFalse [rule_format] : "Not' False' = True'"

NotTrue [rule_format] : "Not' True' = False'"

AndDef1 [rule_format] : "False' && False' = False'"

AndDef2 [rule_format] : "False' && True' = False'"

AndDef3 [rule_format] : "True' && False' = False'"

AndDef4 [rule_format] : "True' && True' = True'"

OrDef [rule_format] :
"ALL x. ALL y. x || y = Not' (Not' x && Not' y)"

OtherwiseDef [rule_format] : "otherwiseH = True'"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndDef1 [simp]
declare AndDef2 [simp]
declare AndDef3 [simp]
declare AndDef4 [simp]

theorem NotTrue1 : "ALL x. Not' x = True' = (x = False')"
apply auto
apply(case_tac x)
apply auto
done

ML "Header.record \"NotTrue1\""

theorem NotFalse2 : "ALL x. Not' x = False' = (x = True')"
apply auto
apply(case_tac x)
apply auto
done

ML "Header.record \"NotFalse2\""

theorem TB1 : "~ True' = False'"
by auto

ML "Header.record \"TB1\""

end
