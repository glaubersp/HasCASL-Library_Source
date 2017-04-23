theory Prelude_Bool_1
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize [\"Ax4\", \"Not_False\", \"Not_True\"]"

typedecl Bool

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
X_False :: "Bool" ("False''")
X_True :: "Bool" ("True''")

instance Bool:: type ..

axioms
Not_False [rule_format] : "Not' False' = True'"

Not_True [rule_format] : "Not' True' = False'"

declare Not_False [simp]
declare Not_True [simp]

theorem Ax4 : "~ True' = False'"
by auto

ML "Header.record \"Ax4\""

end
