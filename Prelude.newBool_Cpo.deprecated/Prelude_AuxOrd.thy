theory Prelude_AuxOrd
imports "$HETS_LIB/Isabelle/MainHC"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"ALeAsymmetry\", \"ALeIrreflexivity\", \"ALeTransitive\",
     \"ALeTotal\"]"

consts
X__le__X :: "'a => 'a => bool" ("(_/ le/ _)" [44,44] 42)

axioms
ALeIrreflexivity [rule_format] : "ALL x. ~ x le x"

ALeTransitive [rule_format] :
"ALL x. ALL y. ALL z. x le y & y le z --> x le z"

ALeTotal [rule_format] : "ALL x. ALL y. (x le y | y le x) | x = y"

declare ALeIrreflexivity [simp]

theorem ALeAsymmetry : "ALL x. ALL y. x le y --> ~ y le x"
apply(auto)
apply(simp add: ALeIrreflexivity ALeTransitive)

ML "Header.record \"ALeAsymmetry\""

end
