theory Prelude_Composition
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize [\"Comp\", \"Comp1\"]"

consts
X__o__X :: "('b => 'c) * ('a => 'b) => 'a => 'c"

axioms
Comp [rule_format] :
"ALL f.
 ALL g. makePartial o X__o__X (f, g) = makePartial o (% x. f (g x))"

theorem Comp1 : "ALL f. ALL g. ALL y. X__o__X (f, g) y = f (g y)"
apply(auto)
thm Comp
apply(rule Comp)
by auto

ML "Header.record \"Comp1\""

end
