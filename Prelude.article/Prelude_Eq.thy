theory Prelude_Eq
imports "$HETS_LIB/Isabelle/MainHCPairs"
uses "$HETS_LIB/Isabelle/prelude"
begin

ML "Header.initialize
    [\"NotFalse\", \"NotTrue\", \"AndFalse\", \"AndTrue\", \"AndSym\",
     \"OrDef\", \"OtherwiseDef\", \"NotFalse1\", \"NotTrue1\",
     \"notNot1\", \"notNot2\", \"EqualTDef\", \"EqualSymDef\",
     \"EqualReflex\", \"EqualTransT\", \"DiffDef\", \"EqualPrefixDef\",
     \"DiffPrefixDef\", \"IBE3\", \"DiffSymDef\", \"DiffTDef\",
     \"DiffFDef\", \"TE1\", \"TE2\", \"TE3\", \"TE4\", \"IBE1\",
     \"IBE2\", \"IBE4\", \"IBE5\", \"IBE6\", \"IBE7\", \"IBE8\",
     \"IUE1\", \"IUE2\"]"

typedecl Unit

datatype Bool = X_False ("False''") | X_True ("True''")

consts
Not__X :: "Bool => Bool" ("(Not''/ _)" [56] 56)
XLtXEqXEqXGt :: "'a => 'a => Bool"
XLtXSlashXEqXGt :: "'a => 'a => Bool"
X__XAmpXAmp__X :: "Bool => Bool => Bool" ("(_/ &&/ _)" [54,54] 52)
X__XEqXEq__X :: "'a => 'a => Bool" ("(_/ ==''/ _)" [54,54] 52)
X__XSlashXEq__X :: "'a => 'a => Bool" ("(_/ '/=/ _)" [54,54] 52)
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

EqualPrefixDef [rule_format] :
"ALL x. ALL y. XLtXEqXEqXGt x y = x ==' y"

DiffPrefixDef [rule_format] :
"ALL x. ALL y. XLtXSlashXEqXGt x y = x /= y"

IBE3 [rule_format] : "False' ==' True' = False'"

declare NotFalse [simp]
declare NotTrue [simp]
declare AndFalse [simp]
declare AndTrue [simp]
declare EqualReflex [simp]
declare IBE3 [simp]

theorem DiffSymDef : "ALL x. ALL y. x /= y = y /= x"
apply(auto)
apply(simp add: DiffDef)
apply(simp add: EqualSymDef)
done

ML "Header.record \"DiffSymDef\""

theorem DiffTDef :
"ALL x. ALL y. x /= y = True' = (Not' (x ==' y) = True')"
apply(auto)
apply(simp add: DiffDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: DiffDef)
done

ML "Header.record \"DiffTDef\""

theorem DiffFDef :
"ALL x. ALL y. x /= y = False' = (x ==' y = True')"
apply(auto)
apply(simp add: DiffDef)
apply(case_tac "x ==' y")
apply(auto)
apply(simp add: DiffDef)
done

ML "Header.record \"DiffFDef\""

theorem TE1 : "ALL x. ALL y. x ==' y = False' --> ~ x = y"
by (auto)

ML "Header.record \"TE1\""

theorem TE2 :
"ALL x. ALL y. Not' (x ==' y) = True' = (x ==' y = False')"
apply auto
apply(case_tac "x ==' y")
apply auto
done

ML "Header.record \"TE2\""

theorem TE3 :
"ALL x. ALL y. Not' (x ==' y) = False' = (x ==' y = True')"
apply(auto)
apply(case_tac "x ==' y")
apply auto
done

ML "Header.record \"TE3\""

theorem TE4 :
"ALL x. ALL y. (~ x ==' y = True') = (x ==' y = False')"
apply auto
apply(case_tac "x ==' y")
apply auto
done


ML "Header.record \"TE4\""

theorem IBE1 : "True' ==' True' = True'"
by (auto)

ML "Header.record \"IBE1\""

theorem IBE2 : "False' ==' False' = True'"
by (auto)

ML "Header.record \"IBE2\""

theorem IBE4 : "True' ==' False' = False'"
apply(simp add: EqualSymDef)
done

ML "Header.record \"IBE4\""

theorem IBE5 : "True' /= False' = True'"
apply(simp add: DiffDef)
apply(simp add: IBE4)
done

ML "Header.record \"IBE5\""

theorem IBE6 : "False' /= True' = True'"
apply(simp add: DiffDef)
done

ML "Header.record \"IBE6\""

theorem IBE7 : "Not' (True' ==' False') = True'"
apply(simp add: IBE4)
done

ML "Header.record \"IBE7\""

theorem IBE8 : "Not' Not' (True' ==' False') = False'"
apply(simp add: IBE4)
done

ML "Header.record \"IBE8\""

theorem IUE1 : "() ==' () = True'"
by (auto)

ML "Header.record \"IUE1\""

theorem IUE2 : "() /= () = False'"
apply(simp add: DiffDef)
done

ML "Header.record \"IUE2\""

end
