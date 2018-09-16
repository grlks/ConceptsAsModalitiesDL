theory ALC
  imports Main
begin
typedecl i (* type for individuals *)
type_synonym \<sigma> = "i\<Rightarrow>bool" (* type for concepts *)
type_synonym r = "i\<times>i\<Rightarrow>bool" (* type for relations*)

abbreviation dlconj :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<sqinter>"51)
  where "C\<sqinter>D \<equiv> \<lambda>x. C(x)\<and>D(x)"
abbreviation dldisj :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<squnion>"50)
  where "C\<squnion>D \<equiv> \<lambda>x. C(x)\<or>D(x)"
abbreviation dlnot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_")
  where "\<^bold>\<not>C \<equiv> \<lambda>x. \<not>C(x)"
abbreviation dlexists :: "r\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<exists>_._"[8]9)
  where "\<^bold>\<exists>R. C\<equiv> \<lambda>x. \<exists>y. R(x,y) \<and> C(y)"
abbreviation dlforall :: "r\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<forall>_._"[8]9)
  where "\<^bold>\<forall>R. C\<equiv> \<lambda>x. \<forall>y. R(x,y)\<longrightarrow>C(y)"
abbreviation subsums :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr"\<sqsubseteq>"48)
  where "C\<sqsubseteq>D \<equiv> \<forall>x. C(x)\<longrightarrow>D(x)"
abbreviation equi :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr"\<^bold>\<equiv>"48)
  where "C\<^bold>\<equiv>D \<equiv> C\<sqsubseteq>D \<and> D \<sqsubseteq> C"

abbreviation dltop :: "\<sigma>" ("\<top>")
  where "\<top> \<equiv> \<lambda>x. True"
abbreviation dlbot :: "\<sigma>" ("\<bottom>")
  where "\<bottom> \<equiv> \<lambda>x. False"

consts Woman :: \<sigma>
consts Man   :: \<sigma>
consts Person:: \<sigma>
consts Female:: \<sigma>


axiomatization where
A1: "Woman \<^bold>\<equiv> Person \<sqinter> Female"  and
A2: "Man   \<^bold>\<equiv> Person \<sqinter> \<^bold>\<not>Female"

theorem "Man \<squnion> Woman \<^bold>\<equiv> Person"
  using A1 A2 by blast

theorem "\<bottom> \<^bold>\<equiv> Man \<sqinter> Female"
  using A1 A2 by blast
end