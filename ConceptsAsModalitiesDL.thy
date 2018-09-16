theory ConceptsAsModalitiesDL
  imports Main
begin
typedecl i (* type for individuals *)
typedecl v (* type for views *)
consts "vn" :: "v" (* normal view *)
type_synonym concept = "i\<times>v\<times>v\<Rightarrow>bool"
type_synonym relation = "i\<times>i\<Rightarrow>bool"

abbreviation dldisj :: "concept\<Rightarrow>concept\<Rightarrow>concept" (infixr"\<squnion>"50)
  where "C\<squnion>D \<equiv> \<lambda>(x,v1,v2). C(x,v1,v2)\<or>D(x,v1,v2)"
abbreviation dlnot :: "concept\<Rightarrow>concept" ("\<^bold>\<not>_"[53]53)
  where "\<^bold>\<not>C  \<equiv> \<lambda>(x,v1,v2). v1=v2 \<and> \<not>(\<exists>v3. C(x,v1,v3))"
abbreviation dlconj :: "concept\<Rightarrow>concept\<Rightarrow>concept" (infixr"\<sqinter>"51)
  where "C\<sqinter>D \<equiv> \<lambda>(x,v1,v2). (\<exists>v3. C(x,v1,v3))\<and>(\<exists>v4. D(x,v1,v4))\<and>(C\<squnion>D)(x,v1,v2)"
abbreviation dlexists :: "relation\<Rightarrow>concept\<Rightarrow>concept" ("\<^bold>\<exists>_._"[8]9)
  where "\<^bold>\<exists>R. C \<equiv> \<lambda>(x,v1,v2). \<exists>y. R(x,y) \<and> C(y,v1,v2)"
abbreviation dlforall :: "relation\<Rightarrow>concept\<Rightarrow>concept" ("\<^bold>\<forall>_._"[8]9)
  where "\<^bold>\<forall>R. C \<equiv> \<lambda>(x,v1,v2). \<forall>y. R(x,y)\<longrightarrow>C(y,v1,v2)"

abbreviation dlgen :: "concept\<Rightarrow>concept\<Rightarrow>concept" (infixr"\<midarrow>\<circ>"52)
  where "C \<midarrow>\<circ> D \<equiv> \<lambda>(x,v1,v2). \<exists>v3. C(x,v1,v3) \<and> D(x,v3,v2)"

abbreviation dltop :: "concept" ("\<top>")
  where "\<top> \<equiv> \<lambda>(x,v1,v2). v1=v2"
abbreviation dlbot :: "concept" ("\<bottom>")
  where "\<bottom> \<equiv> \<lambda>(x,v1,v2). False"

abbreviation subsums :: "concept\<Rightarrow>concept\<Rightarrow>bool" (infixr"\<sqsubseteq>"48)
  where "C\<sqsubseteq>D \<equiv> \<forall>v1. \<forall>x. (\<exists>v2. C(x,v1,v2))\<longrightarrow>(\<exists>v3. D(x,v1,v3))"
abbreviation equi :: "concept\<Rightarrow>concept\<Rightarrow>bool" (infixr"\<^bold>\<equiv>"48)
  where "C\<^bold>\<equiv>D \<equiv> (C\<sqsubseteq>D) \<and> (D\<sqsubseteq>C)"

abbreviation dlass :: "i \<Rightarrow> concept \<Rightarrow> bool" (infixr"\<^bold>:"52)
  where "a\<^bold>:C \<equiv> \<exists>v2. C(a,vn,v2)"

axiomatization where
 ConceptAx: "\<And>C D x y v1 v2 v3. (C::concept)(x,v1,v2) \<and> (D::concept)(y,v3,v2) 
                                        \<longrightarrow> C(y,v1,v2)" 
(*  ConceptRelAx: "\<And>C v1 v2. (\<exists>x. C(x,v1,v2)) \<longrightarrow> q(C,v1,v2)" and
  InViewAx: "\<And>v x. (\<exists>C. \<exists>v1. C(x,v1,v)) \<longrightarrow> e(v,x)" and
  ConceptTrippleAx: "\<And>C v1 v2 x. q(C,v1,v2) \<and> e(v2,x) \<longrightarrow> C(x,v1,v2)" *)

theorem "x \<^bold>: \<top>"
  by blast

theorem "\<bottom> \<^bold>\<equiv> \<^bold>\<not>\<top>"
  by blast

(* timed out:
theorem False sledgehammer *)
(* nitpick: empty assignment *)
(* theorem True nitpick[satisfy,user_axioms=true] *)

end