theory VeggiBurger
  imports ConceptsAsModalitiesDL
begin

consts burger :: concept
consts meat   :: concept
consts bread  :: concept
consts veggi  :: concept
consts Ingredient :: relation
consts a :: i

axiomatization where
T1: "burger \<sqsubseteq> (\<^bold>\<exists>Ingredient. meat)" and
T2: "burger \<sqsubseteq> (\<^bold>\<exists>Ingredient. bread)" and
T3: "veggi  \<sqsubseteq> (\<^bold>\<forall>Ingredient. veggi)" and
T4: "\<bottom>     \<equiv>  veggi \<sqinter> meat" and
T5: "veggi \<midarrow>\<circ> bread \<sqsubseteq> bread" and
A1: "a \<^bold>: veggi \<midarrow>\<circ> burger"

theorem "a \<^bold>: (\<^bold>\<exists>Ingredient. veggi \<midarrow>\<circ> meat)"
proof -
  from A1 have "a \<^bold>: veggi \<midarrow>\<circ> burger" by -
  hence "\<exists>v2. (veggi \<midarrow>\<circ> burger)(a,vn,v2)" by -
  hence "\<exists>v2. \<exists>v1. veggi(a,vn,v1) \<and> burger(a,v1,v2)" by simp
  hence "\<exists>v2. \<exists>v1. veggi(a,vn,v1) \<and> (\<^bold>\<exists>Ingredient. meat)(a,v1,v2)"
    using T1 by blast
  hence "\<exists>v2. \<exists>v1. veggi(a,vn,v1) \<and> (\<exists>y. Ingredient(a,y) \<and> meat(y,v1,v2))"
    by simp
  hence "\<exists>y. Ingredient(a,y) \<and> (\<exists>v1. veggi(a,vn,v1) \<and> (\<exists>v2. meat(y,v1,v2)))"
    by auto
  moreover have "\<forall>y. (\<exists>v. veggi(a,vn,v)) \<and> Ingredient(a,y) \<longrightarrow> (\<exists>v. veggi(y,vn,v))" 
    using T3 by blast
  ultimately have "\<exists>y. Ingredient(a,y) \<and> (\<exists>v1. veggi(y,vn,v1) \<and> (\<exists>v2. meat(y,v1,v2)))"
    using ConceptAx by blast
  hence "\<exists>y. Ingredient(a,y) \<and> (\<exists>v2. (veggi\<midarrow>\<circ>meat)(y,vn,v2))" by blast
  hence "\<exists>v2. (\<^bold>\<exists>Ingredient. veggi \<midarrow>\<circ> meat)(a,vn,v2)" by blast
  then show "a \<^bold>: (\<^bold>\<exists>Ingredient. veggi \<midarrow>\<circ> meat)" by -
qed

end