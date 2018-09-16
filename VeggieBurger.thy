theory VeggieBurger
  imports ConceptsAsModalitiesDL
begin

consts burger :: concept
consts meat   :: concept
consts bread  :: concept
consts veggie  :: concept
consts Ingredient :: relation
consts a :: i

axiomatization where
  (* TBox *)
  T1: "burger \<sqsubseteq> (\<^bold>\<exists>Ingredient. meat)" and
  T2: "burger \<sqsubseteq> (\<^bold>\<exists>Ingredient. bread)" and
  T3: "veggie \<sqsubseteq> (\<^bold>\<forall>Ingredient. veggie)" and
  T4: "\<bottom>     \<equiv>  veggie \<sqinter> meat" and
  T5: "veggie \<midarrow>\<circ> bread \<sqsubseteq> bread" and
  (* ABox *)
  A1: "a \<^bold>: veggie \<midarrow>\<circ> burger"

theorem "a \<^bold>: (\<^bold>\<exists>Ingredient. veggie \<midarrow>\<circ> meat)"
proof -
  from A1 have "a \<^bold>: veggie \<midarrow>\<circ> burger" by -
  hence "\<exists>v2. (veggie \<midarrow>\<circ> burger)(a,vn,v2)" by -
  hence "\<exists>v2. \<exists>v1. veggie(a,vn,v1) \<and> burger(a,v1,v2)" by simp
  hence "\<exists>v2. \<exists>v1. veggie(a,vn,v1) \<and> (\<^bold>\<exists>Ingredient. meat)(a,v1,v2)"
    using T1 by blast
  hence "\<exists>v2. \<exists>v1. veggie(a,vn,v1) \<and> (\<exists>y. Ingredient(a,y) \<and> meat(y,v1,v2))"
    by simp
  hence "\<exists>y. Ingredient(a,y) \<and> (\<exists>v1. veggie(a,vn,v1) \<and> (\<exists>v2. meat(y,v1,v2)))"
    by auto
  moreover have "\<forall>y. (\<exists>v. veggie(a,vn,v)) \<and> Ingredient(a,y) \<longrightarrow> (\<exists>v. veggie(y,vn,v))" 
    using T3 by blast
  ultimately have "\<exists>y. Ingredient(a,y) \<and> (\<exists>v1. veggie(y,vn,v1) \<and> (\<exists>v2. meat(y,v1,v2)))"
    using ConceptAx by blast
  hence "\<exists>y. Ingredient(a,y) \<and> (\<exists>v2. (veggie\<midarrow>\<circ>meat)(y,vn,v2))" by blast
  hence "\<exists>v2. (\<^bold>\<exists>Ingredient. veggie \<midarrow>\<circ> meat)(a,vn,v2)" by blast
  then show "a \<^bold>: (\<^bold>\<exists>Ingredient. veggie \<midarrow>\<circ> meat)" by -
qed

end
