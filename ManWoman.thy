theory ManWoman
  imports ConceptsAsModalitiesDL
begin

consts Woman :: concept
consts Man   :: concept
consts Person:: concept
consts Female:: concept

axiomatization where
A1: "Woman \<^bold>\<equiv> Person \<sqinter> Female"  and
A2: "Man   \<^bold>\<equiv> Person \<sqinter>\<^bold>\<not>Female"

theorem "Female \<midarrow>\<circ> \<^bold>\<not>Female \<sqsubseteq> Female"
  by blast

theorem "Female \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<not>Female"
  by blast

theorem "\<top> \<sqsubseteq> Female\<squnion>\<^bold>\<not>Female"
  by blast

theorem "Person \<^bold>\<equiv> Woman \<squnion> Man"
proof -
  {
    fix x
    fix v1
    assume 1:"\<exists>v. Person(x,v1,v)"
    {
      assume 2:"\<exists>v. Female(x,v1,v)"
      from 1 2 have "\<exists>v. Woman(x,v1,v)" using A1 by blast
      hence "\<exists>v. (Woman\<squnion>Man)(x,v1,v)" by blast
    } moreover {
      assume "\<not>(\<exists>v. Female(x,v1,v))"
      hence 3:"\<exists>v. (\<^bold>\<not>Female)(x,v1,v)" by blast
      from 1 3 have "\<exists>v. Man(x,v1,v)" using A2 by blast
      hence "\<exists>v. (Woman\<squnion>Man)(x,v1,v)" by blast
    }
    ultimately have "\<exists>v. (Woman\<squnion>Man)(x,v1,v)" by blast
  }
  hence  "Person \<sqsubseteq> Woman \<squnion> Man" by blast
  moreover have "Woman \<squnion> Man \<sqsubseteq> Person" using A1 A2 by blast
  ultimately show "Person \<^bold>\<equiv> Woman \<squnion> Man" by blast
qed

theorem "\<bottom> \<^bold>\<equiv> Man \<sqinter> Female"
  using A1 A2 by blast

end