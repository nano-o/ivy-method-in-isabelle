theory PBFT
  imports Main "HOL-Eisbach.Eisbach"
begin                                 
  
method rewrite_funs = (simp (no_asm_use) only: fun_upd_apply[abs_def] fun_eq_iff if_split_asm)
  \<comment> \<open>rewrites function-update and function equality terms to first-order equality.\<close>

section "First-Order Abstraction"

locale byz_quorums =
  fixes byz_member :: "'n \<Rightarrow> 'q1 \<Rightarrow> bool" (infix "\<in>\<^sub>b" 50)
    and is_good :: "'n \<Rightarrow> bool"
    and good_member :: "'n \<Rightarrow> 'q2 \<Rightarrow> bool" (infix "\<in>\<^sub>g" 50)
  assumes 
    "\<And> q n . n \<in>\<^sub>g q \<Longrightarrow> is_good n" 
      \<comment> \<open>good quorums contain only good nodes\<close>
    and "\<And> q1 q2 . \<exists> n . n \<in>\<^sub>g q1 \<and> n \<in>\<^sub>g q2" 
      \<comment> \<open>good quorums intersect\<close>
    and "\<And> q1 . \<exists> q2 . \<forall> n . n \<in>\<^sub>g q2 \<longrightarrow> n \<in>\<^sub>b q1" 
      \<comment> \<open>every byz quorum contains at least one good quorum\<close>

locale fol_bft = byz_quorums + linorder less_eq less for
  less_eq :: "'r \<Rightarrow> 'r \<Rightarrow> bool" (infix "\<le>" 50) and less (infix "<" 50) +
fixes bot :: 'r
  \<comment> \<open>the special bottom round\<close>
begin

no_notation 
  ord_class.less_eq ("op \<le>") and
  ord_class.less_eq  ("(_/ \<le> _)"  [51, 51] 50) and
  ord_class.less ("op <") and
  ord_class.less  ("(_/ < _)"  [51, 51] 50) and
  Set.member  ("op \<in>") and
  Set.member  ("(_/ \<in> _)" [51, 51] 50)

lemma False 
  \<comment> \<open>checking for inconsistent hypothesis\<close>
  nitpick[expect=genuine, verbose=true] oops

lemmas fol_bft_assms = fol_bft_axioms fol_bft_def class.linorder_def class.order_def
    class.preorder_def class.order_axioms_def class.linorder_axioms_def byz_quorums_def
  
end
  
section "Abstract PBFT Model"
  
text "We use propose messages to verify 1b messages as in Lamport's version of PBFT.
We do not model pre-prepare messages."
  
context fol_bft
begin

definition byz_send where
  \<comment> \<open>byzantine nodes can do anything but impersonate non-byz nodes\<close>
  "byz_send vote_msg proposal start_round_msg left_round joined_round
      vote_msg' proposal' start_round_msg' left_round' joined_round' \<equiv>
    \<forall> n . is_good n \<longrightarrow> (
      vote_msg' n = vote_msg n
      \<and> left_round' n = left_round n
      \<and> joined_round' n = joined_round n 
      \<and> proposal' n = proposal n)"

definition join_round where
  "join_round vote_msg proposal start_round_msg left_round joined_round
      vote_msg' proposal' start_round_msg' left_round' joined_round' n r \<equiv>
    r \<noteq> bot
    \<and> start_round_msg r
    \<and> \<not> left_round n r
    \<and> (\<forall> n' r' . left_round' n' r' = ((left_round n' r') \<or> (n' = n \<and> r' < r)))
    \<and> joined_round' = joined_round(n := (joined_round n)(r := True))
    \<and> vote_msg' = vote_msg \<and> proposal' = proposal \<and> start_round_msg' = start_round_msg"

definition propose where
  "propose vote_msg proposal start_round_msg left_round joined_round
      vote_msg' proposal' start_round_msg' left_round' joined_round' n q r \<equiv>
    (\<forall> v . \<not> proposal n r v)
    \<and> r \<noteq> bot
    \<and> (\<forall> n . n \<in>\<^sub>b q \<longrightarrow> joined_round n r)
    \<and> (\<exists> v .
        ( (\<forall> n r' v . n \<in>\<^sub>b q \<and> r' < r \<longrightarrow> \<not>vote_msg n r' v)
          \<or> (\<exists> rmax . rmax \<noteq> bot \<and> rmax < r
            \<and> (\<forall> n v' . n \<in>\<^sub>b q \<and> vote_msg n rmax v' \<longrightarrow> v = v')
            \<and> (\<forall> n r' v . n \<in>\<^sub>b q \<and> vote_msg n r' v \<and> r' < r \<longrightarrow> r' \<le> rmax)
            \<and> (\<exists> n . is_good n \<and> proposal n rmax v)) )
        \<and> proposal' = proposal(n := (proposal n)(r := (proposal n r)(v := True))) )
    \<and> vote_msg' = vote_msg \<and> start_round_msg' = start_round_msg \<and> left_round = left_round' \<and> joined_round' = joined_round"

definition vote where
  "vote vote_msg proposal start_round_msg left_round joined_round
      vote_msg' proposal' start_round_msg' left_round' joined_round' n q r v \<equiv>
    r \<noteq> bot
    \<and> \<not> left_round n r
    \<and> (\<exists> q . \<forall> n . n \<in>\<^sub>b q \<longrightarrow> proposal n r v)
    \<and> vote_msg' = vote_msg(n := (vote_msg n)(r := (vote_msg n r)(v := True)))
    \<and> proposal' = proposal \<and> left_round = left_round' \<and> joined_round' = joined_round \<and> start_round_msg' = start_round_msg"
  
definition trans where
  "trans vote_msg proposal start_round_msg left_round joined_round vote_msg' proposal' start_round_msg' left_round' joined_round' n r v q \<equiv>
      join_round vote_msg proposal start_round_msg left_round joined_round vote_msg' proposal' start_round_msg' left_round' joined_round' n r
      \<or> propose vote_msg proposal start_round_msg left_round joined_round vote_msg' proposal' start_round_msg' left_round' joined_round' n q r
      \<or> vote vote_msg proposal start_round_msg left_round joined_round vote_msg' proposal' start_round_msg' left_round' joined_round' n q r v
      \<or> byz_send vote_msg proposal start_round_msg left_round joined_round vote_msg' proposal' start_round_msg' left_round' joined_round'"

section "Auxiliary Invariants and Safety Property"

definition inv1 where
  "inv1 vote_msg proposal start_round_msg left_round joined_round \<equiv> \<forall> n r v .
    (\<forall> r' . is_good n \<and> joined_round n r \<and> r' < r \<longrightarrow> left_round n r')
    \<and> (is_good n \<and> vote_msg n r v \<longrightarrow> (\<exists> q . \<forall> n . n \<in>\<^sub>g q \<longrightarrow> proposal n r v))
    \<and> (\<forall> v' . is_good n \<and> proposal n r v \<and> proposal n r v' \<longrightarrow> v = v')"

definition choosable_inv where
  "choosable_inv vote_msg proposal start_round_msg left_round joined_round \<equiv>
    \<forall> r1 r2 v1 v2 n . r1 < r2 \<and> is_good n \<and> proposal n r2 v2 \<and> v1 \<noteq> v2 \<longrightarrow>
        (\<forall> q2 . \<exists> n2 . n2 \<in>\<^sub>g q2 \<and> left_round n2 r1 \<and> \<not> vote_msg n2 r1 v1)"

definition safety where
  "safety vote_msg proposal start_round_msg left_round joined_round \<equiv>
    \<forall> r r' q q' v v' . (\<forall> n . n \<in>\<^sub>b q \<longrightarrow> vote_msg n r v) \<and> (\<forall> n . n \<in>\<^sub>b q' \<longrightarrow> vote_msg n r' v')
      \<longrightarrow> v = v'"

section "Safety proof"

lemma inv1:
  assumes "inv1 vote_msg proposal start_round_msg left_round joined_round" and
    "trans vote_msg proposal start_round_msg left_round joined_round 
      vote_msg' proposal' start_round_msg' left_round' joined_round' n r v q"
  shows "inv1 vote_msg' proposal' start_round_msg' left_round' joined_round'"
  (*<*) (* nitpick[card 'a=5, card 'd=5, card 'e=2, card 'c=2, card 'b=2, expect=none] *) (*>*)
  using assms fol_bft_axioms
  unfolding trans_def inv1_def byz_send_def join_round_def propose_def vote_def fol_bft_assms
  apply rewrite_funs apply smt
  done
    
lemma choosable:
  assumes "inv1 vote_msg proposal start_round_msg left_round joined_round"
    "choosable_inv vote_msg proposal start_round_msg left_round joined_round" and
    "trans vote_msg proposal start_round_msg left_round joined_round 
      vote_msg' proposal' start_round_msg' left_round' joined_round' n r v q"
  shows "choosable_inv vote_msg' proposal' start_round_msg' left_round' joined_round'"
  (*<*) (* nitpick[card 'a=5, card 'd=4, card 'e=2, card 'c=2, card 'b=2, expect=none, timeout=300] *) (*>*)
  using assms fol_bft_axioms
  unfolding trans_def inv1_def byz_send_def join_round_def propose_def vote_def
    fol_bft_assms choosable_inv_def
  apply rewrite_funs apply smt
  done
  
lemma safety:
  assumes "inv1 vote_msg proposal start_round_msg left_round joined_round" and
    "choosable_inv vote_msg proposal start_round_msg left_round joined_round"
  shows "safety vote_msg proposal start_round_msg left_round joined_round"
  using assms fol_bft_axioms
  unfolding safety_def inv1_def choosable_inv_def choosable_inv_def fol_bft_assms
  apply auto apply metis
  done

end
  
end