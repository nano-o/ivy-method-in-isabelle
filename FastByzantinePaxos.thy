text \<open>Fast Paxos made Byzantine by loosely following the reasoning of Lamport et al. as explained in the paper "Byzantizing Paxos by Refinement".
  Here there is no refinement though; instead, we think of Byzantizing as maintaining the same invariants as Fast Paxos.\<close>

theory FastByzantinePaxos
  imports Main
begin                                 

section "First-Order Abstraction"

locale byz_quorums =
  fixes byz_member :: "'n \<Rightarrow> 'q1 \<Rightarrow> bool" (infix "\<in>\<^sub>b" 50)
    \<comment> \<open>this models 2/3 quorums\<close>
    and third_member :: "'n \<Rightarrow> 'q4 \<Rightarrow> bool" (infix "\<in>\<^sub>t" 50)
    \<comment> \<open>this models 1/3 quorums\<close>

    \<comment> \<open>ghost relations below:\<close>
    and is_good :: "'n \<Rightarrow> bool"
      \<comment> \<open>a good node is not byzantine\<close>
    and ghost_classic_member :: "'n \<Rightarrow> 'q2 \<Rightarrow> bool" (infix "\<in>\<^sub>c" 50)
      \<comment> \<open>this models classic quorums of Fast Paxos. Classic quorums are majorities among the good nodes\<close>
    and ghost_fast_member :: "'n \<Rightarrow> 'q3 \<Rightarrow> bool" (infix "\<in>\<^sub>f" 50)
      \<comment> \<open>this models fast quorums of Fast Paxos. They consist of more than 2/3rds among the good nodes\<close>
  \<comment> \<open>The quorum types @{typ 'q2} and @{typ 'q3} are "ghost" in the sense that they are
  only used in the proof. They are the quorums of crash-stop Fast-Paxos.\<close>
  assumes 
    "\<And> q n . n \<in>\<^sub>c q \<Longrightarrow> is_good n" 
      \<comment> \<open>ghost classic quorums contain only good nodes\<close>
    "\<And> q n . n \<in>\<^sub>f q = is_good n" 
      \<comment> \<open>there is only one ghost fast quorum, containing all good nodes (this is stronger than in Fast Paxos)\<close>
    and "\<And> q1 q2 . \<exists> n . n \<in>\<^sub>c q1 \<and> n \<in>\<^sub>c q2"
      \<comment> \<open>ghost classic quorums intersect\<close>
    and "\<And> bq . \<exists> cq . \<forall> n . n \<in>\<^sub>c cq \<longrightarrow> n \<in>\<^sub>b bq"
      \<comment> \<open>a byzantine quorum contains a ghost classic quorum\<close>
    and "\<And> thq . \<exists> n . is_good n \<and> n \<in>\<^sub>t thq"
      \<comment> \<open>1/3 quorums contain a good node\<close> (* We can wait for at least one good node by waiting for a 1/3-quorum *)
    and "\<And> cq . \<exists> thq . \<forall> n . n \<in>\<^sub>c cq = (n \<in>\<^sub>t thq)"
      \<comment> \<open>For every ghost classic quorum there is a 1/3-quorum that contains it.\<close>

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

lemmas fol_bft_assms_defs = fol_bft_axioms fol_bft_def class.linorder_def class.order_def
    class.preorder_def class.order_axioms_def class.linorder_axioms_def byz_quorums_def
  
end
  
section "Abstract Model"
  
record ('n, 'r, 'v) state =
  \<comment> \<open>The state of the system\<close>
  vote_msg :: "'n \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool"
  any_msg :: "'n \<Rightarrow> 'r \<Rightarrow> bool"
  prepare_msg :: "'n \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool"
  left_round :: "'n \<Rightarrow> 'r \<Rightarrow> bool"
  joined_round :: "'n \<Rightarrow> 'r \<Rightarrow> bool"
  
locale fast_fol_bft = fol_bft + fixes is_fast :: "'f \<Rightarrow> bool"
begin

definition join_round where
  "join_round s s' n r \<equiv>
    r \<noteq> bot \<and> \<not> left_round s n r
    \<and> (\<exists> left_round' . left_round' = (\<lambda> r' . left_round s n r' \<or> r' < r)
        \<and> s' = s\<lparr>left_round := (left_round s)(n := left_round'),
          joined_round := (joined_round s)(n := (joined_round s n)(r := True))\<rparr>)"

text "We do not model pre-prepare messages"

text \<open>Below, Node @{term n} sends a prepare or "any" msg for round @{term r} according to the information gathered
  from quorum @{term q}.\<close>
definition prepare where "prepare s s' n q r \<equiv>
  (\<forall> v . \<not> prepare_msg s n r v)
  \<and> \<not> any_msg s n r
  \<and> r \<noteq> bot
  \<and> (\<forall> n . n \<in>\<^sub>b q \<longrightarrow> joined_round s n r) \<comment> \<open>A quorum joined the round\<close>
  \<and> 
  (\<exists> v .
    \<comment> \<open>no vote reported:\<close>
    ((\<forall> n r' v . (n \<in>\<^sub>b q \<and> r' < r \<longrightarrow> \<not>vote_msg s n r' v))
      \<and> (if is_fast r
          then s' = s\<lparr>any_msg := (any_msg s)(n := (any_msg s n)(r := True))\<rparr>
          else s' = s\<lparr>prepare_msg := (prepare_msg s)(n := (prepare_msg s n)
            (r := (prepare_msg s n r)(v := True)))\<rparr>))
    \<or>
    \<comment> \<open>some votes reported:\<close>
    (\<exists> rmax . rmax \<noteq> bot \<and> rmax < r
      \<and> (\<forall> n r' v . n \<in>\<^sub>b q \<and> vote_msg s n r' v \<and> r' < r \<longrightarrow> r' \<le> rmax)
      \<and> (if \<not> is_fast rmax 
        then 
          (\<exists> thq . \<forall> n . n \<in>\<^sub>t thq \<longrightarrow> prepare_msg s n rmax v) \<comment> \<open>one good node sent the prepare\<close>
          \<and> (\<forall> n v' . n \<in>\<^sub>b q \<and> vote_msg s n rmax v' \<longrightarrow> v' = v)
          \<and> s' = s\<lparr>prepare_msg := (prepare_msg s)(n := (prepare_msg s n)(r := (prepare_msg s n r)(v := True)))\<rparr>
        else 
          (\<exists> thq . (\<forall> n . n \<in>\<^sub>t thq \<longrightarrow> any_msg s n rmax) \<or> (\<forall> n . n \<in>\<^sub>t thq \<longrightarrow> prepare_msg s n rmax v))
          \<and>
          (\<exists> v2 . 
            ( (\<exists> thq . (\<forall> n . n \<in>\<^sub>t thq \<longrightarrow> n \<in>\<^sub>b q \<and> vote_msg s n rmax v2))
              \<or> (v2 = v \<and> (\<forall> v' thq . (\<forall> n . n \<in>\<^sub>t thq \<longrightarrow> n \<in>\<^sub>b q) \<longrightarrow> (\<exists> n . n \<in>\<^sub>t thq \<and> \<not> vote_msg s n rmax v'))))
            \<and> s' = s\<lparr>prepare_msg := (prepare_msg s)(n := (prepare_msg s n)(r := (prepare_msg s n r)(v2 := True)))\<rparr>)) ))"

definition classic_vote where
  "classic_vote s s' n q r v \<equiv>
    r \<noteq> bot
    \<and> \<not> is_fast r
    \<and> \<not> left_round s n r
    \<and> (\<exists> q . \<forall> n . n \<in>\<^sub>b q \<longrightarrow> prepare_msg s n r v)
    \<and> s' = s\<lparr>vote_msg := (vote_msg s)(n := (vote_msg s n)(r := (vote_msg s n r)(v := True)))\<rparr>"
  
definition fast_vote where
  "fast_vote s s' n q r v \<equiv> 
    r \<noteq> bot
    \<and> is_fast r
    \<and> (\<forall> v . \<not> vote_msg s n r v)
    \<and> \<not> left_round s n r
    \<and> (\<exists> q . \<forall> n . n \<in>\<^sub>b q \<longrightarrow> any_msg s n r)
    \<and> s' = s\<lparr>vote_msg := (vote_msg s)(n := (vote_msg s n)(r := (vote_msg s n r)(v := True)))\<rparr>"

text \<open>Note we do not model byzantine nodes. That is because our invariant do not mention byzantine nodes,
  therefore their state (i.e. state and messages) can be arbibrary.\<close>

definition trans where
  \<comment> \<open>The transition relation of the system.\<close>
  "trans s s' \<equiv> \<exists> n r q v .
    join_round s s' n r \<or> prepare s s' n q r \<or> classic_vote s s' n q r v \<or> fast_vote s s' n q r v"

section "Auxiliary Invariants and Safety Property"

definition inv1 where
  \<comment> \<open>Auxiliary, simple invariants\<close>
  "inv1 s \<equiv> \<forall> n r v . is_good n \<longrightarrow>
    (\<forall> r' . joined_round s n r \<and> r' < r \<longrightarrow> left_round s n r')
    \<and> ((vote_msg s n r v \<and> \<not> is_fast r) \<longrightarrow> (\<exists> cq . \<forall> n . n \<in>\<^sub>c cq \<longrightarrow> prepare_msg s n r v))
    \<and> (vote_msg s n r v \<and> is_fast r \<longrightarrow> 
        (\<exists> cq . (\<forall> n . n \<in>\<^sub>c cq \<longrightarrow> any_msg s n r)
          \<or> (\<forall> n . n \<in>\<^sub>c cq \<longrightarrow> prepare_msg s n r v)))
    \<and> (\<forall> v' . (vote_msg s n r v \<and> vote_msg s n r v' \<longrightarrow> v = v'))
    \<and> (\<forall> v' . prepare_msg s n r v \<and> prepare_msg s n r v' \<longrightarrow> v = v')
    \<and> (any_msg s n r \<longrightarrow> is_fast r)
    \<and> \<not> (prepare_msg s n r v \<and> any_msg s n r)"

text \<open>The main invariants. Those are the same as in Fast Paxos.\<close>

definition choosable_classic where
  "choosable_classic s \<equiv>
    \<forall> r1 r2 v1 v2 n . \<not> is_fast r1 \<and> r1 < r2 \<and> is_good n \<and> ((prepare_msg s n r2 v2 \<and> v1 \<noteq> v2) \<or> any_msg s n r2) \<longrightarrow>
        (\<forall> q2 . \<exists> n2 . n2 \<in>\<^sub>c q2 \<and> left_round s n2 r1 \<and> \<not> vote_msg s n2 r1 v1)"

definition choosable_fast where
  "choosable_fast s \<equiv>
    \<forall> r1 r2 v1 v2 n . is_fast r1 \<and> r1 < r2 \<and> is_good n \<and> ((prepare_msg s n r2 v2 \<and> v1 \<noteq> v2) \<or> any_msg s n r2) \<longrightarrow>
        (\<forall> q2 . \<exists> n2 . n2 \<in>\<^sub>f q2 \<and> left_round s n2 r1 \<and> \<not> vote_msg s n2 r1 v1)"

text \<open>The safety property\<close>

definition chosen where
  "chosen s r v \<equiv> if is_fast r
    then (\<exists> q . \<forall> n . n \<in>\<^sub>f q \<longrightarrow> vote_msg s n r v)
    else (\<exists> q . \<forall> n . n \<in>\<^sub>c q \<longrightarrow> vote_msg s n r v)"

definition safety where
  "safety s \<equiv> 
    \<forall> v v' r r' . chosen s r v \<and> chosen s r' v' \<longrightarrow> v = v'"

end
  
end