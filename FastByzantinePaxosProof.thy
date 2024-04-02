theory FastByzantinePaxosProof
  imports FastByzantinePaxos "HOL-Eisbach.Eisbach"
begin

declare [[smt_reconstruction_step_timeout=1000, smt_certificates="./FBFT.cert", smt_oracle=true]]
declare  [[smt_timeout=300]]  

method rewrite_funs = (simp (no_asm_use) only: fun_upd_apply[abs_def] fun_eq_iff if_split_asm)
  \<comment> \<open>rewrites function-update and function equality terms to first-order equality.\<close>

context fast_fol_bft begin

section "Safety proof"

declare if_splits[split]

method rw_record_expr for s = 
  (cases s; simp; match premises in P[thin]:"s = _" \<Rightarrow> \<open>-\<close>)

lemma inv1:
  fixes s :: "('a,'f,'g) state"
  assumes "inv1 s" and "trans s s'" shows "inv1 s'"
  using assms
  unfolding trans_def inv1_def join_round_def prepare_def classic_vote_def fast_vote_def
  apply -
  apply (rw_record_expr s; rw_record_expr s')
     apply (simp_all add:fun_eq_iff)
            apply (insert fol_bft_axioms[simplified fol_bft_assms_defs])
            apply smt+
  done

lemma choosable_classic:
  fixes s :: "('a,'f,'g) state"
  assumes "inv1 s"  and "choosable_classic s" and "trans s s'"
  shows "choosable_classic s'"
  using assms
  unfolding trans_def inv1_def join_round_def prepare_def classic_vote_def fast_vote_def choosable_classic_def choosable_fast_def
  apply -
  apply (rw_record_expr s; rw_record_expr s') 
      apply (simp_all add:fun_eq_iff)
             apply (insert fol_bft_axioms[simplified fol_bft_assms_defs])
         apply (clarify; smt)+
  done

lemma choosable_fast:
  fixes s :: "('a,'f,'g) state"
  assumes "inv1 s" and "choosable_fast s" and "trans s s'"
  shows "choosable_fast s'"
  using assms
  unfolding trans_def inv1_def join_round_def prepare_def classic_vote_def fast_vote_def choosable_fast_def choosable_classic_def
  apply -
  apply (rw_record_expr s; rw_record_expr s') 
      apply (simp_all add:fun_eq_iff)
             apply (insert fol_bft_axioms[simplified fol_bft_assms_defs])
         apply (clarify; smt)+ 
  done
  
lemma safety:
  fixes s :: "('a, 'f, 'g) state"
  assumes "inv1 s" and "choosable_classic s" and "choosable_fast s" shows "safety s" 
  using assms fol_bft_axioms
  unfolding safety_def inv1_def choosable_classic_def choosable_fast_def chosen_def  
  apply -
  apply (insert fol_bft_axioms[simplified fol_bft_assms_defs])
  apply (clarify; smt)+
  done

end

end