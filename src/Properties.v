Require Import Notations
  Coq.Lists.List
  Coq.Arith.Arith
  Coq.Arith.Compare_dec
  Coq.Bool.Sumbool
  Coq.Bool.Bool
  Coq.ZArith.ZArith
  Coq.Logic.FinFun
  Coq.Program.Basics
  Coq.Logic.FunctionalExtensionality
  Psatz
  ListLemma
  Margin
  Schulze
  Candidates.


Import ListNotations.
Open Scope Z.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

Module Properties (Import Cand : Candidate).
  Module Import M := Margin Cand.
  Module Import S := Schulze Cand.

  (* we assume that margin matrix is symmetric. *)
  Axiom marg_neq :
    forall (c d : cand) 
    (marg : cand -> cand -> Z), 
    marg c d = -marg d c. 


  (* candidate c is a weak Condorcet winner if 
    it ties with every other candidates *)
  Definition condercet_winner 
    (c : cand) (marg : cand -> cand -> Z) :=
    forall d, 0 <= marg c d.

  
  Lemma gen_marg_gt₀ :
    forall (c d : cand) n (marg : cand -> cand -> Z), 
    condercet_winner c marg ->
    0 <= M marg n c d.
  Proof. 
    unfold condercet_winner. 
    intros c d n marg Hc.
    rewrite M_M_new_equal. 
    revert d; revert n.
    induction n; cbn; try auto.
    intros d. 
    pose proof (IHn d).
    nia.
  Qed.


  Lemma gen_marg_lt₀ :
    forall c d n marg, 
    condercet_winner c marg ->
    M marg n d c <= 0.
  Proof.
    unfold condercet_winner. 
    intros c d n marg Hc.
    rewrite M_M_new_equal.
    revert d; revert n.
    induction n.
    + cbn. intros d. pose proof (marg_neq c d marg).
      pose proof (Hc d). lia. 
    + cbn. intros d.
      apply Z.max_lub_iff. 
      split.
      pose proof (IHn d). lia.
      apply upperbound_of_nonempty_list;
      [apply Cand.cand_not_nil |
      apply Cand.dec_cand | 
      intros x Hx; pose proof (IHn x);
      nia].
  Qed.


  Lemma condercet_winner_genmarg :
    forall c d n marg, 
    condercet_winner c marg -> 
    M marg n d c <= M marg n c d.
  Proof.
    intros c d n marg Hc.
    pose proof (gen_marg_gt₀ c d n marg Hc).
    pose proof (gen_marg_lt₀ c d n marg Hc).
    nia.
  Qed.


  Lemma condercet_winner_headoff :
    forall c marg, 
    condercet_winner c marg <-> 
    (forall d,  marg d c <= marg c d).
  Proof.
    split; intros Hc d.
    +  
    unfold condercet_winner in Hc.
    pose proof (Hc d).
    pose proof (marg_neq c d marg).
    nia.
    + 
    pose proof (Hc d). 
    pose proof (marg_neq d c marg).
    nia.
  Qed.


  (* if candidate c ties everyone in head to head count, then it ties
    everyone in generalized margin *)
  Lemma condercet_winner_marg (c : cand) (marg : cand -> cand -> Z) :
    forall n, 
    (forall d, marg d c <= marg c d) -> 
    forall d, M marg n d c <= M marg n c d.
  Proof. 
    intros n Hc d.
    apply condercet_winner_genmarg.
    apply condercet_winner_headoff.
    assumption.
  Qed.
  
  (* if candidate c is condercet winner then it's winner of election *)
  Lemma condercet_winner_implies_winner 
    (c : cand) (marg : cand -> cand -> Z) :
    condercet_winner c marg -> 
    c_wins marg c = true. 
  Proof.
    intros Hc. 
    apply c_wins_true; intro d.
    exact (condercet_winner_genmarg c d (length cand_all) marg Hc).
  Qed.

  (* End of condercet property *)

  (* Beginning of reversal symmetry *)
  (* We reverse the ballot. Reversing the ballot and computing 
     the margin is equlivalent to marg d c*)

  (* Notion of Unique Winner *)
  Definition unique_winner (marg : cand -> cand -> Z) (c : cand) :=
    c_wins marg c = true /\ 
    (forall d, d <> c -> c_wins marg d = false).

  (* We multiply -1 to margin matrix *)
  Definition rev_marg (marg : cand -> cand -> Z) (c d : cand) :=
     -marg c d. 


  (* our goal is to prove *)
  Lemma winner_reversed :
    forall marg c, 
    unique_winner marg c ->
    (exists d, c_wins marg d = false /\ c <> d) ->
    c_wins (rev_marg marg) c = false.
  Proof.
  Admitted.

  

End Properties.
