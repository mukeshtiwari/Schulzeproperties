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
  Candidates.
  
Import ListNotations.
Open Scope Z.

Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.


Module Schulze (Import Cand : Candidate).
  Module Import M := Margin Cand. 

  Definition ballot := cand -> nat.

  Inductive State: Type :=
  | partial: (list ballot * list ballot)  -> (cand -> cand -> Z) -> State
  | winners: (cand -> bool) -> State.

 
  Inductive Count (bs : list ballot) : State -> Type :=
  | ax us m : us = bs -> (forall c d, m c d = 0) ->
      Count bs (partial (us, []) m)             (* zero margin      *)
  | cvalid u us m nm inbs : Count bs (partial (u :: us, inbs) m) ->
      (forall c, (u c > 0)%nat) ->              (* u is valid       *)
      (forall c d : cand,
        ((u c < u d)%nat -> nm c d = m c d + 1) (* c preferred to d *) /\
        ((u c = u d)%nat -> nm c d = m c d)     (* c, d rank equal  *) /\
        ((u c > u d)%nat -> nm c d = m c d - 1))(* d preferred to c *) ->
      Count bs (partial (us, inbs) nm)
  | cinvalid u us m inbs : Count bs (partial (u :: us, inbs) m) ->
      (exists c, (u c = 0)%nat)                 (* u is invalid     *) ->
      Count bs (partial (us, u :: inbs) m)
  | fin m inbs w 
      (d : (forall c, (wins_type m c) + (loses_type m c))):
      Count bs (partial ([], inbs) m)           (* no ballots left  *) ->
      (forall c, w c = true  <-> (exists x, d c = inl x)) ->
      (forall c, w c = false <-> (exists x, d c = inr x)) ->
      Count bs (winners w).

  Local Open Scope nat_scope.

  Definition forall_exists_fin_dec : forall (A : Type) (l : list A) (f : A -> nat),
      {forall x, In x l -> f x > 0} + {exists x, In x l /\ f x = 0} := 
      fun (A : Type) =>
        fix F l f {struct l} :=
        match l with
        | [] => left (fun (x : A) (H : In x []) => match H with end)
        | h :: t =>
          match Nat.eq_dec (f h) 0 with
          | left e =>
            right (ex_intro _  h (conj (in_eq h t) e))
          | right n =>
            match F t f with
            | left Fl =>
              left (fun x H =>
                      match H with
                      | or_introl H1 =>
                        match zerop (f x) with
                        | left e =>
                          False_ind (f x > 0) ((eq_ind h (fun v : A => f v <> 0) n x H1) e)
                        | right r => r
                        end
                      | or_intror H2 => Fl x H2
                      end)
            | right Fr =>
              right
                match Fr with
                | ex_intro _ x (conj Frl Frr) =>
                  ex_intro _ x (conj (in_cons h x t Frl) Frr)
                end
            end
          end
        end.

    Definition ballot_valid_dec : forall b : ballot, {forall c, b c > 0} + {exists c, b c = 0} :=
      fun b => let H := forall_exists_fin_dec cand cand_all in
               match H b with
               | left Lforall => left
                                   (fun c : cand => Lforall c (cand_fin c))
               | right Lexists => right
                                    match Lexists with
                                    | ex_intro _ x (conj _ L) =>
                                      ex_intro (fun c : cand => b c = 0) x L
                                    end
               end.

    Local Open Scope Z_scope.

    Definition update_marg (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
      fun c d =>  if (Nat.ltb (p c) (p d))%nat
               then (m c d + 1)%Z
               else (if (Nat.ltb (p d) (p c))%nat
                     then (m c d -1)%Z
                     else m c d).

    Definition listify_v (m : cand -> cand -> Z) :=
      map (fun s => (fst s, snd s, m (fst s) (snd s))) (all_pairs cand_all). 


    Fixpoint linear_search_v (c d : cand) (m : cand -> cand -> Z) l :=
      match l with
      | [] => m c d
      | (c1, c2, k) :: t =>
        match dec_cand c c1, dec_cand d c2 with
        | left _, left _ => k
        | _, _ => linear_search_v c d m t
        end
      end.
    
    Definition update_marg_listify (p : ballot) (m : cand -> cand -> Z) : cand -> cand -> Z :=
      let t := update_marg p m in
      let l := listify_v t in
      fun c d => linear_search_v c d t l.

    Theorem equivalent_m_w_v : forall c d m, linear_search_v c d m (listify_v m) = m c d.
    Proof.
      unfold  listify_v.
      intros. induction (all_pairs cand_all); simpl; auto.
      destruct a as (a1, a2). simpl in *.
      destruct (dec_cand c a1).
      destruct (dec_cand d a2). subst. auto.
      auto. auto.
    Qed.

    Corollary equiv_cor : forall p m c d, update_marg p m c d = update_marg_listify p m c d.
    Proof.
      intros p m c d.  unfold update_marg_listify.
      rewrite <- equivalent_m_w_v. 
      auto.
    Qed.
      
    (* correctness of update_marg above *)
    Lemma update_marg_corr: forall m (p : ballot) (c d : cand),
        ((p c < p d)%nat -> update_marg p m c d = m c d + 1) /\
        ((p c = p d)%nat -> update_marg p m c d = m c d) /\
        ((p c > p d)%nat -> update_marg p m c d = m c d - 1).
    Proof.
      intros m p c d.
      split; intros; unfold update_marg.
      destruct (p c <? p d)%nat eqn: H1. lia.
      destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. lia.
      apply Nat.ltb_ge in H2. apply Nat.ltb_ge in H1. lia.
      split; intros.
      destruct (p c <? p d)%nat eqn: H1.
      apply Nat.ltb_lt in H1. lia.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2. apply Nat.ltb_lt in H2.
      apply Nat.ltb_ge in H1. lia. apply Nat.ltb_ge in H2. lia.
      unfold update_marg.
      destruct (p c <? p d)%nat eqn:H1. apply Nat.ltb_lt in H1. lia.
      apply Nat.ltb_ge in H1. destruct (p d <? p c)%nat eqn: H2.
      apply Nat.ltb_lt in H2. lia. apply Nat.ltb_ge in H2. lia.
    Qed.

    
    Lemma update_marg_corr_listify: forall m (p : ballot) (c d : cand),
      ((p c < p d)%nat -> update_marg_listify p m c d = m c d + 1) /\
      ((p c = p d)%nat -> update_marg_listify p m c d = m c d) /\
      ((p c > p d)%nat -> update_marg_listify p m c d = m c d - 1).
    Proof.
      intros m p c d. rewrite <- equiv_cor. apply update_marg_corr.
    Qed.


    Definition partial_count_all_counted bs : forall u inbs m,
        Count bs (partial (u, inbs) m) ->  existsT i m, (Count bs (partial ([], i) m)) :=
      fix F u {struct u} :=
        match u with
        | [] =>
          fun inbs m Hc =>
            existT _ inbs (existT _ m Hc)
        | h :: t =>
          fun inbs m Hc =>
            match ballot_valid_dec h with
            | left Hv =>
              let w := update_marg_listify h m in 
              F t inbs w (cvalid bs h t m w inbs Hc Hv (update_marg_corr_listify m h))
            | right Hi =>  F t (h :: inbs) m (cinvalid bs h t m inbs Hc Hi)
            end
      end.


    Definition all_ballots_counted (bs : list ballot) :
      existsT i m, Count bs (partial ([], i) m) :=
      partial_count_all_counted bs bs [] (fun _ _ : cand => 0)
                                (ax bs bs (fun _ _ : cand => 0) eq_refl
                                    (fun _ _ : cand => eq_refl)).

    
    Definition schulze_winners (bs : list ballot) :
      existsT (f : cand -> bool), Count bs (winners f).
    Proof.
      destruct (all_ballots_counted bs) as [inv [m p]].
      exists (c_wins m).
      eapply fin.
      + exact p.
      + split; intros.
        instantiate (1 := wins_loses_type_dec m).
        eapply c_wins_true_type in H; exact H. 
        eapply c_wins_true_type; exact H.
      + split; intros.
        eapply c_wins_false_type in H; exact H.
        eapply c_wins_false_type; exact H.
    Defined.  
        


End Schulze.
