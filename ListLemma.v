Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z.
Require Import
        Program Morphisms Relations RelationClasses Permutation.



Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.



Fixpoint all_pairs_row_t {A : Type} (l1 : list A) (l2 : list A) : list (A * A) :=
  match l1 with
  | [] => []
  | c :: cs =>
    map (fun x => (c, x)) l2 ++ all_pairs_row_t cs l2
  end.

Eval compute in all_pairs_row_t [1;2;3] [4].

Lemma row_t_correctness :
  forall (A : Type) (a1 a2 : A) (l1 l2 : list A),
    In a1 l1 -> In a2 l2 -> In (a1, a2) (all_pairs_row_t l1 l2). 
Proof.
  intros A a1 a2.
  induction l1; simpl; intros; try auto.
  - destruct H; subst.
    +  apply in_app_iff.  
       left. apply in_map. auto.
    +  apply in_app_iff. right. auto.
Qed.

Definition all_pairs_row {A : Type} (l : list A) : list (A * A) :=
  all_pairs_row_t l l.

Lemma all_pairs_row_in :
  forall (A : Type) (a1 a2 : A) (l : list A),
    In a1 l -> In a2 l -> In (a1, a2) (all_pairs_row l).
Proof.
  intros A a1 a2 l H1 H2.
  unfold all_pairs_row.
  pose proof (row_t_correctness A a1 a2 l l H1 H2); auto.
Qed.


Fixpoint all_pairs_col_t {A : Type} (l1 : list A) (l2 : list A) : list (A * A) :=
  match l1 with
  | [] => []
  | c :: cs =>
      map (fun x => (x, c)) l2 ++ all_pairs_col_t cs l2
  end.

Eval compute in all_pairs_col_t [1;2;3] [4].


Lemma col_t_correctness :
  forall (A : Type) (a1 a2 : A) (l1 l2 : list A),
    In a1 l1 -> In a2 l2 -> In (a2, a1) (all_pairs_col_t l1 l2). 
Proof.
  intros A a1 a2.
  induction l1; simpl; intros; try auto.
  - destruct H; subst.
    +  apply in_app_iff. 
       left. pose proof (in_map (fun x : A => (x, a1)) l2 a2 H0).
       simpl in H. auto.
    +  apply in_app_iff. right. pose proof (IHl1 l2 H H0).
       auto.
Qed.

Definition all_pairs_col {A : Type} (l : list A) : list (A * A) :=
  all_pairs_col_t l l.

Lemma all_pairs_col_in :
  forall (A : Type) (a1 a2 : A) (l : list A),
    In a1 l -> In a2 l -> In (a2, a1) (all_pairs_col l).
Proof.
  intros A a1 a2 l H1 H2.
  pose proof (col_t_correctness A a1 a2 l l H1 H2).
  auto.
Qed.



(* all_pairs computes all the pairs of candidates in l *)
Fixpoint all_pairs {A: Type} (l: list A): list (A * A) :=
  match l with
  | [] => []
  | c::cs => (c, c) :: (all_pairs cs)
                   ++  (map (fun x => (c, x)) cs)
                   ++ (map (fun x => (x, c)) cs)
  end.


Lemma all_pairsin: forall {A : Type} (a1 a2 : A) (l : list A),
    In a1 l -> In a2 l -> In (a1, a2) (all_pairs l).
Proof.
  intros A a1 a2 l H1 H2. induction l.
  inversion H1. simpl.
  destruct H1 as [H3 | H3].
  {
    destruct H2 as [H4 | H4].
    left. congruence.
    right. apply in_app_iff. right.
    apply in_app_iff. left.
    rewrite H3. apply in_map. assumption.
  }
  {
    destruct H2 as [H4 | H4].
    right. apply in_app_iff.
    right. apply in_app_iff.
    right. rewrite H4. apply in_map_iff.
    exists a1. split. auto. auto.
    right. apply in_app_iff. left.
    apply IHl. assumption. assumption.
  }
Qed.
  
Theorem length_all_pairs :
  forall (A : Type) (l : list A), length (all_pairs l)  = (length l * length l)%nat.
Proof.
  intros A l. induction l. simpl. auto.
  simpl. apply f_equal. repeat (rewrite app_length).
  repeat (rewrite map_length). rewrite IHl.
  remember (length l) as n. rewrite Nat.mul_succ_r.
  omega.
Qed.

Theorem length_all_pairs_t_row :
  forall (A : Type) (l1 l2 : list A) ,
    length (all_pairs_row_t l1 l2) = (length l1 * length l2)%nat.
Proof.
  intros A.
  induction l1; simpl; intros; try auto.
  rewrite app_length. rewrite map_length.
  apply f_equal. apply IHl1.
Qed.

Theorem length_all_pairs_row :
  forall (A : Type) (l : list A),
    length (all_pairs_row l) = (length l * length l)%nat.
Proof.
  intros A l.
  pose proof (length_all_pairs_t_row A l l).
  assumption.
Qed.



Theorem length_all_pairs_t_col :
  forall (A : Type) (l1 l2 : list A) ,
    length (all_pairs_col_t l1 l2) = (length l1 * length l2)%nat.
Proof.
  intros A.
  induction l1; simpl; intros; try auto.
  rewrite app_length. rewrite map_length.
  apply f_equal. apply IHl1.
Qed.

Theorem length_all_pairs_col :
  forall (A : Type) (l : list A),
    length (all_pairs_col l) = (length l * length l)%nat.
Proof.
  intros A l.
  pose proof (length_all_pairs_t_col A l l).
  assumption.
Qed.

  

(* maxlist return the maximum number in list l. 0 in case of empty list *)
Fixpoint maxlist (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | [h] => h
  | h :: t => Z.max h (maxlist t)
  end.

(* give two numbers m and n with proof that m < n then it return the
   proof that maximum of m and n is n *)
Lemma max_two_integer : forall (m n : Z), m < n -> Z.max m n = n.
Proof.
  intros m n H; apply Z.max_r; omega.
Qed.

(* Shows the prop level existence of element x in list l >=  s if maximum element of
   list l >= s  *)
Lemma max_of_nonempty_list :
  forall (A : Type) (l : list A) (H : l <> nil) (H1 : forall x y : A, {x = y} + {x <> y}) (s : Z) (f : A -> Z),
    maxlist (map f l) >= s <-> exists (x:A), In x l /\ f x >= s.
Proof.
  split; intros. generalize dependent l.
  induction l; intros. specialize (H eq_refl). inversion H.
  pose proof (list_eq_dec H1 l []).
  destruct H2. exists a. rewrite e. intuition. rewrite e in H0.
  simpl in H0. auto.
  assert (Hm : {f a >= maxlist (map f l)} + {f a < maxlist (map f l)}) by
      apply (Z_ge_lt_dec (f a) (maxlist (map f l))).
  destruct Hm. rewrite map_cons in H0.
  pose proof (exists_last n).  destruct X as [l1 [x l2]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in l2. rewrite l2. simpl. auto.
    rewrite l2. simpl. auto. }
  pose proof (Z.ge_le _ _ g). pose proof (Z.max_l _ _ H3).
  rewrite H2 in H0. rewrite H4 in H0. exists a. intuition.
  rewrite map_cons in H0. pose proof (exists_last n). destruct X as [l1 [x l2]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in l2. rewrite l2. simpl. auto.
    rewrite l2. simpl. auto. }
  rewrite H2 in H0. pose proof (max_two_integer _ _ l0). rewrite H3 in H0.
  specialize (IHl n H0). destruct IHl. exists x0. intuition.
  destruct H0 as [x [H2 H3]].
  induction l. specialize (H eq_refl). inversion H.
  pose proof (list_eq_dec H1 l []). destruct H0.
  (* empty list *)
  subst. simpl in *. destruct H2. subst. auto. inversion H0.
  (* not empty list *)
  rewrite map_cons. pose proof (exists_last n). destruct X as [l1 [x0 H4]].
  assert (maxlist (f a :: map f l) = Z.max (f a) (maxlist (map f l))).
  { destruct l1. simpl in H4. rewrite H4. simpl. auto.
    rewrite H4. simpl. auto. }
  rewrite H0. unfold Z.max. destruct (f a ?= maxlist (map f l)) eqn:Ht.
  destruct H2. subst. auto. pose proof (proj1 (Z.compare_eq_iff _ _) Ht).
  specialize (IHl n H2). rewrite H5. auto.
  destruct H2. subst.
  pose proof (proj1 (Z.compare_lt_iff _ _) Ht). omega.
  apply IHl. assumption. assumption.
  destruct H2. subst. assumption. specialize (IHl n H2).
  pose proof (proj1 (Z.compare_gt_iff _ _) Ht).  omega.
Qed.

(* minimum of two integers m and n is >= s then both numbers are
   >= s *)
Lemma z_min_lb : forall m n s, Z.min m n >= s <-> m >= s /\ n >= s.
Proof.
  split; intros. unfold Z.min in H.
  destruct (m ?= n) eqn:Ht.
  pose proof (proj1 (Z.compare_eq_iff _ _) Ht). intuition.
  pose proof (proj1 (Z.compare_lt_iff _ _) Ht). intuition.
  pose proof (proj1 (Z.compare_gt_iff _ _) Ht). intuition.
  destruct H as [H1 H2].
  unfold Z.min. destruct (m ?= n) eqn:Ht; auto.
Qed.

(* if length of list l >= 1 then  l is nonempty *)
Lemma exists_list : forall (A : Type) (l : list A) (n : nat),
    (length l >= S n)%nat -> exists a ls, l = a :: ls.
Proof.
  intros A l. destruct l eqn: Ht; intros; simpl in H. inversion H.
  exists a, l0. reflexivity.
Qed.

(* If a in list l and x in not in list l then x <> a *)
Lemma not_equal_elem : forall (A : Type) (a x : A) (l : list A),
    In a l -> ~ In x l -> x <> a.
Proof.
  intros A a x l H1 H2.
  induction l. inversion H1.
  specialize (proj1 (not_in_cons x a0 l) H2); intros.
  simpl in H1. destruct H as [H3 H4]. destruct H1.
  subst. assumption. apply IHl. assumption. assumption.
Qed.

(* all the elements appearing in l also appears in list c *)
Definition covers (A : Type) (c l : list A) := forall x : A, In x l -> In x c.

(* split the list l at duplicate elements given the condition that c covers l *)
Lemma list_split_dup_elem : forall (A : Type) (n : nat) (c : list A) (H1 : forall x y : A, {x = y} + {x <> y}),
    length c = n -> forall (l : list A) (H : (length l > length c)%nat),
      covers A c l -> exists (a : A) l1 l2 l3, l = l1 ++ (a :: l2) ++ (a :: l3).
Proof.
  intros A n. induction n; intros. unfold covers in H1. rewrite H in H0.
  unfold covers in H2. pose proof (proj1 (length_zero_iff_nil c) H).
  rewrite H3 in H2. simpl in H2. pose proof (exists_list _ _ _ H0).
  destruct H4 as [a [ls H4]]. rewrite H4 in H2. specialize (H2 a (in_eq a ls)). inversion H2.
  rewrite H in H0. pose proof (exists_list _ _ _ H0).
  destruct H3 as [l0 [ls H3]].
  pose proof (in_dec H1 l0 ls). destruct H4.
  pose proof (in_split l0 ls i). destruct H4 as [l1 [l2 H4]].
  rewrite H4 in H3. exists l0, [], l1, l2. simpl. auto.
  unfold covers in H2. rewrite H3 in H2.
  pose proof (H2 l0 (in_eq l0 ls)).
  pose proof (in_split l0 c H4). destruct H5 as [l1 [l2 H5]].
  rewrite H5 in H. rewrite app_length in H. simpl in H.
  assert (Ht : (length l1 + S (length l2))%nat = (S (length l1 + length l2))%nat) by omega.
  rewrite Ht in H. clear Ht. inversion H. clear H.
  rewrite <- app_length in H7.
  assert ((length ls > length (l1 ++ l2))%nat).
  { rewrite H7. rewrite H3 in H0. simpl in H0. omega. }
  specialize (IHn (l1 ++ l2) H1 H7 ls H).
  assert (covers A (l1 ++ l2) ls).
  { unfold covers. intros x Hin.
    specialize (not_equal_elem _ x l0 ls Hin n0); intros.
    specialize (H2 x (or_intror Hin)).
    rewrite H5 in H2.
    pose proof (in_app_or l1 (l0 :: l2) x H2). destruct H8.
    apply in_or_app. left. assumption.
    simpl in H8. destruct H8. contradiction.
    apply in_or_app. right. assumption. }
  specialize (IHn H6). destruct IHn as [a [l11 [l22 [l33 H10]]]].
  exists a, (l0 :: l11), l22, l33.  simpl. rewrite H10 in H3. assumption.
Qed.

(* if maximum of two numbers m, n >= s then either m >= s or
   n >= s *)
Lemma z_max_lb : forall m n s, Z.max m n >= s <-> m >= s \/ n >= s.
Proof.
  split; intros. unfold Z.max in H. destruct (m ?= n) eqn : Ht.
  left. auto. right. auto. left. auto.
  destruct H. unfold Z.max. destruct (m ?= n) eqn: Ht.
  auto. pose proof (proj1 (Z.compare_lt_iff _ _) Ht). omega. omega.
  unfold Z.max. destruct (m ?= n) eqn:Ht.
  pose proof (proj1 (Z.compare_eq_iff _ _) Ht). omega.
  omega. pose proof (proj1 (Z.compare_gt_iff _ _) Ht). omega.
Qed.

(* if length of list l is > n then there is a natural number
   p such that p + n = length of list l *)
Lemma list_and_num : forall (A : Type) (n : nat) (l : list A),
    (length l > n)%nat -> exists p, (length l = p + n)%nat.
Proof.
  intros A n l H. induction l. inversion H.
  simpl in *. apply gt_S in H. destruct H. specialize (IHl H). destruct IHl as [p IHl].
  exists (S p). omega. exists 1%nat. omega.
Qed.

(* if forallb f l returns false then existance of element x in list l
   such that f x = false, and if x is in list l and f x = false then
   forallb f l will evaluate to false *)
Lemma forallb_false : forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false <-> (exists x, In x l /\ f x = false).
Proof.
  intros A f l. split. intros H. induction l. simpl in H. inversion H.
  simpl in H. apply andb_false_iff in H. destruct H.
  exists a. split. simpl. left. auto. assumption.
  pose proof IHl H. destruct H0. exists x. destruct  H0 as [H1 H2].
  split. simpl. right. assumption. assumption.
  intros. destruct H as [x [H1 H2]]. induction l. inversion H1.
  simpl. apply andb_false_iff. simpl in H1. destruct H1.
  left. congruence. right. apply IHl. assumption.
Qed.


  
(*  Shows the type level existence of element x in list l >=  s if maximum element of
   list l >= s *)
Lemma max_of_nonempty_list_type :
  forall (A : Type) (l : list A) (H : l <> nil) (H1 : forall x y : A, {x = y} + {x <> y})
    (s : Z) (f : A -> Z), maxlist (map f l) >= s -> existsT (x:A), In x l /\ f x >= s.
Proof.
  intros A.
  assert (Hm : forall (a b : A) (l : list A) (f : A -> Z),
             maxlist (f a :: map f (b :: l)) = Z.max (f a) (maxlist (map f (b :: l)))) by auto.
  refine (fix F l {struct l} :=
            fun H H1 s f => 
              match l as l0 return (l = l0 -> l0 <> [] ->
                                    maxlist (map f l0) >= s ->
                                    existsT (x : A), In x l0 /\ f x >= s) with
              | [] => fun _ H =>  match H eq_refl with end
              | h :: t =>
                fun Heq Hn =>
                  match t as t0 return (t = t0 -> (h :: t0) <> [] ->
                                        maxlist (map f (h :: t0)) >= s ->
                                        existsT (x : A), In x (h :: t0) /\ f x >= s) with
                  | [] => fun _ H1 H2 => existT _ h (conj (in_eq h []) H2)
                  | h1 :: t1 =>
                    let Hmax := (Z_ge_lt_dec (f h) (maxlist (map f (h1 :: t1)))) in
                    match Hmax with
                    | left e => fun H1 H2 H3 => _
                    | right r => fun H1 H2 H3 => _
                    end 
                  end eq_refl Hn
            end eq_refl H).
  
  rewrite map_cons in H3. rewrite Hm in H3.
  apply Z.ge_le in e. pose proof (Z.max_l _ _ e) as Hmx.
  rewrite Hmx in H3.
  exists h. intuition.

  
  rewrite map_cons in H3. rewrite Hm in H3.
  pose proof (max_two_integer _ _ r) as Hmx.
  rewrite Hmx in H3.
  assert (Ht : [] <> h1 :: t1) by apply nil_cons.
  apply not_eq_sym in Ht. 
  rewrite <- H1 in H2, H3, Hmx, Ht.
  specialize (F _ Ht H4 s f H3).
  destruct F as [x [Fin Fx]]. rewrite <- H1. 
  exists x. intuition.
Defined.   
   
 

(* if forallb f l returns false then type level existance of element x in list l
   such that f x = false *)
Lemma forallb_false_type : forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = false -> existsT x, In x l /\ f x = false.
Proof. 
  refine (fun A f =>
            fix F l :=
            match l as l0 return (forallb f l0 = false ->
                                  existsT x, In x l0 /\ f x = false) with
            | [] => fun H => match (diff_true_false H) with end
            | h :: t =>
              fun H => match f h as v return (f h = v -> existsT x, In x (h :: t) /\ f x = false) with
                    | false => fun H1 => existT _ h (conj (in_eq h t) H1)
                    | true => fun H1 => _
                    end eq_refl                             
            end).
 
  simpl in H. rewrite H1 in H. simpl in H. pose proof (F t H) as Ft.
  destruct Ft as [x [Fin Fx]]. exists x. intuition.
Defined.

Lemma filter_empty : forall (A : Type) (l : list A) (f : A -> bool),
    filter f l = [] <->
    (forall x, In x l -> f x = false).
Proof.
  intros A. induction l.
  split; intros. inversion H0. reflexivity.
  split; intros. destruct H0. simpl in H.
  destruct (f a) eqn : Ht. inversion H.
  rewrite <- H0. assumption.
  simpl in H. destruct (f a). inversion H.
  pose proof (proj1 (IHl f) H x H0). assumption.
  simpl. destruct (f a) eqn: Ht.
  pose proof (H a (in_eq a l)). congruence.
  pose proof (IHl f). destruct H0.
  apply H1. intros. firstorder.
Qed.

Lemma complementary_filter_perm A (p: A -> bool) (l: list A):
  Permutation l (filter p l ++ filter (compose negb p) l).
Proof with auto.
  induction l...
  simpl.
  unfold compose.
  destruct (p a); simpl...
  apply Permutation_cons_app...
Qed.

Lemma complementary_filter_In : forall
    (A : Type) (l : list A) (f : A -> bool) (g : A -> bool)
    (H : forall x, In x l -> f x = negb (g x)),
    Permutation l (filter f l ++ filter g l).
Proof with auto.
  intros A l f g H.
  induction l...
  simpl.
  destruct (f a) eqn : Ht; simpl...
  pose proof (H a (in_eq a l)).
  rewrite Ht in H0.
  symmetry in H0.
  apply negb_true_iff in H0.
  rewrite H0. apply perm_skip. apply IHl.
  intros. apply H. simpl. right. auto.
  pose proof (H a (in_eq a l)).
  rewrite Ht in H0. symmetry in H0. apply negb_false_iff in H0.
  rewrite H0.
  apply Permutation_cons_app...
  apply IHl. intros.
  apply H. simpl. right. auto.
Qed.

(*
Lemma not_equal_elem : forall (A : Type) (a x : A) (l : list A),
    In a l -> ~ In x l -> x <> a.
Proof.
  intros A a x l H1 H2.
  induction l. inversion H1.
  specialize (proj1 (not_in_cons x a0 l) H2); intros.
  simpl in H1. destruct H as [H3 H4]. destruct H1.
  subst. assumption. apply IHl. assumption. assumption.
Qed. *)

Theorem transitive_dec_first :
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (x y z : A),
    {P x y -> P y z -> P x z} +
    {~(P x y -> P y z -> P x z)}. 
Proof.
  intros.
  destruct (Hp x y), (Hp y z), (Hp x z); intuition.
Qed.



Theorem transitive_dec_second :
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (x y: A) (l : list A),
    {forall z, In z l -> P x y -> P y z -> P x z} +
    {~(forall z, In z l -> P x y -> P y z -> P x z)}. 
Proof.
  intros.
  induction l.
  left; intuition.
  destruct IHl.
  pose proof (transitive_dec_first A Hcd P Hp x y a).
  destruct H.
  left. intros. destruct H. subst. auto.
  intuition.
  right. unfold not. intros. apply n. intros.
  intuition.
  pose proof (transitive_dec_first A Hcd P Hp x y a).
  destruct H.
  right. unfold not. intros. apply n.
  intuition.
  right. intuition.
Qed.
  
Theorem transitive_dec_third :
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (x : A) (l1 l2 : list A),
    {forall y z, In y l1 -> In z l2 -> P x y -> P y z -> P x z} +
    {~(forall y z, In y l1 -> In z l2 -> P x y -> P y z -> P x z)}.
Proof.
  intros.
  induction l1.
  left; intuition.

  destruct IHl1.  
  pose proof (transitive_dec_second A Hcd P Hp x a l2).
  destruct H.
  left. intros. destruct H.
  subst. intuition. apply p with y; intuition.
  right. unfold not. intros. apply n.  intros.
  apply H with a; intuition.
  pose proof (transitive_dec_second A Hcd P Hp x a l2).
  destruct H.
  right. unfold not. intros. apply n. intros. apply H with y; intuition.
  right. unfold not. intros. apply n. intros. apply H with y; intuition.
Qed.

Theorem transitive_dec_fourth :
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (l1 l2 l3 : list A),
    {forall x y z, In x l1 -> In y l2 -> In z l3 -> P x y -> P y z -> P x z} +
    {~(forall x y z, In x l1 -> In y l2 -> In z l3 -> P x y -> P y z -> P x z)}.
Proof.
  intros.
  induction l1.
  left; intuition.

  destruct IHl1.
  pose proof (transitive_dec_third A Hcd P Hp a l2 l3).
  destruct H.
  left. intros. destruct H. subst. apply p0 with y; intuition.
  apply p with y; intuition.
  right. unfold not. intros. apply n. intros.
  apply H with y; intuition.
  right. unfold not. intros. apply n. intros.
  apply H with y; intuition.
Qed.

Theorem transitive_dec:
  forall (A : Type) (Hcd : forall (c d : A), {c = d} + {c <> d})
         (P : A -> A -> Prop) (Hp : forall (c d : A), {P c d} + {~P c d}) (l : list A),
    {forall x y z, In x l -> In y l -> In z l -> P x y -> P y z -> P x z} +
    {~(forall x y z, In x l -> In y l -> In z l -> P x y -> P y z -> P x z)}.
Proof.
  intros. pose proof (transitive_dec_fourth A Hcd P Hp l l l). auto.
Qed.

(* End of List Lemma file *)

