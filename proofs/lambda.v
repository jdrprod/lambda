Require Import List Nat Arith Arith.EqNat Program.Equality.
Import ListNotations.

Inductive term :=
  | Var : nat -> term
  | App : term -> term -> term
  | Lam : nat -> term -> term.

Fixpoint vars (t : term) : list nat :=
  match t with
  | Var n   => [n]
  | App x y => vars x ++ vars y
  | Lam x t => x::vars t
  end.

Fixpoint free_vars (t : term) : list nat :=
  match t with
  | Var n => [n]
  | App t1 t2 => free_vars t1 ++ free_vars t2
  | Lam x t => remove Nat.eq_dec x (free_vars t)
  end.

Fixpoint α_rename (n : nat) (m : nat) (t : term) :=
  match t with
  | Var n'  => if n =? n' then Var m else Var n'
  | App x y => App (α_rename n m x) (α_rename n m y)
  | Lam x t =>
    if x =? n then Lam m (α_rename n m t)
    else Lam x (α_rename n m t)
  end.

Inductive α_eq : term -> term -> Prop :=
  | α_congr   : forall t u t' u',
    α_eq t t' -> α_eq u u' -> α_eq (App t u) (App t' u')
    
  | α_abs     : forall x t t',
    α_eq t t' -> α_eq (Lam x t) (Lam x t')
    
  | α_alpha  : forall x y t,
    ~(In y (vars t)) ->
    α_eq (Lam x t) (Lam y (α_rename x y t))
  
  | α_refl    : forall t,
    α_eq t t
  
  | α_trans   : forall t1 t2 t3,
    α_eq t1 t2 -> α_eq t2 t3 -> α_eq t1 t3

  | α_symm    : forall t u,
    α_eq t u -> α_eq u t.

Infix "===α" := α_eq (at level 80).


Lemma eqb_refl:
  forall n, n =? n = true.
Proof.
  intros.
  rewrite Nat.eqb_eq.
  reflexivity.
Qed.


Search (~(_ \/ _) -> ~_ /\ ~_).

Lemma in_app_and:
  forall (x:nat) (l l' : list nat), ~ (In x (l ++ l')) -> (~In x l) /\ (~In x l').
Proof.
  intros.
  apply Decidable.not_or.
  rewrite in_app_iff in H.
  assumption.
Qed.

Lemma in_vars_aff:
  forall n x t,
  ~In n (vars t) -> n <> x -> ~In n (vars (Lam x t)).
Proof.
Admitted.

Theorem bound_not_free:
  forall x t,
  ~In x (free_vars (Lam x t)).
Proof.
  intros x t H.
  cbn in H.
  apply remove_In in H.
  contradiction.
Qed.


Theorem α_eq_α_rename:
  forall t x y,
  ~(In x (free_vars t)) ->
  ~(In y (free_vars t)) -> t ===α (α_rename x y t).
Proof.
  (* intros.
  induction t.
  - induction (Nat.eq_dec x n).
    + subst. cbn in H. elim H. left. reflexivity.
    + cbn. apply Nat.eqb_neq in b.
      replace (x =? n) with false.
      apply α_refl.
  - cbn. apply α_congr;
    cbn in H;
    apply in_app_and in H;
    inversion H.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - induction (Nat.eq_dec x n).
    + cbn. subst. rewrite eqb_refl.
      apply α_alpha.
      induction (In_dec Nat.eq_dec n (free_vars t)).
      ++  *)
Admitted.


Inductive A_eq : term -> term -> Prop :=
  | A_congr   : forall t u t' u',
    A_eq t t' -> A_eq u u' -> A_eq (App t u) (App t' u')
    
  | A_abs     : forall x t t',
    A_eq t t' -> A_eq (Lam x t) (Lam x t')
    
  | A_alpha  : forall x y t,
    ~(In y (vars t)) ->
    A_eq (Lam x t) (Lam y (α_rename x y t))
  
  | A_refl    : forall n,
    A_eq (Var n) (Var n)
  
  | A_trans   : forall t1 t2 t3,
    A_eq t1 t2 -> A_eq t2 t3 -> A_eq t1 t3

  | A_symm    : forall t u,
    A_eq t u -> A_eq u t.

Infix "===A" := A_eq (at level 80).




Theorem A_eq_α_eq:
  forall t1 t2, 
  A_eq t1 t2 <-> α_eq t1 t2.
Proof.
  intros; split.
  - intro.
    induction H; subst.
    + apply (α_congr _ _ _ _ IHA_eq1 IHA_eq2).
    + apply (α_abs _ _ _ IHA_eq).
    + apply (α_alpha _ _ _ H).
    + apply α_refl.
    + apply (α_trans _ _ _ IHA_eq1 IHA_eq2).
    + apply (α_symm _ _ IHA_eq).
  - intro.
    dependent induction H; subst.
    + apply (A_congr _ _ _ _ IHα_eq1 IHα_eq2).
    + apply (A_abs _ _ _ IHα_eq).
    + apply (A_alpha _ _ _ H).
    + induction t.
      -- apply A_refl.
      -- apply (A_congr _ _ _ _ IHt1 IHt2).
      -- apply (A_abs _ _ _ IHt).
    + apply (A_trans _ _ _ IHα_eq1 IHα_eq2).
    + apply (A_symm _ _ IHα_eq).
Qed.

Example id0_α_eq_id1 :
  Lam 0 (Var 0) ===α Lam 1 (Var 1).
Proof.
  apply α_alpha.
  intros [].
  - discriminate H.
  - contradiction H.
Qed.

Lemma helper_1:
  forall n t,
  Var n ===A t -> exists m, t = Var m.
Proof.
  intros.
  dependent induction H.
  - exists n. reflexivity.
  - inversion H; subst.
    * eelim IHA_eq1 with (n0 := n). intros.
      apply IHA_eq2 with (n0 := x).
      assumption.
      reflexivity.
    * eelim IHA_eq1 with (n0 := n). intros.
      apply IHA_eq2 with (n := x).
      assumption.
      reflexivity.
    * eelim IHA_eq1 with (n0 := n). intros.
      apply IHA_eq2 with (n := x).
      assumption.
      reflexivity.
  - inversion H; subst.
    * exists n. reflexivity.
Admitted.

Lemma α_α_rename:
  forall t x y,
    ~(In x (free_vars t)) ->
    ~(In x (free_vars t)) ->
    t ===A α_rename x y t.
Proof.
  intros.
  induction t; simpl.
  + destruct (x =? n) eqn:E.
    apply A_refl.
  
  induction (Nat.eq_dec x n).
    - cbn. subst. rewrite eqb_refl.
      apply A_alpha. 


Lemma useless_rename:
  forall x t, 
  α_rename x x t = t.
Proof.
  intros.
  induction t.
  + cbn. elim (Nat.eq_dec x n); intros.
    * subst. rewrite eqb_refl. reflexivity.
    * apply Nat.eqb_neq in b.
      replace (x =? n) with false.
      reflexivity.
  + cbn. rewrite IHt1, IHt2.
    reflexivity.
  + cbn. elim (Nat.eq_dec x n); intros.
    * subst. rewrite IHt.
      rewrite eqb_refl. reflexivity.
    * apply Nat.eqb_neq in b.
      rewrite Nat.eqb_sym in b.
      replace (n =? x) with false.
      rewrite IHt.
      reflexivity.
Qed.

Lemma alpha_sub_rename:
  forall x y t t',
  t ===A t' ->
  α_rename x y t ===A α_rename x y t'.
Proof.
  intros.
  dependent induction t'.
  + cbn. elim (Nat.eq_dec x n); intros.
    * subst. rewrite eqb_refl.
      eapply A_trans.
      **


Admitted.


Lemma alpha_renaming:
  forall t1 t2 x2 y2,
  t1 ===A t2 <-> t1 ===A (α_rename x2 y2 t2).
Proof.
  intros. split. intros.
  + dependent induction H.
    - cbn. apply A_congr; assumption.
    - cbn. elim (Nat.eq_dec x x2). intros.
      * subst. rewrite eqb_refl.
        elim (Nat.eq_dec x2 y2); intros.
        ** subst. rewrite useless_rename.
            apply A_abs. assumption.
        ** apply A_alpha.



Example not_α_eq_exp :
  Lam 0 (Var 0) ===A Lam 1 (Var 0) -> False.
Proof.
  intro H.

  
  dependent induction H.
  - apply IHA_eq2; try reflexivity.
    exfalso.
    dependent induction H; subst.
    *

  inversion H; subst; try discriminate.
  + apply



  dependent induction H.
  - 
  
  apply IHα_eq1.
    reflexivity.
    inversion H0.
    + reflexivity.
    + subst.



  

