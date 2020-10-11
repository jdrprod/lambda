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

Inductive A_eq : term -> term -> Prop :=
  | A_congr   : forall t u t' u',
    A_eq t t' -> A_eq u u' -> A_eq (App t u) (App t' u')
    
  | A_abs     : forall x t t',
    A_eq t t' -> A_eq (Lam x t) (Lam x t')
    
  | A_alpha  : forall x y t,
    ~(In y (vars t)) ->
    A_eq (Lam x t) (Lam y (α_rename x y t))
  
  | A_refl    : forall t,
    A_eq t t
  
  | A_trans   : forall t1 t2 t3,
    A_eq t1 t2 -> A_eq t2 t3 -> A_eq t1 t3

  | A_symm    : forall t u,
    A_eq t u -> A_eq u t.

Infix "===α" := α_eq (at level 80).
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
  

Example not_α_eq_exp :
  Lam 0 (Var 0) ===A Lam 1 (Var 0) -> False.
Proof.
  intro H.
  inversion H; subst; try discriminate.
  + red in H. cbn in H.



  dependent induction H.
  - 
  
  apply IHα_eq1.
    reflexivity.
    inversion H0.
    + reflexivity.
    + subst.



  

