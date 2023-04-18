From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import stlc_unscoped.
From Hammer Require Import Tactics Hammer.
From Coq Require Import micromega.Lia.

Require Import Coq.Program.Equality.

(* fin n is the set of variables *)
(* context is indexed by n, which indicates the number of free variables *)
Definition context := nat -> ty.

(* Statics *)
(* The index m tells us only 0..(m-1) in Γ matters *)
Inductive Typing (m : nat) (Γ : context) : tm -> ty -> Prop :=
| T_Var i : i < m -> Typing m Γ (var_tm i) (Γ i)
| T_Lam : forall A a B, Typing (S m) (A .: Γ) a B -> Typing m Γ (lam a) (TPi A B)
| T_App : forall a A B b, Typing m Γ a (TPi A B) -> Typing m Γ b A -> Typing m Γ (app a b) B
| T_Unit : Typing m Γ unit TUnit.

#[export]Hint Constructors Typing : core.

Lemma renaming
  (n : nat) (Γ : context) (a : tm)
  (A : ty) (h : Typing n Γ a A)   :
  forall (m : nat) (ξ : nat -> nat) (Δ : context),
  (forall i, i < n -> Γ i = Δ (ξ i) /\ ξ i < m) ->
  (* ---------------------------------------- *)
  Typing m Δ (ren_tm ξ a) A .
Proof.
  elim : n Γ a A / h.
  - hauto lq:on inv:Typing ctrs:Typing.
  - move => m Γ A a B h_body ih n ξ Δ hΔ /=.
    constructor.
    apply ih.
    move => x hx.
    split.
    + hauto l:on inv:nat.
    + case : x hx => [| x] hx; first sfirstorder.
      asimpl.
      suff : x < m by sfirstorder.
      sfirstorder.
  - hauto lq:on rew:off ctrs:Typing.
  - sfirstorder.
Qed.

Lemma morphing
  (n : nat) (Γ : context) (a : tm) (A : ty)
  (h : Typing n Γ a A) :
  forall m (ξ : fin -> tm) (Δ : context),
  (forall i, i < n -> Typing m Δ (ξ i) (Γ i)) ->
  (* ---------------------------------------- *)
  (Typing m Δ (subst_tm ξ a)  A).
Proof.
  elim : n Γ a A / h.
  - sfirstorder.
  - move => n Γ A a B h_body ih m ξ Δ hΔ /=.
    asimpl.
    constructor.
    apply ih.
    case => *.
    + hauto lq:on inv:-  ctrs:Typing solve:lia.
    + asimpl.
      hauto lq:on use:renaming unfold:shift solve:lia.
  - hauto lq:on ctrs:Typing.
  - sfirstorder.
Qed.

Lemma subst_one
  (n : nat) (Γ : fin -> ty) (a : tm)
  (b : tm) (A B : ty) :
  Typing (S n) (A .: Γ) a B ->
  Typing n Γ b A ->
  (* ------------------------------------ *)
  Typing n Γ (subst_tm (scons b ids) a) B.
Proof.
  move => h0 h1.
  apply morphing with (Γ := A .: Γ) (n := S n); auto.
  case => *.
  - by asimpl.
  - asimpl.
    hauto lq:on ctrs:Typing solve:lia.
Qed.

Reserved Notation "a '⤳' b" (at level 80).
Inductive Red : tm  -> tm  -> Prop :=
| R_AppAbs (a : tm) (b : tm) :
  Red (app (lam a) b) (subst_tm (scons b ids) a)
| R_App (a a' b : tm) :
  Red a a' ->
  Red (app a b) (app a' b)
where "a '⤳' b" := (Red a b).

Lemma preservation (a a' : tm) (h : Red a a') :
  forall n Γ A, Typing n Γ a A -> Typing n Γ a' A.
  elim : a a' / h.
  - hauto lq:on use:subst_one inv:Typing.
  - hauto l:on inv:Typing.
Qed.

Definition is_value (m : tm) : bool :=
  match m with
  | unit => true
  | lam _ => true
  | _ => false
  end.

Lemma empty_lam_pi_inv : forall (a : tm) (Γ : context) (A B : ty),
    Typing 0 Γ a (TPi A B) ->
    is_value a ->
    exists a0, a = lam a0.
Proof.
  hauto q:on inv:Typing solve:lia.
Qed.

Lemma progress (a : tm) (A  :ty) (Γ : context) (h : Typing 0 Γ a A) :
  is_value a \/ exists a', a ⤳ a'.
Proof.
  move : h.
  move eq0 : 0 => zero h.
  move : eq0.
  elim : zero Γ a A / h.
  - lia.
  - sfirstorder.
  - hauto ctrs:Red l:on use:empty_lam_pi_inv.
  - sfirstorder.
Qed.
