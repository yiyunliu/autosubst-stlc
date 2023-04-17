From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import stlc.
From Hammer Require Import Tactics Hammer.

Definition context (n : nat) := fin n -> ty.

Reserved Notation "Gamma ⊢ a : A" (at level 80, a at level 99).

Inductive typing {m : nat} (Γ : context m) : tm m -> ty -> Prop :=
| T_Var i : Γ ⊢ var_tm i : Γ i
| T_Lam : forall A a B, A .: Γ ⊢ a : B -> Γ ⊢ lam a : TPi A B
| T_App : forall a A B b, Γ ⊢ a : TPi A B -> Γ ⊢ b : A -> Γ ⊢ app a b : B
| T_Unit : Γ ⊢ unit : TUnit
where "Γ ⊢ a : A" := (typing Γ a A).

#[export]Hint Constructors typing : core.

(* Weakening in Locally-nameless *)
Lemma renaming
  (n : nat) (Γ : context n) (a : tm n)
  (A : ty) (h : Γ ⊢ a : A)   :
  forall (m : nat) (ξ : fin n -> fin m) (Δ : context m),
  (forall i, Γ i = Δ (ξ i)) ->
  (* ---------------------------------------- *)
  Δ ⊢ (ren_tm ξ a) : A .
Proof.
  elim : n Γ a A / h;
    hauto q:on inv:option,typing ctrs:typing.
Qed.

(* Substitution in Locally-nameless *)
Lemma morphing
  (n : nat) (Γ : context n) (a : tm n) (A : ty)
  (h : Γ ⊢ a : A) :
  forall m (ξ : fin n -> tm m) (Δ : context m),
  (forall i, Δ ⊢ ξ i : Γ i) ->
  (* ---------------------------------------- *)
  (Δ ⊢ subst_tm ξ a : A).
Proof.
  elim : n Γ a A / h;
    hauto drew:off inv:option,typing ctrs:typing use:renaming.
Qed.

(* Specialized substitution with nil in Locally-nameless *)
Lemma subst_one
  (n : nat) (Γ : fin n -> ty) (a : tm (S n))
  (b : tm n) (A B : ty) :
  A .: Γ ⊢ a : B ->
  Γ ⊢ b : A ->
  (* ------------------------------------ *)
  Γ ⊢ (subst_tm (scons b ids)) a : B.
Proof.
  hauto q:on inv:option,typing ctrs:typing use:morphing.
Qed.

Reserved Notation "a '⤳' b" (at level 80).
Inductive pstep :
