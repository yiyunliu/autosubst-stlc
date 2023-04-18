From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import coc_unscoped.
From Hammer Require Import Tactics Hammer.
From Coq Require Import micromega.Lia.

Require Import Coq.Program.Equality.

(* fin n is the set of variables *)
(* context is indexed by n, which indicates the number of free variables *)
Definition context := nat -> tm.

Definition shift_p (p : nat) (x : fin) : fin := p + x.

Definition dep_ith (Γ : context) (x : fin) :=
  ren_tm (shift_p (S x)) (Γ x).

Lemma dep_ith_ren_tm (Γ : context) (A : tm) (x : fin) :
  dep_ith (A .: Γ) (S x) = ren_tm shift (dep_ith Γ x).
Proof.
  case : x => [|x].
  - rewrite /dep_ith; asimpl.
    reflexivity.
  - rewrite /dep_ith.
    asimpl.
    f_equal.
Qed.
(* Statics *)
(* The index m tells us only 0..(m-1) in Γ matters *)
Inductive Typing (m : nat) (Γ : context) : tm -> tm -> Prop :=
| T_Var i :
  i < m ->
    (* ------------------------------- *)
    Typing m Γ (var_tm i) (dep_ith Γ i)

| T_Axiom :
    (* ---------------------------- *)
    Typing m Γ (type TYPE) (type KIND)

| T_Pi : forall A B s1 s2,
    Typing m Γ A (type s1) ->
    Typing (S m) (A .: Γ) B (type s2) ->
    (* ------------------------------- *)
    Typing m Γ (pi A B) (type s2)

| T_Lam : forall A a B s,
    Typing (S m) (A .: Γ) a B ->
    Typing m Γ (pi A B) (type s) ->
    (* -------------------------- *)
    Typing m Γ (lam a) (pi A B)

| T_App : forall a A B b,
    Typing m Γ a (pi A B) ->
    Typing m Γ b A ->
    (* ----------------------------- *)
    Typing m Γ (app a b) (subst_tm (scons b ids) B).

#[export]Hint Constructors Typing : core.

Lemma renaming
  (n : nat) (Γ : context) (a : tm)
  (A : tm) (h : Typing n Γ a A)   :
  forall (m : nat) (ξ : nat -> nat) (Δ : context),
  (forall i, i < n -> ren_tm ξ (dep_ith Γ i) = dep_ith Δ (ξ i) /\ ξ i < m) ->
  (* ---------------------------------------- *)
  Typing m Δ (ren_tm ξ a) (ren_tm ξ A) .
Proof.
  elim : n Γ a A / h.
  - hauto lq:on inv:Typing ctrs:Typing.
  - sfirstorder.
  - move => m Γ A B s1 s2 h0 ih0 h1 ih1 x ξ Δ hΔ /=.
    apply T_Pi with (s1 := s1); eauto.
    apply ih1.
    case => [| i /Arith_prebase.lt_S_n] ?.
    + split.
      rewrite /dep_ith; asimpl; reflexivity.
      move => /=; lia.
    + asimpl; split; last sfirstorder.
      repeat rewrite dep_ith_ren_tm.
      case /(_ i ltac:(assumption)) : hΔ => hΔ1 hΔ2.
      rewrite -hΔ1.
      by asimpl.
  - move => m Γ A a B s h0 ih0 h1 ih1 n ξ Δ hΔ /=.
    asimpl.
    apply T_Lam with (s := s); eauto.
    apply : {ih1} ih0.
    case => [| i /Arith_prebase.lt_S_n] ?.
    + split.
      rewrite /dep_ith; asimpl; reflexivity.
      move => /=; lia.
    + asimpl; split; last sfirstorder.
      repeat rewrite dep_ith_ren_tm.
      case /(_ i ltac:(assumption)) : hΔ => hΔ1 hΔ2.
      rewrite -hΔ1.
      by asimpl.
  - move => n Γ a A B b h0 ih0 h1 ih1 m ξ Δ hΔ.
    replace (ren_tm ξ (app a b)) with
      (app (ren_tm ξ a) (ren_tm ξ b));
      last by asimpl.
    replace (ren_tm ξ (subst_tm (scons b ids) B)) with
      ( (subst_tm (scons (ren_tm ξ b) ids) (ren_tm (upRen_tm_tm ξ) B)));
      last by asimpl.
    apply T_App with (A := ren_tm ξ A); eauto.
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
