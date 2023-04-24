From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import stlc.
From Hammer Require Import Tactics Hammer.
Require Import Coq.Program.Equality.


(* fin n is the set of variables *)
(* context is indexed by n, which indicates the number of free variables *)
Definition context (n : nat) := fin n -> ty.

Reserved Notation "Gamma ⊢ a : A" (at level 80, a at level 99).

(* Statics *)
Inductive typing {m : nat} (Γ : context m) : tm m -> ty -> Prop :=
| T_Var i : Γ ⊢ var_tm i : Γ i
| T_Lam : forall A a B, A .: Γ ⊢ a : B -> Γ ⊢ lam a : TPi A B
| T_App : forall a A B b, Γ ⊢ a : TPi A B -> Γ ⊢ b : A -> Γ ⊢ app a b : B
| T_Unit : Γ ⊢ unit : TUnit
where "Γ ⊢ a : A" := (typing Γ a A).

#[export]Hint Constructors typing : core.

(* Structural rules *)

(* Weakening in Locally-nameless *)
Lemma renaming
  (n : nat) (Γ : context n) (a : tm n)
  (A : ty) (h : Γ ⊢ a : A)   :
  forall (m : nat) (ξ : fin n -> fin m) (Δ : context m),
  (forall i, Γ i = Δ (ξ i)) ->
  (* ---------------------------------------- *)
  Δ ⊢ (ren_tm ξ a) : A .
Proof.
  (* An easy proof with sauto *)
  elim : n Γ a A / h;
    hauto q:on inv:option,typing ctrs:typing.

  (* Let's try again with manual proofs *)
  Restart.
  elim : n Γ a A / h.
  - move => n Γ x m ξ Δ hΔ /=.
    by rewrite hΔ.
  - move => m Γ A a B h_body ih x ξ Δ hΔ /=.
    apply T_Lam.
    apply ih.
    (* Show that the extended ξ is still a proper renaming *)
    destruct i.
    (* Some is just Succ *)
    + rewrite /upRen_tm_tm.  (* Some unnecessary unfolding to see what's going on *)
      rewrite /up_ren.
      rewrite /shift.
      vm_compute.
      by apply hΔ.
    + by vm_compute.
  - move => *.
    asimpl.
    apply : T_App; eauto.
  - simpl; auto.
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

  Restart.
  elim : n Γ a A / h.
  - move => n Γ x m ξ Δ hΔ /=.
    (* this is surprisingly reminiscent of a logical relation proof *)
    (* the var case triviall holds because of the assumption baked in *)
    by firstorder.
  - move => n Γ A a B h_body ih m ξ Δ hΔ /=.
    apply T_Lam.
    apply ih.
    move => x.
    destruct x.
    + simpl.
      (* >> must be forward composition *)
      (* I think it's probably opaque, but hammer went through because it doesn't care *)
      asimpl.
      (* uparrow/shift can be viewed as weakening on expressions *)
      (* we know that ξ f is well-typed under Δ  *)
      (* Let's do one step of weakening to fix it up *)
      apply renaming with (Γ := Δ).
      firstorder.
      (* The proof obligation just wants us to ensure that the
      variables are mapped to the same type under the new context *)
      by vm_compute.
    + simpl.
      apply T_Var.
  (* Trivial cases that follow from ih *)
  - move => * /=.
    econstructor; eauto.
  - move => * /=.
    econstructor.
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

  Restart.

  move => h0 h1.
  apply morphing with (Γ := A .: Γ).
  - assumption.
  (* Define the morphing function *)
  - destruct i.
    (* Map var > 0 to themself; trivial proof obligation *)
    + simpl.
      apply T_Var.
    (* Map 0 to b; immediate from the context *)
    + simpl.
      assumption.
Qed.

(* Dynamics *)

Reserved Notation "a '⤳' b" (at level 80).
Inductive Red {n : nat} : tm n -> tm n -> Prop :=
| R_AppAbs (a : tm (S n)) (b : tm n) :
  Red (app (lam a) b) (subst_tm (scons b ids) a)
| R_App (a a' b : tm n) :
  Red a a' ->
  Red (app a b) (app a' b)
where "a '⤳' b" := (Red a b).

Definition is_value {n : nat} (m : tm n) : bool :=
  match m with
  | unit => true
  | lam _ => true
  | _ => false
  end.

(* Type soundness *)

Lemma preservation (n : nat) (a a' : tm n) (h : a ⤳ a') :
  forall Γ A, Γ ⊢ a : A -> Γ ⊢ a' : A.
  (* why cannot I pass in n here? *)
  (* because the S n dependency? *)
  elim : a a' / h;
    [hauto l:on inv:typing use:subst_one
    | hauto lq:on rew:off inv:typing ctrs:typing].
Qed.


Lemma empty_lam_pi_inv : forall (a : tm 0) (A B : ty),
    null ⊢ a : TPi A B ->
    is_value a ->
    exists a0, a = lam a0.
Proof.
  hauto q:on inv:typing.
Qed.

(* Progress *)
Lemma progress (a : tm 0) (A  :ty) (h : null ⊢ a : A) :
  is_value a \/ exists a', a ⤳ a'.
Proof.
  dependent induction h.
  - by [].
  - sfirstorder.
  - hauto inv:- ctrs:Red l:on use:empty_lam_pi_inv.
  - sfirstorder.
Qed.

Inductive step {n : nat} : tm n -> tm n -> Prop :=
| S_AppAbs (a : tm (S n)) (b : tm n) :
  step (app (lam a) b) (subst_tm (scons b ids) a)
| S_App0 (a a' b : tm n) :
  step a a' ->
  step (app a b) (app a' b)
| S_App1 (a b b' : tm n) :
  step b b' ->
  step (app a b) (app a b').

Definition rstep {n : nat} (a b : tm n) := step b a.

Definition sn {n : nat} := Acc (@rstep n).

(* SNe is equivalent to the definition of Base *)
Inductive SNe {n : nat} : tm n -> Prop :=
| SNe_Var x :
  (* ------------- *)
  SNe (var_tm x)

| SNe_Unit :
(* ------------ *)
  SNe unit

| SNe_App a b :
  SNe a ->
  SN b ->
  (* -------------- *)
  SNe (app a b)

with SN {n : nat} : tm n -> Prop :=
| SN_Lam a0 :
  SN a0 ->
(* ------------------ *)
  SN (lam a0)

| SN_BaseIncl a :
  SNe a ->
(* -------- *)
  SN a

| SN_BackExp a b :
  SN_Red a b ->
  SN b ->
(* ------- *)
  SN a

with SN_Red {n : nat} : tm n -> tm n -> Prop :=
| SNR_AppAbs a b:
  SN b ->
  (* --- *)
  SN_Red (app (lam a) b) (subst_tm (b..) a)

| SNR_App a a' b :
  SN_Red a a' ->
  (* --------- *)
  SN_Red (app a b) (app a' b).

Scheme SNe_ind' := Induction for SNe Sort Prop
  with SN_ind' := Induction for SN Sort Prop
  with SN_Red_ind' := Induction for SN_Red Sort Prop.

Combined Scheme sn_mutual from SNe_ind', SN_ind', SN_Red_ind'.

#[export]Hint Constructors SNe SN SN_Red : core.

Check sn_mutual.

Inductive sn_Red {n : nat} : tm n -> tm n -> Prop :=
| snR_AppAbs a b:
  sn b ->
  (* --- *)
  sn_Red (app (lam a) b) (subst_tm (b..) a)

| snR_App a a' b :
  sn_Red a a' ->
  (* --------- *)
  sn_Red (app a b) (app a' b).

Lemma SN_sound_mutual :
  forall n,
  (forall (a : tm n), SNe a -> sn a) /\
  (forall (a : tm n), SN a -> sn a) /\
  (forall (a b : tm n), SN_Red a b -> sn_Red a b).
Proof.
  apply sn_mutual; eauto.
  - hauto q:on inv:step ctrs:Acc.
  - hauto q:on inv:step ctrs:Acc.
  - admit.
  - hauto q:on inv:step ctrs:Acc.
  - admit.
  - hauto l:on inv:step ctrs:Acc.
  - hauto l:on inv:step ctrs:Acc.
Admitted.


(* Semantic arrow *)
Definition SArr {n : nat} (A B : tm n -> Prop) (F : tm n) :=
  forall a, A a -> B (app F a).

Fixpoint Denote {n : nat} (T : ty) : tm n -> Prop :=
  match T with
  | TUnit => SN
  | TPi A B => SArr (Denote A) (Denote B)
  end.

Fixpoint Base {n : nat} (a : tm n) :=
  match a with
  | var_tm x => True
  | app a1 a2 => Base a1 /\ sn a2
  | lam a => False
  | unit => True
  end.

(* Lemma Base_0_impossible : *)
(*   forall (a : tm 0), ~ Base a. *)
(* Proof. *)
(*   dependent induction a; sfirstorder. *)
(* Qed. *)

Definition SAT {n : nat} (A : tm n -> Prop) :=

    (forall a, A a -> sn a) /\  (* subset condition *)
    (forall a, Base a -> A a) /\ (* 4.3.2.1(a) *)
      (forall a b, sn_Red a b -> A b -> A a) (* 4.3.2.1(b) *).

(* Prove that Base a -> a will never reduce to a lambda? *)
(* Lemma Base_is_SN {n : nat} (a : tm n) : *)
(*   Base a -> *)
(*   (* ----- *) *)
(*   SN a. *)
(* Proof. *)
(*   elim:n/a. *)
(*   - sfirstorder. *)
(*   - sfirstorder. *)
(*   - (* t will never be a lambda *) *)
(*   - sfirstorder. *)


#[export]Hint Unfold SAT : core.
(* Lemma 4.3.3.1 *)
Lemma SN_is_SAT {n : nat} : @SAT n sn.
Proof.
  rewrite /SAT; eauto.
  split; auto.
  split.
  move => a.
  elim : n / a.
  - hauto q:on inv:step ctrs:Acc.
  - sfirstorder.
  - cbn.
    move => n a ih0 b ih1 [ha hb].
    (* Base a /\ sn b should imply that (app a b) is normalizing *)
    have : Base (app a b) by sfirstorder.

Qed.

Lemma SArr_SAT {n : nat} (A B : tm n -> Prop) :
  SAT A -> SAT B -> SAT (SArr A B).
Proof.
  rewrite/ SAT.
  move => [h00 [h01 h02]] [h10 [h11 h12]].
  split.
  - rewrite /SArr.
    move => a.
    move /(_ unit ltac:(sfirstorder)).
    move /h10.
    move => h0.
    admit.
  - split.
    + dependent induction a; sfirstorder.
    + sfirstorder.
Admitted.

Lemma Denote_SAT {n : nat} (T : ty) : @SAT n (Denote T).
Proof.
  move : n.
  elim : T.
  - move => /= n.
    apply : SN_is_SAT.
  - move => /= T h0 T1 h1 n.
    hauto l:on use:SArr_SAT.
Qed.
