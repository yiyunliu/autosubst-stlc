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


Definition fin_to_nat (n : nat) (x : fin n) : nat.
  induction n.
  - inversion x.
  - destruct x.
    exact (1 + IHn f).
    exact 0.
Defined.

Definition fin2 : fin 4 := (Some (Some None)).
Definition fin3 : fin 4 := (Some (Some (Some None))).

Compute fin_to_nat fin2.
Compute fin_to_nat fin3.

Definition dependent_context (n : nat) := forall x:fin n, tm (n - 1 - fin_to_nat x).
