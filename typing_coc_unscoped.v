From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import coc_unscoped.
From Hammer Require Import Tactics Hammer.
From Coq Require Import micromega.Lia Relation_Operators Operators_Properties.

Require Import Coq.Program.Equality.

(* Dynamics *)
Reserved Notation "a '⤳' b" (at level 80).
Inductive Red : tm  -> tm  -> Prop :=
| R_AppAbs (a : tm) (b : tm) :
  Red (app (lam a) b) (subst_tm (scons b ids) a)
| R_App (a a' b : tm) :
  Red a a' ->
  Red (app a b) (app a' b)
where "a '⤳' b" := (Red a b).

Definition is_value (m : tm) : bool :=
  match m with
  | lam _ => true
  | type _ => true
  | pi _ _ => true
  | _ => false
  end.

Reserved Notation "a '≡' b" (at level 70).
Inductive DefEq : tm -> tm -> Prop :=
| E_Var x :
  (* -- *)
  var_tm x ≡ var_tm x

| E_Sym a b :
  a ≡ b ->
  (* ------- *)
  b ≡ a

| E_Trans a b c :
  a ≡ b ->
  b ≡ c ->
  (* ---- *)
  a ≡ c

| E_App a0 a1 b0 b1 :
  a0 ≡ a1 ->
  b0 ≡ b1 ->
  (* --------- *)
  app a0 b0 ≡ app a1 b1

| E_Abs a0 a1 :
  a0 ≡ a1 ->
  (* --------- *)
  lam a0 ≡ lam a1

| E_Pi a0 a1 b0 b1 :
  a0 ≡ b0 ->
  a1 ≡ b1 ->
  (* --------- *)
  pi a0 a1 ≡ pi b0 b1

| E_Type s  :
  (* --------- *)
  type s ≡ type s

| E_AppAbs a0 a1 b0 b1 c:
  (* makes ih easier to apply *)
  c = (subst_tm (b1..) a1) ->
  a0 ≡ lam a1 ->
  b0 ≡ b1 ->
  (* ------------------------------ *)
  app a0 b0 ≡ c

where "a '≡' b" := (DefEq a b).

#[export]Hint Constructors DefEq : core.

Lemma E_Refl a : a ≡ a.
Proof.
  induction a; auto. Qed.

#[export]Hint Resolve E_Refl : core.


Reserved Notation "a '⇒' b" (at level 70).
Inductive Par : tm -> tm -> Prop :=
| P_Var x :
  (* -- *)
  var_tm x ⇒ var_tm x

| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* --------- *)
  app a0 b0 ⇒ app a1 b1

| P_Abs a0 a1 :
  a0 ⇒ a1 ->
  (* --------- *)
  lam a0 ⇒ lam a1

| P_Pi a0 a1 b0 b1 :
  a0 ⇒ b0 ->
  a1 ⇒ b1 ->
  (* --------- *)
  pi a0 a1 ⇒ pi b0 b1

| P_Type s  :
  (* --------- *)
  type s ⇒ type s

| P_AppAbs a0 a1 b0 b1 c:
  (* makes ih easier to apply *)
  c = (subst_tm (b1..) a1) ->
  a0 ⇒ lam a1 ->
  b0 ⇒ b1 ->
  (* ------------------------------ *)
  app a0 b0 ⇒ c

where "a '⇒' b" := (Par a b).

#[export]Hint Constructors Par : core.

(* Statics *)
(* context is not indexed because we are using the unscoped version *)
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
    Typing m Γ (app a b) (subst_tm (scons b ids) B)

| T_Conv : forall a A B s,
    Typing m Γ a A ->
    Typing m Γ B (type s) ->
    A ≡ B ->
    (* -------------------- *)
    Typing m Γ a B.

#[export]Hint Constructors Typing : core.

Lemma defeq_renaming ξ A B (h : A ≡ B):
  ren_tm ξ A ≡ ren_tm ξ B.
  move : ξ.
  elim : A B / h; eauto 3.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => a0 a1 b0 b1 c h h0 ih0 h1 ih1 ξ /=.
    apply : E_AppAbs; eauto.
    rewrite h; by asimpl.
Qed.

Lemma defeq_subst ξ A B (h : A ≡ B):
  subst_tm ξ A ≡ subst_tm ξ B.
  move : ξ.
  elim : A B / h; eauto 3.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => *.
    apply : E_AppAbs; eauto.
    by subst; asimpl.
Qed.

Lemma par_renaming ξ A B (h : A ⇒ B):
  ren_tm ξ A ⇒ ren_tm ξ B.
  move : ξ.
  elim : A B / h; eauto 3.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - move => a0 a1 b0 b1 c h h0 ih0 h1 ih1 ξ /=.
    apply : P_AppAbs; eauto.
    rewrite h; by asimpl.
Qed.

Lemma par_morphing ξ0 ξ1 A B (h : A ⇒ B) :
  (forall i, ξ0 i ⇒ ξ1 i) ->
  subst_tm ξ0 A ⇒ subst_tm ξ1 B.
Proof.
  move : ξ0 ξ1.
  elim : A B / h => /= //; eauto 3.
  - sfirstorder.
  - move => ? ? ? ih0 * /=.
    constructor.
    apply ih0.
    hauto l:on inv:nat ctrs:Par use:par_renaming.
  - move => ? ? ? ? ? ? ? ih * /=.
    constructor; eauto.
    apply ih.
    hauto l:on inv:nat ctrs:Par use:par_renaming.
  - move => a0 a1 b0 b1 c ? h1 ih1 h2 ih2 ξ0 ξ1 hξ.
    move /(_ ξ0 ξ1 hξ) : ih1 => ih1.
    apply : P_AppAbs; eauto.
    by subst; asimpl.
Qed.

Lemma par_cong A B C D
  (h : A ⇒ B)
  (h0 : C ⇒ D) :
  (* ------------------ *)
  subst_tm (C..) A ⇒ subst_tm (D..) B.
Proof.
  apply par_morphing; sauto lq:on.
Qed.


Lemma par_confluence A B C
  (h : A ⇒ B)
  (h0 : A ⇒ C) :
  (* --------------- *)
  exists D, B ⇒ D /\ C ⇒ D.
Proof.
  move :  C h0.
  elim : A B  / h.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a0 a1 b0 b1 h0 ih0 h1 ih1 C h2.
    case E : (app a0 b0) C / h2; try congruence.
    (* App App *)
    + hauto lq:on inv:Par ctrs:Par.
    (* App Abs *)
    + hauto lq:on ctrs:Par inv:Par use:par_cong.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - hauto lq:on inv:Par ctrs:Par.
  - move => a0 a1 b0 b1 ? ? h0 ih0 h1 ih1 C h2; subst.
    case E : (app a0 b0) C / h2; try congruence.
    (* App Abs *)
    + hauto lq:on ctrs:Par inv:Par use:par_cong.
    (* Abs Abs *)
    + qauto l:on ctrs:Par inv:Par use:par_cong.
Qed.

Definition Multipar := clos_trans_1n _ Par.
#[export]Hint Unfold Multipar : core.
Notation "a '⇒*' b" := (Multipar a b) (at level 70).

Lemma multipar_trans A B C
  (h : A ⇒* B)
  (h0 : B ⇒* C) :
  (* ----------- *)
  A ⇒* C.
Proof. sauto lq:on use:clos_trans_t1n_iff. Qed.


Lemma multipar_par_confluence A B C
  (h : A ⇒* B)
  (h0 : A ⇒ C) :
  (* ---------- *)
  exists D, B ⇒* D /\ C ⇒* D.
Proof.
  move : C h0.
  elim : A B /h.
  - move=> x y H C h0.
    have [D ?] : exists D, y ⇒ D /\ C ⇒ D by sfirstorder use:par_confluence.
    hauto q:on ctrs:clos_trans_1n.
  - move=> x y z h h0 h1 C h2.
    have [D ?] : exists D, y ⇒ D /\ C ⇒ D by sfirstorder use:par_confluence.
    hauto lq:on ctrs:clos_trans_1n.
Qed.

Lemma multipar_confluence A B C
  (h : A ⇒* B)
  (h0 : A ⇒* C) :
  (* ---------- *)
  exists D, B ⇒* D /\ C ⇒* D.
Proof.
  move : C h0.
  elim : A B /h.
  - hauto lq:on use:multipar_par_confluence.
  - move=> x y z h h0 h1 C h2.
    have [D [*]] : exists D, y ⇒* D /\ C ⇒* D by hauto lq:on use:multipar_par_confluence.
    have [E [*]] : exists E, D ⇒* E /\ z ⇒* E by hauto lq:on use:multipar_par_confluence.
    sfirstorder use:multipar_trans.
Qed.

Definition Join A B := exists C, A ⇒* C /\ B ⇒* C.
Notation "a '⇔' b" := (Join a b) (at level 79).
#[export]Hint Unfold Join : core.

Lemma join_trans A B C
  (h0 : A ⇔ B)
  (h1 : B ⇔ C) :
  (* --- *)
  A ⇔ C.
Proof.
  rewrite /Join in h0 h1 *.
  case : h0 => C0 [*].
  case : h1 => C1 [*].
  have [D [*]] : exists D, C0 ⇒* D /\ C1 ⇒* D by sfirstorder use:multipar_confluence.
  exists D. sfirstorder use:multipar_trans.
Qed.

Lemma par_refl A : Par A A.
Proof. elim : A; sfirstorder. Qed.

Lemma multipar_refl A : Multipar A A.
Proof. hauto l:on use:par_refl. Qed.

Lemma join_sym A B
  (h0 : A ⇔ B) :
  (* --------- *)
  B ⇔ A.
Proof. sfirstorder unfold:Join. Qed.

Lemma join_refl A:
  A ⇔ A.
Proof. sfirstorder use:multipar_refl. Qed.

Lemma par_implies_defeq A B
  (h0 : A ⇒ B) :
  (* -------- *)
  A ≡ B.
Proof. elim : A B / h0; sfirstorder. Qed.

Lemma multipar_implies_defeq A B
  (h0 : A ⇒* B) :
  (* -------- *)
  A ≡ B.
Proof.
  elim : A B /h0;
    sfirstorder use:par_implies_defeq.
Qed.

Lemma join_implies_defeq A B
  (h0 : A ⇔ B) :
  (* -------- *)
  A ≡ B.
Proof.
  hauto q:on ctrs:DefEq use:multipar_implies_defeq.
Qed.

Lemma multipar_par_app_intro A0 B0 A1 B1
  (h0 : A0 ⇒* B0)
  (h1 : A1 ⇒ B1) :
  (* ----------- *)
  app A0 A1 ⇒* app B0 B1.
Proof.
  move : A1 B1 h1.
  elim : A0 B0 / h0.
  - hauto l:on ctrs:clos_trans_1n.
  - move=> ? B ? ? ? ? A1 B1 h2.
    apply Relation_Operators.t1n_trans with (y := app B B1); auto.
    sfirstorder use:par_refl.
Qed.

Lemma multipar_app_intro A0 B0 A1 B1
  (h0 : A0 ⇒* B0)
  (h1 : A1 ⇒* B1) :
  (* ------------ *)
  app A0 A1 ⇒* app B0 B1.
Proof.
  move : A0 B0 h0.
  elim : A1 B1 / h1.
  - sfirstorder use:multipar_par_app_intro.
  - hauto lq:on use:multipar_trans, multipar_par_app_intro, multipar_refl.
Qed.

Lemma join_app_intro  A0 B0 A1 B1
  (h0 : A0 ⇔ B0)
  (h1 : A1 ⇔ B1) :
  (* ------------ *)
  app A0 A1 ⇔ app B0 B1.
Proof.
  hauto q:on use:multipar_app_intro.
Qed.

Lemma multipar_abs_intro A B
  (h0 : A ⇒* B) :
  (* --------- *)
  lam A ⇒* lam B.
Proof.
  elim : A B / h0; hauto lq:on inv:Par ctrs:clos_trans_1n, Par.
Qed.

Lemma join_abs_intro A B
  (h0 : A ⇔ B) :
  (* --------- *)
  lam A ⇔ lam B.
Proof.
  hauto q:on use:multipar_abs_intro.
Qed.

Lemma multipar_join A B
  (h0 : A ⇒* B) :
  (* ----------- *)
  A ⇔ B.
Proof.
  sfirstorder use:multipar_refl.
Qed.

Lemma par_join A B
  (h0 : A ⇒ B) :
  (* ----------- *)
  A ⇔ B.
Proof.
  hauto lq:on ctrs:clos_trans_1n use:multipar_join.
Qed.

Lemma multipar_par_pi_intro A0 B0 A1 B1
  (h0 : A0 ⇒* B0)
  (h1 : A1 ⇒ B1) :
  (* ------------ *)
  pi A0 A1 ⇒* pi B0 B1.
Proof.
  move : A1 B1 h1.
  elim : A0 B0 / h0.
  - hauto lq:on ctrs:clos_trans_1n, Par.
  - move=> ? B ? ? ? ? A1 B1 h2.
    apply Relation_Operators.t1n_trans with (y := pi B B1); auto.
    sfirstorder use:par_refl.
Qed.

Lemma multipar_pi_intro A0 B0 A1 B1
  (h0 : A0 ⇒* B0)
  (h1 : A1 ⇒* B1) :
  (* ------------ *)
  pi A0 A1 ⇒* pi B0 B1.
Proof.
    move : A0 B0 h0.
  elim : A1 B1 / h1.
  - sfirstorder use:multipar_par_pi_intro.
  - hauto lq:on use:multipar_trans, multipar_par_pi_intro, multipar_refl.
Qed.

Lemma join_pi_intro A0 B0 A1 B1
  (h0 : A0 ⇔ B0)
  (h1 : A1 ⇔ B1) :
  (* ------------ *)
  pi A0 A1 ⇔ pi B0 B1.
Proof.
  hauto q:on use:multipar_pi_intro.
Qed.

Lemma defeq_implies_join A B
  (h0 : A ≡ B) :
  (* --------- *)
  A ⇔ B.
Proof.
  elim : A B /h0.
  - hauto l:on.
  - strivial use:join_sym.
  - hauto l:on use:join_trans.
  - hauto l:on use:join_app_intro.
  - hauto lq:on use:join_abs_intro.
  - hauto l:on use:join_pi_intro.
  - hauto l:on.
  - move=> a0 a1 b0 b1 ? ? _ ih0 _ ih1; subst.
    apply join_trans with (B := app (lam a1) b1); first by hauto l:on use:join_app_intro.
    have : app (lam a1) b1 ⇒ subst_tm (b1..) a1 by sfirstorder use:par_refl.
    sfirstorder use:par_join.
Qed.

Lemma defeq_join_iff A B : A ≡ B <-> A ⇔ B.
Proof.
  firstorder using join_implies_defeq, defeq_implies_join.
Qed.

Lemma par_proj A0 B0 A1 B1
  (h0 : pi A0 A1 ⇒ pi B0 B1) :
  A0 ⇒ B0 /\ A1 ⇒ B1.
Proof. hauto lq:on inv:Par. Qed.

Lemma multipar_proj A0 B0 A1 B1
  (h0 : pi A0 A1 ⇒* pi B0 B1) :
  A0 ⇒* B0 /\ A1 ⇒* B1.
Proof.
  move E0: (pi A0 A1) h0 => A.
  move E1: (pi B0 B1) => B h.
  move : A0 A1 B0 B1 E0 E1.
  elim : A B / h; sblast use:par_proj.
Qed.

Lemma multipar_pi_inv A0 A1 C
  (h0 : pi A0 A1 ⇒* C) :
  exists B0 B1, pi A0 A1 ⇒* pi B0 B1 /\ C = pi B0 B1.
Proof.
  move E : (pi A0 A1) h0 => A h.
  move : A0 A1 E.
  elim : A C / h.
  - hauto lq:on rew:off inv:Par ctrs:clos_trans_1n.
  - hauto lq:on rew:off inv:Par ctrs:clos_trans_1n.
Qed.

Lemma join_pi_proj A0 B0 A1 B1
  (h0 : pi A0 A1 ⇔ pi B0 B1) :
  A0 ⇔ B0 /\ A1 ⇔ B1.
Proof.
  qauto use:multipar_proj, multipar_pi_inv.
Qed.

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
    (* This mess explains why the cbpv proof uses equations as premises
       to make Typing G a A rely only on vars so the IH becomes easier to apply  *)
    (* Use ssreflect to suppress the substitution of the second occurence? *)
    replace (ren_tm ξ (app a b)) with
      (app (ren_tm ξ a) (ren_tm ξ b));
      last by asimpl.
    replace (ren_tm ξ (subst_tm (scons b ids) B)) with
      ( (subst_tm (scons (ren_tm ξ b) ids) (ren_tm (upRen_tm_tm ξ) B)));
      last by asimpl.
    apply T_App with (A := ren_tm ξ A); eauto.
  - hauto q:on ctrs:Typing use:defeq_renaming.
    (* move => n Γ a A B s h0 ih0 h1 ih1 h2 m ξ Δ hΔ. *)
    (* apply T_Conv with (A := ren_tm ξ A) (s := s); eauto. *)
    (* by apply :defeq_renaming. *)
Qed.

Lemma morphing
  (n : nat) (Γ : context) (a : tm) (A : tm)
  (h : Typing n Γ a A) :
  forall m (ξ : fin -> tm) (Δ : context),
  (forall i, i < n -> Typing m Δ (ξ i) (subst_tm ξ (dep_ith Γ i))) ->
  (* ---------------------------------------- *)
  (Typing m Δ (subst_tm ξ a) (subst_tm ξ A)).
Proof.
  elim : n Γ a A / h.
  - sfirstorder.
  - sfirstorder.
  - move => m Γ A B s1 s2 h0 ih0 h1 ih1 x ξ Δ hΔ /=.
    apply T_Pi with (s1 := s1); eauto.
    (* Clear ih0 from the context and apply ih1 *)
    apply : {ih0} ih1.
    case => [| i /Arith_prebase.lt_S_n] ?.
    + rewrite /dep_ith.
      asimpl.
      (* Again, maybe derive an alternative typing judgment lemma to make life easier *)
      replace (subst_tm (ξ >> ren_tm shift) A) with
        (ren_tm shift (subst_tm ξ A)); last by asimpl.
      apply T_Var; lia.
    + rewrite dep_ith_ren_tm.
      asimpl.
      replace (subst_tm (ξ >> ren_tm shift) (dep_ith Γ i)) with
        (ren_tm shift (subst_tm ξ (dep_ith Γ i))); last by asimpl.
      apply : renaming; eauto.
      move => x0 ?.
      split.
      * rewrite /dep_ith.
        by asimpl.
      * rewrite /shift; lia.
  - move => n Γ A a B s h0 ih0 h1 ih1 m ξ Δ hΔ /=.
    apply T_Lam with (s := s) ; eauto.
    (* Clear ih0 from the context and apply ih1 *)
    apply : {ih1} ih0.
    case => [| i /Arith_prebase.lt_S_n] ?.
    + rewrite /dep_ith.
      asimpl.
      (* Again, maybe derive an alternative typing judgment lemma to make life easier *)
      replace (subst_tm (ξ >> ren_tm shift) A) with
        (ren_tm shift (subst_tm ξ A)); last by asimpl.
      apply T_Var; lia.
    + rewrite dep_ith_ren_tm.
      asimpl.
      replace (subst_tm (ξ >> ren_tm shift) (dep_ith Γ i)) with
        (ren_tm shift (subst_tm ξ (dep_ith Γ i))); last by asimpl.
      apply : renaming; eauto.
      move => x0 ?.
      split.
      * rewrite /dep_ith.
        by asimpl.
      * rewrite /shift; lia.
  - move => n Γ a A B b h0 ih0 h1 ih1 m ξ Δ hΔ.
    simpl in ih0.
    asimpl in ih0.
    (* replace (ren_tm ξ (app a b)) with *)
    (*   (app (ren_tm ξ a) (ren_tm ξ b)); *)
    (*   last by asimpl. *)
    replace (subst_tm (scons (subst_tm ξ b) ξ) B) with
      (subst_tm (scons (subst_tm ξ b) ids) (subst_tm (up_tm_tm ξ) B));
      last by asimpl.
    (* autosubst doesn't want to rewrite the generic up_tm  *)
    (* must use the specialized up_tm_tm instead *)
    econstructor; eauto.

    (* The following is required if we had used up_tm instead *)
    (* asimpl. *)
    (* f_equal. *)
    (* apply FunctionalExtensionality.functional_extensionality. *)
    (* case. *)
    (* by asimpl. *)
    (* move => n0. *)
    (* asimpl. *)
    (* rewrite /up_tm. *)
    (* simpl. *)
    (* asimpl. *)
    (* reflexivity. *)
  - hauto q:on ctrs:Typing use:defeq_subst.
Qed.

Lemma subst_one
  (n : nat) (Γ : fin -> tm) (a : tm)
  (b : tm) (A B : tm) :
  Typing (S n) (A .: Γ) a B ->
  Typing n Γ b A ->
  (* ------------------------------------ *)
  Typing n Γ (subst_tm (b ..) a) (subst_tm (b ..) B).
Proof.
  move => h0 h1.
  apply morphing with (Γ := A .: Γ) (n := S n); auto.
  case => *.
  - rewrite /dep_ith; by asimpl.
  - rewrite dep_ith_ren_tm.
    asimpl.
    hauto lq:on ctrs:Typing solve:lia.
Qed.

Lemma app_inv n Γ (a b T : tm)
  (h : Typing n Γ (app a b) T) :
  exists A B,
    Typing n Γ a (pi A B) /\
    Typing n Γ b A /\
    ((subst_tm (b..) B ≡ T /\ exists s, Typing n Γ T (type s))
     \/ subst_tm (b..) B = T).
Proof.
  move eqn : (app a b) h => t h.
  move : a b eqn.
  elim : n Γ t T / h; try congruence.
  - hauto l:on ctrs:Typing.
  - hauto l:on.
Qed.

Lemma abs_inv n Γ (a T : tm)
  (h : Typing n Γ (lam a) T) :
  exists A B,
    Typing (S n) (A .: Γ) a B /\
    ((pi A B ≡ T /\ exists s, Typing n Γ T (type s))
     \/ pi A B = T).
Proof.
  move eqn : (lam a) h => t h.
  move : a eqn.
  elim : n Γ t T / h; try congruence.
  - hauto lq:on ctrs:Typing.
  (* DO *NOT* USE ctrs: in this case *)
  - hauto l:on.
Qed.

Lemma preservation (a a' : tm) (h : Red a a') :
  forall n Γ A, Typing n Γ a A -> Typing n Γ a' A.
  elim : a a' / h.
  - move => a b n Γ A /app_inv.
    move => [A0 [B h0]].
    case : h0.
    move /abs_inv => [A1 [B0 [? h2]]].
    case : h2.
    + move => [h2 [s h4]] [h5 h6].
      case : h6 => [[h6 [s0 h7]] | h6].
      * apply T_Conv with (A := subst_tm (b..) B) (s := s0); try assumption.
        (* pisnd *)
        (* also need to strengthen lam_inv to show that the pi type is
        well-formed *)
        admit.
      * subst.
        (* same here *)
admit.
    + hauto lq:on ctrs:Typing use:subst_one.
  - move => a a' b h0 ih0 n Γ A /app_inv.
    hauto q:on ctrs:Typing.
Admitted.

(* Need par proof *)
Lemma empty_lam_pi_inv : forall (a : tm) (Γ : context) (A B : tm),
    Typing 0 Γ a (pi A B) ->
    is_value a ->
    exists a0, a = lam a0.
Proof.
(*   hauto q:on inv:Typing solve:lia. *)
  (* Qed. *)
Admitted.

Lemma progress (a : tm) (A  :tm) (Γ : context) (h : Typing 0 Γ a A) :
  is_value a \/ exists a', a ⤳ a'.
Proof.
  move : h.
  move eq0 : 0 => zero h.
  move : eq0.
  elim : zero Γ a A / h; eauto 3.
  (* var *)
  - lia.
  (* app *)
  - hauto ctrs:Red l:on use:empty_lam_pi_inv.
Qed.
