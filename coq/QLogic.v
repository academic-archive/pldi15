Require Import QClight.
Require Import ZArith.

Notation "x ≤ y" := (Z.le x y) (at level 70, no associativity).
Notation "x ≥ y" := (Z.ge x y) (at level 70, no associativity).

Section QLOGIC.
Open Scope Z.
Context `{Sem: BaseSemantics} (ge: genv) (M: revent → Z).

(** Resource safety of a program configuration. *)
Definition pay t c := List.fold_left (λ c e, c - M e) t c.

Reserved Notation "C ↓ n" (at level 60).
Inductive runs: nat → (stmt * cont * mstate * Z) → Prop :=

  | safe_zero C: C ↓ 0

  | safe_step n s1 k1 m1 c:
    (∀ t s2 k2 m2,
      step_base ge t (s1, k1, m1) (s2, k2, m2) →
      (s2, k2, m2, pay t c) ↓ n) →
    0 ≤ c →
    (s1, k1, m1, c) ↓ (S n)

where "C ↓ n" := (runs n C).

Lemma runs_le:
  ∀ n n' (LE: le n' n) C (RUNS: C ↓ n), C ↓ n'.
Proof.
induction n; intros.
+ replace n' with O by omega. auto.
+ inversion RUNS; subst.
  destruct n'; constructor.
  - intros; apply IHn.
    omega. auto.
  - assumption.
Qed.


(** Logic assertions. *)
Delimit Scope Logic_scope with L.

Definition assn := mstate → Z → Prop.

Definition assn_addZ (P: assn) (x: Z) :=
  λ m c, 0 ≤ c - x ∧ P m (c - x).

Definition assn_bottom: assn := λ _ _, False.

Infix "+" := assn_addZ: Logic_scope.
Notation "⊥" := assn_bottom: Logic_scope.

(* Stack independent assertions are used
 * for function calls.  It is stated as
 * a typeclass so, when we define compound
 * assertions it will be possible to derive
 * stack independence with the class
 * resolution mechanism of Coq.
 *)
Class StackIndep (P: assn): Prop :=
  stack_indep: ∀ σ σ' θ c, P (σ, θ) c → P (σ', θ) c.

Lemma assn_addZ_props:

  (* Weak associative *)
  (∀ (P: assn) (x y: Z) (XSGN: 0 ≤ x) (YSGN: 0 ≤ y) m c,
    ((P + x) + y)%L m c ↔ (P + (x + y))%L m c)

  (* Weak commutative *)
∧ (∀ (P: assn) (x y: Z) (YSGN: 0 ≤ y) m c,
    ((P + x) + y)%L m c → ((P + y) + x)%L m c).

Proof with assumption.
unfold assn_addZ; intuition;
match goal with [ H: ?P _ ?x |- ?P _ ?y ] =>
  replace y with x by omega end...
Qed.

Definition assn_addZ_pos  := (proj1 assn_addZ_props).
Definition assn_addZ_comm := (proj2 assn_addZ_props).


(** Logic semantics in terms of resource safety. *)
Definition safe n (P: assn) (sk: stmt * cont) :=
  let (s, k) := sk in
  ∀ m c (INI: P m c) , 0 ≤ c → (s, k, m, c) ↓ n.

Definition safek n (B: assn) (R: option rval → assn) (Q: assn) k :=
    safe n B (SBreak, k)
  ∧ (∀ r, safe n (λ m c, (∀ v, evalo ge m r v → R v m c)) (SReturn r, k))
  ∧ safe n Q (SSkip, k).

Definition valid n (B: assn) (R: option rval → assn) (P: assn) s (Q: assn) :=
  (∀ x k p
     (LE: le p n)
     (XSGN: 0 ≤ x)
     (SAFEK: safek p (B + M EBreak + x) (λ r, R r + x) (Q + x) k),
    safe p (P + x) (s, k)
  )%L.

Notation "n \ B \ R ⊨ {{ P }} S {{ Q }}" :=
  (valid n B%L R%L P%L S Q%L)
  (at level 74, R at next level, B at next level,
  format "n \  B \  R  ⊨  '[' {{  P  }} '/'  S  '/' {{  Q  }} ']'").

Inductive fun_spec: Type :=
  (* A function specification. *)
  FSpec

    (* The type of logical variables. *)
    (Log: Type)

    (* Function precondition,
     * parameterized by the logical state
     * and the function arguments.
     *)
    (Pf: Log → list rval → assn)

    (* Function postcondition,
     * parameterized by the return value
     * and the logical state.
     *)
    (Qf: Log → option rval → assn):

    (∀ z a, StackIndep (Pf z a)) →
    (∀ z r, StackIndep (Qf z r)) →
    fun_spec.

Definition flog (fs: fun_spec) :=
  let (Log, _, _, _, _) := fs in Log.
Definition fpre (fs: fun_spec): (flog fs → list rval → assn) :=
  match fs return (flog fs → list rval → assn) with
  | FSpec _ Pf _ _ _ => Pf
  end.
Definition fpost (fs: fun_spec): (flog fs → option rval → assn) :=
  match fs return (flog fs → option rval → assn) with
  | FSpec _ _ Qf _ _ => Qf
  end.

(* A context of hypothesis on functions used in logic derivations,
 * it is often written Δ.
 *)
Definition fun_ctx := fid → option fun_spec.

Definition ctx_add {A: Type} (c1 c2: fid → option A) f :=
  match c2 f with
  | Some x => Some x
  | None => c1 f
  end.

Infix "∪" := ctx_add (at level 60).

(* This defines the validity of a set of hypothesis. *)
Definition validC (n: nat) (Δ: fun_ctx): Prop :=
  ∀ f spec bdy,
    Δ f = Some spec →
    find_func ge f = Some bdy →
    ∀ y a, n\ ⊥\ λ r, fpost spec y r + M (EReturn f)
      ⊨ {{ fpre spec y a }} bdy {{ ⊥ }}.

(* Various weakening lemmas. *)
Lemma safe_le:
  ∀ n n' P s k (LE: le n' n), safe n P (s, k) → safe n' P (s, k).
Proof. unfold safe; intuition; eauto using runs_le. Qed.
Lemma safek_le:
  ∀ n n' B R Q k (LE: le n' n), safek n B R Q k → safek n' B R Q k.
Proof. unfold safek; intuition; eauto using safe_le. Qed.


(** Soundness of logic rules. *)

(* Prove safety of a configuration by trying to
 * make a step.
 *)
Ltac step :=
  match goal with
  | [ |- _ ↓ (S ?n) ] =>
    constructor;
    [ let hstep := fresh in
      intros ? ? ? ? hstep;
      inversion hstep; subst; clear hstep
    | simpl; try omega ]
  | [ |- _ ↓ (S _) ] => fail 1
  | [ |- _ ↓ 0 ] => constructor
  | [ |- _ ↓ ?n ] => destruct n; step
  end.

(* Useful to combine a weakening and an hypothesis
 * in the context.
 *)
Ltac apple H :=
  match goal with
  | [ |- runs _ _ ]          => eapply runs_le
  | [ |- safek _ _ _ _ _ ]   => eapply safek_le
  end; [| eapply H ]; try omega.


Lemma sound_LSkip:
  ∀ n B R Q,
  n\ B\ R ⊨ {{ Q }} SSkip {{ Q }}.
Proof.
unfold valid; intros.
apply SAFEK.
Qed.

Lemma sound_LBreak:
  ∀ n B R Q,
  n\ B\ R ⊨ {{ B + M EBreak }} SBreak {{ Q }}.
Proof.
unfold valid; intros.
apply SAFEK.
Qed.

Lemma sound_LReturn:
  ∀ n B R Q r,
  n\ B\ R ⊨ {{ λ m c, ∀ v, evalo ge m r v → R v m c }} SReturn r {{ Q }}.
Proof.
unfold valid, safek, safe, assn_addZ; intros.
apply SAFEK; intuition; eapply INI.
Qed.

Lemma sound_LLoop:
  ∀ n B R I Q s
    (BDY: n\ Q\ R ⊨ {{ I }} s {{ I + M ELoop }}),
  n\ B\ R ⊨ {{ I }} SLoop s {{ Q }}.
Proof.
unfold valid; intros.
induction p as [p IND] using lt_wf_rec.

unfold safe; intros. step.
apply BDY with (x := x); eauto. omega.
clear INI.
unfold safek, safe; intuition; step.
+ apply assn_addZ_comm in INI; auto.
  apple SAFEK; apply INI.
+ apple SAFEK; assumption.
+ apply assn_addZ_comm in INI; auto.
  apply (IND p); eauto; try apply INI.
  omega.
  apple SAFEK.
Qed.

Lemma sound_LFrame:
  ∀ n B R P s Q x (XSGN: 0 ≤ x)
    (PRE: n\ B\ R ⊨ {{ P }} s {{ Q }}),
  n\ (B + x)\ (λ r, R r + x) ⊨ {{ P + x }} s {{ Q + x }}.
Proof.
unfold valid, safe; intros.
apply PRE with (x := x + x0); try omega.
clear INI.
unfold safek, safe;
  intuition; apply SAFEK; eauto.
+ unfold assn_addZ in *.
  repeat split; try omega.
  replace (c0 - x0 - M EBreak - x)
     with (c0 - (x + x0) - M EBreak)
    by omega.
  apply INI.
+ intros; rewrite assn_addZ_pos; auto.
+ rewrite assn_addZ_pos; auto.
+ rewrite <- assn_addZ_pos; auto.
Qed.

Lemma sound_LSeq:
  ∀ n B R P s1 Q' s2 Q
    (PRE1: n\ B\ R ⊨ {{ P }} s1 {{ Q' + M ESeq }})
    (PRE2: n\ B\ R ⊨ {{ Q' }} s2 {{ Q }}),
  n\ B\ R ⊨ {{ P }} SSeq s1 s2 {{ Q }}.
Proof.
unfold valid at 3, safe; intros.
step.
apply PRE1 with (x := x); try (omega || assumption).
clear INI.
unfold safek, safe; intuition; step.
+ apple SAFEK; assumption.
+ apple SAFEK; assumption.
+ apply assn_addZ_comm in INI; try assumption.
  eapply PRE2 with (x := x); try (omega || apply INI).
  apple SAFEK; assumption.
Qed.

Lemma sound_LIf:
  ∀ n B R (P: assn) e st sf Q,
    let P' b m c: Prop :=
      ∃ v, evalr ge m e v ∧ val_bool v b ∧ P m c
    in
  ∀ (SIDE: ∀ b m c, P' b m c → 0 ≤ c - M (ECond b))
    (PRE: ∀ b,
      n\ B\ R ⊨
        {{ P' b + -M (ECond b) }}
        if b then st else sf
        {{ Q  }}),
  n\ B\ R ⊨ {{ P + M (EEvalr e) }} SIf e st sf {{ Q }}.
Proof.
unfold valid at 2, safe; intros.
step; simpl.
destruct INI as [? [? ?]].
refine (_ (SIDE _ _ _ _));
  repeat esplit; eauto. intros.
apply PRE with (x := x); try omega.
apple SAFEK.
repeat esplit; eauto; try omega.
replace (c - _ - _ - x - - M (ECond b))
    with (c - x - M (EEvalr e)) by omega.
assumption.
Qed.

Lemma sound_LExtend:
  ∀ (Δ Δ': fun_ctx)
    (PRE: ∀ f spec bdy,
      Δ' f = Some spec →
      find_func ge f = Some bdy →
      ∀ y a n,
        validC n (Δ ∪ Δ') →
        S n\ ⊥\ λ r, fpost spec y r + M (EReturn f)
          ⊨ {{ fpre spec y a }} bdy {{ ⊥ }})
    (VALID: ∀ n, validC n Δ),
  ∀ n, validC n (Δ ∪ Δ').
Proof.
induction n as [n IND] using lt_wf_rec.
unfold validC, ctx_add.
intros until 0.
case_eq (Δ' f).
+ inversion 2; subst.
  intros.
  destruct n.
  - unfold valid, safe; intros.
    replace p with O by omega.
    constructor.
  - apply PRE with (f := f); auto.
+ intros.
  eapply VALID; eassumption.
Qed.

Lemma sound_LCall:
  ∀ (Δ: fun_ctx) f spec y B R ret args
    (SPEC: Δ f = Some spec)
    n (VCTX: validC n Δ)
    (A: stack -> Prop),
  let P (m: mstate) c :=
    let (σ, _) := m in
    ∀ vl, eval_list ge m args vl →
          fpre spec y vl m c ∧ A σ
  in
  let Q (m: mstate) c :=
    let (σ, θ) := m in
    ∃ v σ', ret_stack ge f ret v σ' σ
          ∧ fpost spec y v (σ', θ) c ∧ A σ'
  in
  S n\ B\ R ⊨ {{ P + M (ECall f) }} SCall ret f args {{ Q }}.
Proof.
unfold valid, safe; intros.
step.
unfold assn_addZ in INI.
destruct INI as [C0 [C1 PREC]].
refine (_ (PREC vl _)); auto. clear PREC. intros [PRE FRAME].
eapply VCTX with (x := x) (y := y); simpl;
  (eassumption || omega || idtac).

+ clear C0 C1 PRE H c.
  unfold safek, safe; intuition; step.
  refine (_ (INI vr _)); auto. clear INI.
  intros [C0 [C1 POST]].
  apple SAFEK. clear SAFEK.
  unfold assn_addZ; simpl.
  repeat eexists; eauto; try omega.
  replace (c - M (EReturn f) - x)
     with (c - x - M (EReturn f)) by omega.
  destruct spec as [? ? ? ? STKINDEP].
  eapply STKINDEP. apply POST.
  simpl; omega.


+ split. omega.
  replace (c - M (ECall f) - x)
     with (c - x - M (ECall f)) by omega.
  destruct spec as [? ? ? STKINDEP ?].
  eapply STKINDEP. apply PRE.
Qed.

End QLOGIC.
