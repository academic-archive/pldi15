Require Import QClight.
Require Import ZArith.

Notation "x ≤ y" := (Z.le x y) (at level 70, no associativity).
Notation "x ≥ y" := (Z.ge x y) (at level 70, no associativity).

Section QLOGIC.
Open Scope Z.
Context `{Sem: BaseSemantics} (ge: genv).

(** Resource safety of a program configuration. *)
Definition pay t c := List.fold_left (λ c e, c - e) t c.

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
  λ m c, P m (c - x).

Definition assn_bottom: assn := λ _ _, False.

Infix "+" := assn_addZ: Logic_scope.
Notation "⊥" := assn_bottom: Logic_scope.

(* Stack independent assertions are used
 * for function calls.
 *)
Definition StackIndep (P: assn): Prop :=
  ∀ σ σ' θ c, P (σ, θ) c → P (σ', θ) c.


(** Logic semantics in terms of resource safety. *)
Definition safe n (P: assn) (sk: stmt * cont) :=
  let (s, k) := sk in
  ∀ m c (INI: P m c), 0 ≤ c ∧ (s, k, m, c) ↓ n.

Definition safek n (B: assn) (R: option rval → assn) (Q: assn) k :=
    safe n B (SBreak, k)
  ∧ (∀ r, safe n (λ m c, 0 ≤ c ∧ ∀ v, evalo ge m r v → R v m c) (SReturn r, k))
  ∧ safe n Q (SSkip, k).

Definition valid n (B: assn) (R: option rval → assn) (P: assn) s (Q: assn) :=
  (∀ x k p
     (LE: le p n)
     (XSGN: 0 ≤ x)
     (SAFEK: safek p (B + x) (λ r, R r + x) (Q + x) k),
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
  ∀ f spec (DEF: Δ f = Some spec),
  (∀ bdy y a,
     find_func ge f = Some bdy →
     n\ ⊥\ λ r, fpost spec y r
       ⊨ {{ λ m c, 0 ≤ c ∧ fpre spec y a m c }} bdy {{ ⊥ }}).

(* Various weakening lemmas. *)
Lemma safe_le:
  ∀ n n' P s k (LE: le n' n), safe n P (s, k) → safe n' P (s, k).
Proof. unfold safe; intros.
       destruct (H m c INI); eauto using runs_le. Qed.
Lemma safek_le:
  ∀ n n' B R Q k (LE: le n' n), safek n B R Q k → safek n' B R Q k.
Proof. unfold safek; intuition; eauto using safe_le. Qed.


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
    | auto ]
  | [ |- _ ↓ (S _) ] => fail 1
  | [ |- _ ↓ 0 ] => constructor
  | [ |- _ ↓ ?n ] => destruct n; step
  end.


(* An powerful property of the validity. *)
Lemma valid_nneg:
  ∀ n B R P Q s x (XSGN: 0 ≤ x)
    (TRIP: n\ B\ R ⊨ {{ P }} s {{ Q }})
    (QPOS: ∀ m c, (Q + x)%L m c → 0 ≤ c)
    (BPOS: ∀ m c, (B + x)%L m c → 0 ≤ c),
  ∀ m c, (P + x)%L m c → 0 ≤ c.
Proof.
unfold valid; intros.
eapply (TRIP x KStop n).
+ omega.
+ assumption.
+ unfold safek, safe, assn_addZ. clear c m H.
  intuition; eauto; step; eauto.
+ unfold assn_addZ.
  eassumption.
Qed.


(** Soundness of logic rules. *)

(* Try to prove a goal '0 ≤ c' by using the
 * safety of one continuation in the context.
 *)
Ltac fuel :=
  match goal with
  | [ S: safek _ _ _ _ _ |- 0 ≤ ?c ] =>
    destruct S as [S1 [S2 S3]];
      try (eapply S1; now eauto);
      try (eapply S2; now eauto);
      try (eapply S3; now eauto);
      fail 1
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
  n\ B\ R ⊨ {{ B }} SBreak {{ Q }}.
Proof.
unfold valid; intros.
apply SAFEK.
Qed.

Lemma sound_LReturn:
  ∀ n B R Q r,
  n\ B\ R ⊨ {{ λ m c, 0 ≤ c ∧ ∀ v, evalo ge m r v → R v m c }} SReturn r {{ Q }}.
Proof.
unfold valid, safek, safe, assn_addZ; intros.
apply SAFEK; intuition; eapply INI.
Qed.

Lemma sound_LTick:
  ∀ n B R (Q: assn) q
    (QNNEG: q < 0 → ∀ m c, Q m c → 0 ≤ c),
  n\ B\ R ⊨ {{ Q }} STick q {{ Q + -q }}.
Proof.
intros. unfold valid, safe; intros.
assert (CNNEG: 0 ≤ c).
{ assert (QD: q < 0 ∨ 0 ≤ q) by omega.
  destruct QD as [HQ | HQ].
  + cut (0 ≤ c - x).
    intro. omega.
    eapply QNNEG. exact HQ. exact INI.
  + destruct SAFEK as [_ [_ S]].
    cut (0 ≤ c - q). intro. omega.
    eapply S. unfold assn_addZ.
    replace (c - q - x - -q)
    with (c - x) by omega.
    exact INI.
}
split; [ assumption | step ].
apple SAFEK. unfold assn_addZ. simpl.
replace (c - q - x - - q)
with (c - x) by omega.
exact INI.
Qed.

Lemma sound_LLoop:
  ∀ n B R I Q s
    (BDY: n\ Q\ R ⊨ {{ I }} s {{ I }})
    (IGEQ: ∀ m c, I m c → Q m c),
  n\ B\ R ⊨ {{ I }} SLoop s {{ Q }}.
Proof.
unfold valid; intros.
induction p as [p IND] using lt_wf_rec.
unfold safe; intros.
Ltac invq H :=
  match goal with
  | [ S: safek _ _ _ _ _ |- 0 ≤ _ ] =>
    destruct S as [_ [_ S]];
    eapply S; unfold assn_addZ in *;
    now eauto using H
  end || fuel.
assert (CNNEG: 0 ≤ c). invq IGEQ.
split; [ assumption | step ].
apply BDY with (x := x); eauto. omega.
clear INI.
unfold safek, safe; intuition;
  try step; try invq IGEQ.
+ apple SAFEK; apply INI.
+ simpl; apple SAFEK; now auto.
+ apply (IND p); eauto; try apply INI.
  omega.
  apple SAFEK.
Qed.

Lemma sound_LSeq:
  ∀ n B R P s1 Q' s2 Q
    (PRE1: n\ B\ R ⊨ {{ P }} s1 {{ Q' }})
    (PRE2: n\ B\ R ⊨ {{ Q' }} s2 {{ Q }}),
  n\ B\ R ⊨ {{ P }} SSeq s1 s2 {{ Q }}.
Proof with try (intros; fuel).
unfold valid at 3, safe; intros.
assert (C: 0 ≤ c).
{ eapply (valid_nneg n B R P Q' s1 x XSGN PRE1)...
  eapply (valid_nneg n B R Q' Q s2 x XSGN PRE2)...
  eassumption.
}
split; [ assumption | step ].
apply PRE1 with (x := x); try (omega || assumption).
clear INI.
unfold safek, safe; intuition; try step; try fuel.
+ apple SAFEK; assumption.
+ simpl; apple SAFEK; auto.
+ eapply (valid_nneg n B R Q' Q s2 x XSGN PRE2)...
  eassumption.
+ eapply PRE2 with (x := x); try (omega || apply INI).
  simpl; apple SAFEK; now auto.
+ eapply (valid_nneg n B R Q' Q s2 x XSGN PRE2)...
  eassumption.
Qed.

Lemma sound_LFrame:
  ∀ n B R P s Q k (KSGN: 0 ≤ k)
    (PRE: n\ B\ R ⊨ {{ P }} s {{ Q }}),
  n\ (B + k)\ (λ r, R r + k) ⊨ {{ P + k }} s {{ Q + k }}.
Proof.
unfold valid, safe, assn_addZ; intros.
apply PRE with (x := x + k); try omega.
clear INI c m.
unfold safek, safe.
intuition; rewrite Z.sub_add_distr in *;
  try fuel; try apply SAFEK; auto.
rewrite Z.sub_add_distr; exact INI.
Qed.

Section LIF.
Let evalb m e b: Prop :=
  ∃ v, evalr ge m e v ∧ val_bool v b.

Lemma sound_LIf:
  ∀ n B R (P: assn) e st sf Q
    (PGEZ: ∀ m c, P m c → 0 ≤ c) (* required if e crashes ! *)
    (PRE: ∀ b, n\ B\ R ⊨
            {{ λ m c, evalb m e b ∧ P m c }}
              if b then st else sf
            {{ Q  }}),
  n\ B\ R ⊨ {{ P }} SIf e st sf {{ Q }}.
Proof.
unfold valid at 2, safe; intros.
assert (CNNEG: 0 ≤ c).
now cut (0 ≤ c - x);
  [ intro; omega | eapply PGEZ; exact INI ].
split; [ exact CNNEG | step ]; simpl.
apply PRE with (x := x); try omega.
apple SAFEK.
repeat esplit; eauto.
Qed.
End LIF.

Lemma sound_LExtend:
  ∀ (Δ Δ': fun_ctx)
    (PRE: ∀ f spec bdy,
            Δ' f = Some spec →
            find_func ge f = Some bdy →
            ∀ y a n,
              validC n (Δ ∪ Δ') →
              S n\ ⊥\ λ r, fpost spec y r
                ⊨ {{ λ m c, 0 ≤ c ∧ fpre spec y a m c }} bdy {{ ⊥ }})
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
    split. destruct INI as [? _]; omega.
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
    0 ≤ c ∧
    ∀ vl, eval_list ge m args vl →
          fpre spec y vl m c ∧ A (fst m)
  in
  let Q (m: mstate) c :=
    let (σ, θ) := m in
    ∃ v σ', ret_stack ge f ret v σ' σ
          ∧ fpost spec y v (σ', θ) c ∧ A σ'
  in
  S n\ B\ R ⊨ {{ P }} SCall ret f args {{ Q }}.
Proof.
unfold valid, safe; intros.
unfold assn_addZ in INI.
destruct INI as [CSGN PREC].
assert (CNNEG: 0 ≤ c) by omega.
split; [ exact CNNEG | step ].
refine (_ (PREC vl _)); auto. clear PREC. intros [PRE FRAME].
eapply VCTX with (x := x) (y := y); simpl;
  try eassumption; try omega.
+ unfold safek, safe.
  intuition; try destruct INI.
  step. apple SAFEK.
  unfold assn_addZ in *; simpl.
  repeat eexists; eauto; try omega.
  destruct spec as [? ? ? ? STKINDEP].
  eapply STKINDEP. apply H0. eauto.
+ destruct spec as [? ? ? STKINDEP ?].
  split; [ assumption |].
  eapply STKINDEP. apply PRE.
Qed.

End QLOGIC.
