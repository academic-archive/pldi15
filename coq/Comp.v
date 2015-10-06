Section Toy.

  Require Import Utf8.

  Parameter mem: Type.
  Parameter base: Type.
  Parameter sem_base: mem → base → mem → Prop.
  
  Inductive prog: Type :=
  | pskip
  | pbreak
  | pbase (b: base): prog
  | pseq (p1 p2: prog): prog
  | palt (p1 p2: prog): prog
  | ploop (p: prog): prog
  .

  Inductive cont: Type :=
  | kstop
  | kseq (p: prog) (k: cont)
  | kloop (p: prog) (k: cont)
  .

  Definition config: Type :=
    (mem * prog * cont) %type.
  Definition memof (c: config) :=
    fst (fst c).

  Reserved Notation "a ↦ b" (at level 60).
  Inductive step: config → config → Prop :=

  | sbase b m1 m2 k (BASE: sem_base m1 b m2)
    : (m1, pbase b, k) ↦ (m2, pskip, k)

  | sseq1 p1 p2 m k
    : (m, pseq p1 p2, k) ↦ (m, p1, kseq p2 k)
  | sseq2 p m k
    : (m, pskip, kseq p k) ↦ (m, p, k)
  | sseq3 p m k
    : (m, pbreak, kseq p k) ↦ (m, pbreak, k)

  | salt1 p1 p2 m k
    : (m, palt p1 p2, k) ↦ (m, p1, k)
  | salt2 p1 p2 m k
    : (m, palt p1 p2, k) ↦ (m, p2, k)

  | sloop1 p m k
    : (m, ploop p, k) ↦ (m, p, kloop p k)
  | sloop2 p m k
    : (m, pskip, kloop p k) ↦ (m, ploop p, k)
  | sloop3 p m k
    : (m, pbreak, kloop p k) ↦ (m, pskip, k)

  where "a ↦ b" := (step a b).

  Definition assn: Type :=
    mem → Prop.
  Definition bottom: assn :=
    λ _, False.

  (* I is an invariant *)
  Parameter I: assn.

  Inductive triple: assn → prog → assn → assn → Prop :=

  | tskip (A: assn)
    : triple (A) (pskip) (A) (bottom)

  | tbreak (B: assn)
    : triple (B) (pbreak) (bottom) (B)

  | tbase b (A: assn)
    : triple (λ m, ∀ m', sem_base m b m' → A m' ∧ I m')
             (pbase b) (A) (bottom)

  | tseq p1 p2 (A1 A2 A3 B: assn)
         (P1: triple A1 p1 A2 B)
         (P2: triple A2 p2 A3 B)
    : triple (A1) (pseq p1 p2) (A3) (B)

  | talt p1 p2 (A1 A2 B: assn)
         (P1: triple A1 p1 A2 B)
         (P2: triple A1 p2 A2 B)
    : triple (A1) (palt p1 p2) (A2) (B)

  | tloop p (A1 A2: assn)
          (P: triple A1 p A1 A2)
    : triple (A1) (ploop p) (A2) (bottom)

  | tweak p (A1 A2 B A1' A2' B': assn)
          (PRE: ∀ m, A1' m → A1 m)
          (PST: ∀ m, A2 m → A2' m)
          (BRK: ∀ m, B m → B' m)
          (P: triple A1 p A2 B)
    : triple (A1') p (A2') (B')
  .

  Require Import Setoid.

  Definition assn_eq (A1 A2: assn) :=
    ∀ m, A1 m ↔ A2 m.

  Lemma assn_eq_refl: ∀ A, assn_eq A A.
  Proof. unfold assn_eq; firstorder. Qed.
  Lemma assn_eq_sym: ∀ A1 A2, assn_eq A1 A2 → assn_eq A2 A1.
  Proof. unfold assn_eq; firstorder. Qed.
  Lemma assn_eq_trans:
    ∀ A1 A2 A3, assn_eq A1 A2 → assn_eq A2 A3 → assn_eq A1 A3.
  Proof. unfold assn_eq; firstorder. Qed.

  Add Parametric Relation : (assn) (assn_eq)
      reflexivity proved by assn_eq_refl
      symmetry proved by assn_eq_sym
      transitivity proved by assn_eq_trans
        as assn_eq_rel.

  Add Parametric Morphism : (triple) with signature
      (assn_eq ==> eq ==> assn_eq ==> assn_eq ==> iff)
        as triple_mor.
  Proof. unfold assn_eq. esplit; apply tweak; firstorder. Qed.

  
  (* Safety of configurations. *)
  
  Definition spec: Type := nat → config → Prop.

  Inductive safe: spec :=
  | safe0 c: safe 0 c
  | safeN n c
          (SAFE: ∀ c' (STEP: c ↦ c') (INV: I (memof c)),
                   safe n c' ∧ I (memof c'))
    : safe (S n) c
  .

  Require Import Arith.
  Require Import Omega.

  Section SafeRemarks.
    Inductive multi: config → config → Prop :=
    | multi0 c: multi c c
    | multiN c c₁ c₂: c ↦ c₁ → multi c₁ c₂ → multi c c₂
    .

    (* safety expresses the preservation of
     * invariants, during a given number of
     * steps
     *)
    Theorem safe_preserve:
      ∀ c c₁
        (MULT: multi c c₁)
        (IINI: I (memof c))
        (SAFE: ∀ n, safe n c),
        I (memof c₁).
    Proof.
      induction 1; intros.
      - assumption.
      - apply IHMULT.
        + generalize (SAFE 1). clear SAFE.
          inversion_clear 1.
          apply SAFE; assumption.
        + intros.
          generalize (SAFE (S n)). clear SAFE.
          inversion_clear 1.
          apply SAFE; assumption.
    Qed.

    (* safe is downward closed
     *)
    Lemma safe_le:
      ∀ n c (SAFE: safe n c) n' (LE: n' ≤ n),
        safe n' c.
    Proof.
      induction n as [|n IND]; intros.
      - inversion_clear LE.
        apply safe0.
      - destruct n' as [|n'].
        + apply safe0.
        + inversion SAFE; subst.
          apply safeN.
          intros. split.
          * apply IND; auto with arith.
            apply SAFE0; assumption.
          * apply SAFE0; assumption.
    Qed.
  End SafeRemarks.

  Definition valid n (A1: assn) p (A2 B: assn) :=
    ∀ n' k
      (SAFES: ∀ m, A2 m → safe n' (m, pskip, k))
      (SAFEB: ∀ m, B m  → safe n' (m, pbreak, k))
      (NLE: n' ≤ n) m (MOK: A1 m),
    safe n' (m, p, k).

  Lemma valid_le:
    ∀ n A1 p A2 B (VALID: valid n A1 p A2 B) n' (LE: n' ≤ n),
      valid n' A1 p A2 B.
  Proof.
    unfold valid; intros.
    apply VALID; (omega || eauto).
  Qed.

  
  (* Soundness: triple → valid *)
  
  Lemma valid_skip n (A: assn):
    valid n (A) (pskip) (A) (bottom).
  Proof.
    unfold valid; intros.
    apply SAFES, MOK.
  Qed.
    
  Lemma valid_break n (B: assn):
    valid n (B) (pbreak) (bottom) (B).
  Proof.
    unfold valid; intros.
    apply SAFEB, MOK.
  Qed.

  Ltac step :=
    match goal with
      | [ |- safe ?n _ ] =>
        destruct n;
          [ apply safe0
          | apply safeN; inversion_clear 1;
            intros; split; try assumption
          ]
    end.

  Ltac ale H :=
    match goal with
      | [ |- safe _ _ ] => eapply safe_le
      | [ |- valid ?n _ _ _ _ ] => eapply valid_le
    end; [apply H|]; try omega.

  Lemma valid_base n b (A: assn):
    valid n (λ m, ∀ m', sem_base m b m' → A m' ∧ I m')
          (pbase b) (A) (bottom).
  Proof.
    unfold valid; intros.
    step.
    - ale SAFES. apply MOK, BASE.
    - apply MOK, BASE.
  Qed.

  Lemma valid_seq n p1 p2 A1 A2 A3 B
        (VALID1: valid n (A1) (p1) (A2) (B))
        (VALID2: valid n (A2) (p2) (A3) (B)):
    valid n (A1) (pseq p1 p2) (A3) (B).
  Proof with (omega || eauto); intros.
    unfold valid; intros.
    step. apply VALID1...
    - step. apply VALID2...
      + ale SAFES; assumption.
      + ale SAFEB; assumption.
    - step.
      ale SAFEB; assumption.
  Qed.

  Lemma valid_alt n p1 p2 A1 A2 B
        (VALID1: valid n (A1) (p1) (A2) (B))
        (VALID2: valid n (A1) (p2) (A2) (B)):
    valid n (A1) (palt p1 p2) (A2) (B).
  Proof with (omega || eauto).
    unfold valid; intros.
    step.
    - ale VALID1...
    - ale VALID2...
  Qed.

  Lemma valid_loop n p A1 A2
        (VALID: valid n (A1) (p) (A1) (A2)):
    valid n (A1) (ploop p) (A2) (bottom).
  Proof.
    revert p A1 A2 VALID.
    induction n as [n IND] using lt_wf_rec.
    intros; unfold valid; intros.
    step. apply VALID; (omega || eauto).
    - intros. step. clear INV0.
      eapply (IND (S n')); (omega || eauto).
      ale VALID.
      intros; ale SAFES; assumption.
      intros; ale SAFEB; assumption.
    - intros. step.
      ale SAFES; eauto.
  Qed.


  Theorem soundness A1 p A2 B:
    triple (A1) (p) (A2) (B) →
    ∀ n, valid n (A1) (p) (A2) (B).
  Proof.
    induction 1; intros.
    - eauto using valid_skip.
    - eauto using valid_break.
    - eauto using valid_base.
    - eauto using valid_seq.
    - eauto using valid_alt.
    - eauto using valid_loop.
  Qed.


  (* Completeness: safe → triple *)

  Definition mgt p :=
    ∀ k, triple
           (λ m, ∀ n, safe n (m, p, k))
           (p)
           (λ m, ∀ n, safe n (m, pskip, k))
           (bottom).

  Lemma mgt_seq p1 p2
        (MGT1: mgt p1)
        (MGT2: mgt p2):
    mgt (pseq p1 p2).
  Proof.
    unfold mgt in *; simpl. intro.
    eapply tseq.
    - generalize (MGT1 (kseq p2 k)).
      clear MGT1. intro MGT1.


































  
End Toy.

(* 
Notation "n \ B \ R ⊨ {{ P }} S {{ Q }}" :=
  (valid n B%L R%L P%L S Q%L)
  (at level 74, R at next level, B at next level,
  format "n \  B \  R  ⊨  '[' {{  P  }} '/'  S  '/' {{  Q  }} ']'").
*)
