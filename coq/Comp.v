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
    : (m, pskip, kloop p k) ↦ (m, p, kloop p k)
  | sloop3 p m k
    : (m, pbreak, kloop p k) ↦ (m, pskip, k)

  where "a ↦ b" := (step a b).

  Definition assn: Type :=
    mem → Prop.
  Definition bottom: assn :=
    λ _, False.

  Inductive triple: assn → prog → assn → assn → Prop :=

  | tskip (A B: assn)
    : triple (A) (pskip) (A) (B)

  | tbreak (B: assn)
    : triple (B) (pbreak) (bottom) (B)

  | tbase b (A B: assn)
    : let A0 m1 := ∀ m2, sem_base m1 b m2 → A m2
      in triple (A0) (pbase b) (A) (B)

  | tseq p1 p2 (A1 A2 A3 B: assn)
         (P1: triple A1 p1 A2 B)
         (P2: triple A2 p2 A3 B)
    : triple (A1) (pseq p1 p2) (A2) (B)

  | talt p1 p2 (A1 A2 B: assn)
         (P1: triple A1 p1 A2 B)
         (P2: triple A1 p2 A2 B)
    : triple (A1) (palt p1 p2) (A2) (B)

  | tloop p (A1 A2: assn)
          (P: triple A1 p A1 A2)
    : triple (A1) (ploop p) (A2) (bottom)
  .

  Parameter I: assn.
  (* I is an invariant *)

  Definition spec: Type := nat → config → Prop.

  Inductive safe: spec :=
  | safe0 c: safe 0 c
  | safeN n c
          (INV: I (memof c))
          (SAFE: ∀ c' (STEP: c ↦ c'), safe n c')
    : safe (S n) c
  .

  Require Import Arith.
  Require Import Omega.

  Lemma safe_le: (* safe is downward closed *)
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
        * apply INV.
        * intros.
          apply IND; auto with arith.
  Qed.

  Lemma safe_I n c (SAFE: safe (S n) c):
    I (memof c).
  Proof.
    inversion_clear SAFE. exact INV.
  Qed.


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
    apply VALID; (eassumption || omega).
  Qed.
 
  Lemma valid_I n p k
        (A1 A2 B: assn)
        (VALID: valid (S n) (A1) (p) (A2) (B))
        (SAFES: ∀ m, A2 m → safe (S n) (m, pskip, k))
        (SAFEB: ∀ m, B m  → safe (S n) (m, pbreak, k)):
    ∀ m, A1 m → I m.
  Proof.
    intros m A1M.
    replace m with (memof (m, p, k)) by reflexivity.
    eapply safe_I; eauto using VALID.
  Qed.

  
  (* Soundness: triple → valid *)
  
  Lemma valid_skip n (A B: assn):
    valid n (A) (pskip) (A) (B).
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

  Let A0 (A: assn) b m1 :=
    ∀ m2, sem_base m1 b m2 → A m2.

  Ltac step :=
    match goal with
      | [ |- safe ?n _ ] =>
        destruct n;
          [ apply safe0
          | apply safeN;
            [| inversion_clear 1 ]
          ]
    end.

  Ltac ale H :=
    match goal with
      | [ |- safe _ _ ] =>
        eapply safe_le; [apply H|]; try omega
      | [ |- valid ?n _ _ _ _ ] =>
        eapply valid_le; [apply H|]; try omega
    end.  

  Lemma valid_base n b (A B: assn):
    valid n (A0 A b) (pbase b) (A) (B).
  Proof.
    unfold A0, valid; intros.
    step.
    - admit.  (* this could be a reasonable hypothesis of the
                 whole development *)
    - ale SAFES. apply MOK, BASE.
  Qed.

  Section Sequence.
    Lemma safe_skip_kseq n n₁ n₂
          p A1 A2 B (VALID: valid n₁ A1 p A2 B) k
          (SAFES: ∀ m, A2 m → safe (S n₂) (m, pskip, k))
        (SAFEB: ∀ m, B m  → safe (S n₂) (m, pbreak, k))
        m (A1M: A1 m) (LE: n ≤ S n₂ /\ S n₂ ≤ n₁):
      safe n (m, pskip, kseq p k).
    Proof.
      step.
      - eapply valid_I; eauto. ale VALID.
      - ale VALID; eauto; omega.
    Qed.
    
    Lemma safe_break_kseq n n₁ B p k 
          (SAFEB: ∀ m, B m  → safe (S n₁) (m, pbreak, k))
          (LE1: n ≤ S n₁)
          m (BM: B m):
      safe n (m, pbreak, kseq p k).
    Proof.
      step.
      - replace (memof _) with (memof (m, pbreak, k))
          by reflexivity.
        eapply safe_I; eauto.
      - ale SAFEB; assumption.
    Qed.
    
    Lemma valid_seq n p1 p2 A1 A2 A3 B
          (VALID1: valid n (A1) (p1) (A2) (B))
          (VALID2: valid n (A2) (p2) (A3) (B)):
      valid n (A1) (pseq p1 p2) (A3) (B).
    Proof with (omega || eauto); intros.
      unfold valid; intros.
      step.
      - eapply (valid_I n' p1 (kseq p2 k))...
        + ale VALID1.
        + eapply safe_skip_kseq; eauto; omega.
        + eapply safe_break_kseq; eauto.
      - apply VALID1...
        + eapply safe_skip_kseq; eauto; omega.
        + eapply safe_break_kseq; eauto.
    Qed.
  End Sequence.

  Lemma valid_alt n p1 p2 A1 A2 B
        (VALID1: valid n (A1) (p1) (A2) (B))
        (VALID2: valid n (A1) (p2) (A2) (B)):
    valid n (A1) (palt p1 p2) (A2) (B).
  Proof.
    unfold valid; intros.
    step.
    - eapply valid_I; eauto. ale VALID1.
    - ale VALID1; (omega || eauto).
    - ale VALID2; (omega || eauto).
  Qed.

  Lemma valid_loop n p A1 A2
        (VALID: valid n (A1) (p) (A1) (A2)):
    valid n (A1) (ploop p) (A2) (bottom).
  Proof.
    revert p A1 A2 VALID.
    induction n as [n IND] using lt_wf_rec.
    intros; unfold valid; intros.
    step.
    - destruct n as [|n]; [inversion NLE|].
      eapply valid_I.
      eapply (valid_I _ _ (kloop p k)); eauto; intros.
      step.





















  fail.
  
  | tloop p (A1 A2: assn)
          (P: triple A1 p A1 A2)
    : triple (A1) (ploop p) (A2) (bottom)
  .

End Toy.


(* 
Notation "n \ B \ R ⊨ {{ P }} S {{ Q }}" :=
  (valid n B%L R%L P%L S Q%L)
  (at level 74, R at next level, B at next level,
  format "n \  B \  R  ⊨  '[' {{  P  }} '/'  S  '/' {{  Q  }} ']'").
*)
