Section Toy.

  Require Import Utf8.

  Parameter mem: Type.
  Parameter base: Type.
  Parameter sem_base: mem → base → mem → Prop.

  Inductive prog: Type :=
  | pskip
  | pbreak
  | pcall (n: nat): prog
  | pbase (b: base): prog
  | pseq (p1 p2: prog): prog
  | palt (p1 p2: prog): prog
  | ploop (p: prog): prog
  .

  Inductive cont: Type :=
  | kstop
  | kcall (k: cont)
  | kseq (p: prog) (k: cont)
  | kloop (p: prog) (k: cont)
  .

  Parameter pmap: nat -> option prog.

  Definition config: Type :=
    (mem * prog * cont) %type.
  Definition memof (c: config) :=
    fst (fst c).

  Reserved Notation "a ↦ b" (at level 60).
  Inductive step: config → config → Prop :=

  | sbase b m1 m2 k (BASE: sem_base m1 b m2)
    : (m1, pbase b, k) ↦ (m2, pskip, k)

  | scall1 pn m p k (LOOK: pmap pn = Some p)
    : (m, pcall pn, k) ↦ (m, p, kcall k)
  | scall2 m k
    : (m, pskip, kcall k) ↦ (m, pskip, k)

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

  Inductive pspec: Type :=
    mk_pspec (Z: Type) (SPEC: Z → (assn * assn)).
  Definition ctxt: Type :=
    nat → option pspec.

  Definition ctxt_union (C1 C2: ctxt): ctxt :=
    λ pn, match C1 pn with
           | None => C2 pn
           | ospec => ospec
         end.
  Notation "C1 ∪ C2" := (ctxt_union C1 C2) (at level 70).

  Definition pspec_ty (ps: pspec): Type := 
    let (ty, _) := ps in ty.
  Definition pspec_spec ps (z: pspec_ty ps) :=
    match ps return (pspec_ty ps) → (assn * assn) with
        mk_pspec _ spec => spec
    end z.

  (* I is an invariant *)
  Parameter I: assn.

  Inductive triple: ctxt → assn → prog → assn → assn → Prop :=

  | tskip C (A: assn)
    : triple C (A) (pskip) (A) (bottom)

  | tbreak C (B: assn)
    : triple C (B) (pbreak) (bottom) (B)

  | tbase C b (A: assn)
    : triple C (λ m, ∀ m', sem_base m b m' → A m' ∧ I m')
             (pbase b) (A) (bottom)

  | tcall C pn ps z (A1 A2: assn)
          (LOOK: C pn = Some ps)
          (SPEC: pspec_spec ps z = (A1, A2))
    : triple C (A1) (pcall pn) (A2) (bottom)

  | tseq C p1 p2 (A1 A2 A3 B: assn)
         (P1: triple C (A1) (p1) (A2) (B))
         (P2: triple C (A2) (p2) (A3) (B))
    : triple C (A1) (pseq p1 p2) (A3) (B)

  | talt C p1 p2 (A1 A2 B: assn)
         (P1: triple C (A1) (p1) (A2) (B))
         (P2: triple C (A1) (p2) (A2) (B))
    : triple C (A1) (palt p1 p2) (A2) (B)

  | tloop C p (A1 A2: assn)
          (P: triple C (A1) (p) (A1) (A2))
    : triple C (A1) (ploop p) (A2) (bottom)

  | tweak C p (A1 A2 B A1' A2' B': assn)
          (P: triple C (A1) (p) (A2) (B))
          (PRE: ∀ m, A1' m → A1 m)
          (PST: ∀ m, A2 m → A2' m)
          (BRK: ∀ m, B m → B' m)
    : triple C (A1') p (A2') (B')

  | tctxt C C'
          (C'OK: ∀ pn ps p (LOOKP: pmap pn = Some p)
                           (LOOKS: C' pn = Some ps),
                 ∀ z A1 A2,
                   pspec_spec ps z = (A1, A2) →
                   triple (C ∪ C') (A1) (p) (A2) (bottom)
          )
          p (A1 A2 B: assn)
          (P: triple (C ∪ C') (A1) (p) (A2) (B))
    : triple C (A1) (p) (A2) (B)
  .

  
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

  Definition valid_ctxt n (C: ctxt) :=
    ∀ pn p ps (LOOKP: pmap pn = Some p) (LOOKS: C pn = Some ps),
    ∀ z A1 A2 (SPEC: pspec_spec ps z = (A1, A2)),
      valid n (A1) p (A2) (bottom).

  Lemma valid_ctxt_extend n C C'
        (COK: valid_ctxt n C)
        (C'OK: ∀ pn ps p (LOOKP: pmap pn = Some p)
                         (LOOKS: C' pn = Some ps),
               ∀ z A1 A2 (SPEC: pspec_spec ps z = (A1, A2)),
               ∀ n, valid_ctxt n (C ∪ C') →
                    valid (1 + n) (A1) (p) (A2) (bottom)
        ):
    valid_ctxt n (C ∪ C').
  Proof.
    induction n as [n IND] using lt_wf_rec.
    unfold valid_ctxt, ctxt_union.
    intros ? ? ? ?. case_eq (C pn).
    - (* when pn is in C *) 
      intro ps'; intros.
      replace ps' with ps in H by congruence.
      eapply COK; eauto.
    - (* when pn is in C' *)
      intros.
      destruct n.
      + unfold valid; intros.
        replace n' with 0 by omega.
        now apply safe0.
      + eapply C'OK; eauto.
        eapply IND; eauto.
        unfold valid_ctxt in *.
        eauto using valid_le, COK.
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

  Lemma valid_call n C pn ps z A1 A2
        (VALIDC: valid_ctxt n C)
        (LOOKS: C pn = Some ps)
        (SPEC: pspec_spec ps z = (A1, A2)):
    valid (1 + n) (A1) (pcall pn) (A2) (bottom).
  Proof.
    case_eq (pmap pn); unfold valid; intros.
    - (* pn is a valid program reference *)
      step.
      eapply VALIDC; (omega || eauto).
      + intros. step. ale SAFES; assumption.
      + firstorder.
    - (* pn is invalid *) step. congruence.
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

  Lemma valid_weak n p
        (A1 A2 B A1' A2' B': assn)
        (P: valid n (A1) (p) (A2) (B))
        (PRE: ∀ m, A1' m → A1 m)
        (PST: ∀ m, A2 m → A2' m)
        (BRK: ∀ m, B m → B' m):
    valid n (A1') (p) (A2') (B').
  Proof.
    unfold valid; intros.
    apply P; (omega || eauto).
  Qed.

  Theorem soundness C A1 p A2 B:
    triple C (A1) (p) (A2) (B) →
    ∀ n, valid_ctxt n C → valid (1 + n) (A1) (p) (A2) (B).
  Proof.
    induction 1; intros;
    eauto using valid_skip, valid_break, valid_base,
                valid_call, valid_seq, valid_alt,
                valid_loop, valid_weak, valid_ctxt_extend.
  Qed.


  (* Completeness: safe → triple *)

  Ltac pets H := (* step, inverted *)
    match goal with
      | [ |- safe ?n _ ] =>
        generalize (H (S n)); clear H;
        inversion 1 as [|n__ c__ SAFE];
        subst; apply SAFE;
        [ constructor | assumption ]
    end.
      
  Definition mgt p :=
    ∀ k, triple
           (λ m, I m ∧ ∀ n, safe n (m, p, k))
           (p)
           (λ m, I m ∧ ∀ n, safe n (m, pskip, k))
           (λ m, I m ∧ ∀ n, safe n (m, pbreak, k)).

  Lemma mgt_skip:
    mgt (pskip).
  Proof.
    intro.
    eapply tweak; eauto using tskip.
    - intros. exact H.
    - eauto.
    - firstorder.
  Qed.

  Lemma mgt_break:
    mgt (pbreak).
  Proof.
    intro.
    eapply tweak; eauto using tbreak.
    - intros. exact H.
    - firstorder.
    - eauto.
  Qed.

  Lemma mgt_base b:
    mgt (pbase b).
  Proof.
    intro.
    eapply tweak; eauto using tbase.
    - instantiate (1 := (λ m, I m ∧ ∀ n, safe n (m, pskip, k))).
      simpl. intros.
      assert (I m'). {
        replace m' with (memof (m', pskip, k)) by reflexivity.
        destruct H.
        apply (safe_preserve (m, pbase b, k) (m', pskip, k));
          repeat (eauto; econstructor).
      }
      intuition. pets H3; assumption.
    - simpl; eauto.
    - firstorder.
  Qed.
 
  Lemma mgt_seq p1 p2
        (MGT1: mgt p1)
        (MGT2: mgt p2):
    mgt (pseq p1 p2).
  Proof.
    intro.
    eapply tseq.
    - generalize (MGT1 (kseq p2 k)).
      clear MGT1 MGT2. intro MGT1.
      eapply tweak; eauto.
      + simpl. intuition. pets H1.
      + simpl. intuition. pets H1.
    - generalize (MGT2 k).
      clear MGT1 MGT2. intro MGT2.
      eapply tweak; eauto; simpl; eauto.
      simpl. intuition. pets H1.
  Qed.

  Lemma mgt_alt p1 p2
        (MGT1: mgt p1)
        (MGT2: mgt p2):
    mgt (palt p1 p2).
  Proof.
    intro.
    eapply talt.
    - generalize (MGT1 k).
      clear MGT1 MGT2. intro MGT.
      eapply tweak; eauto.
      simpl. intuition. pets H1.
    - (* same proof *)
      generalize (MGT2 k).
      clear MGT1 MGT2. intro MGT.
      eapply tweak; eauto.
      simpl. intuition. pets H1.
  Qed.

  Lemma mgt_loop p
        (MGT: mgt p):
    mgt (ploop p).
  Proof.
    intro.
    eapply tweak. apply tloop.
    generalize (MGT (kloop p k)).
    clear MGT. intro MGT.
    eapply tweak; eauto.
    - simpl. intuition.
      assert (∀ n, safe n (m, ploop p, k))
        by (intro; pets H1).
      pets H.
    - simpl. intuition. pets H1.
    - simpl. intuition. pets H1.
    - firstorder.
  Qed.

  Lemma key0: ∀ p, mgt p.
  Proof.
    induction p;
    eauto using mgt_skip, mgt_break, mgt_base,
                mgt_seq, mgt_alt, mgt_loop.
  Qed.

  Lemma key1 p (X: assn) (MGT: mgt p):
    (∀ m, X m → I m ∧ ∀ n, safe n (m, p, kstop)) →
    triple (X) p (λ _, True) (λ _, True).
  Proof.
    unfold mgt. intros VALIDX.
    eapply tweak; eauto.
    intuition.
  Qed.
    
  Theorem completeness p (X: assn):
    (∀ m, X m → I m ∧ ∀ n, safe n (m, p, kstop)) →
    triple (X) p (λ _, True) (λ _, True).
  Proof. eauto using key0, key1. Qed.
  
End Toy.
