Section Toy.

  Require Import Utf8.

  Parameter mem: Type.
  Parameter base: Type.
  Parameter sem_base: mem → base → mem → Prop.


  (* Syntax *)

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


  (* Semantics *)

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


  (* Assertions and derivability *)
  
  Definition assn: Type :=
    mem → Prop.
  Definition bottom: assn := λ _, False.
  Definition top: assn    := λ _, True.

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
          (LOOKS: C pn = Some ps)
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
                   triple (C ∪ C') (A1) (p) (A2) (top)
          )
          p (A1 A2 B: assn)
          (P: triple (C ∪ C') (A1) (p) (A2) (B))
    : triple C (A1) (p) (A2) (B)
  .

  Lemma ctxt_extensionality:
    ∀ C p A1 A2 B
      (TRIPLE: triple C A1 p A2 B)
      C' (CEQ: ∀ pn, C pn = C' pn),
    triple C' A1 p A2 B.
  Proof.
    induction 1; econstructor; eauto.
    - (* tcall *) congruence.
    - (* tctxt *)
      assert (U: ∀ pn, (C ∪ C') pn = (C'0 ∪ C') pn). {
        intros; unfold ctxt_union.
        case_eq (C pn); case_eq (C'0 pn);
        intros; congruence.
      }
      eapply (tctxt _ C'); intros;
      eauto using H, IHTRIPLE.
  Qed.

  
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
      valid n (A1) p (A2) (top).

  Lemma valid_ctxt_extend n C C'
        (COK: valid_ctxt n C)
        (C'OK: ∀ pn ps p (LOOKP: pmap pn = Some p)
                         (LOOKS: C' pn = Some ps),
               ∀ z A1 A2 (SPEC: pspec_spec ps z = (A1, A2)),
               ∀ n, valid_ctxt n (C ∪ C') →
                    valid (1 + n) (A1) (p) (A2) (top)
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
      + intros. step.
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

  Definition mga p k := λ m, I m ∧ ∀ n, safe n (m, p, k).
  Definition mgpspec p :=
    mk_pspec (cont) (λ k, (mga p k, mga pskip k)).
  Definition mgc: ctxt :=
    λ pn, match pmap pn with
            | Some p => Some (mgpspec p)
            | None => None
          end.

  Lemma mga_step p p' k k' m m'
        (MGA: mga p k m)
        (STEP: (m, p, k) ↦ (m', p', k'))
        (INV: I m'):
    mga p' k' m'.
  Proof.
    unfold mga in *; intuition.
    generalize (H0 (S n)).
    inversion 1; subst.
    apply SAFE; assumption.
  Qed.

  Ltac pets H :=
    eapply (mga_step _ _ _ _ _ _ H);
    (econstructor || eauto using (proj1 H)).

  Definition mgt p :=
    ∀ k, triple mgc (mga p k) (p) (mga pskip k) (mga pbreak k).

  Lemma mgt_skip:
    mgt (pskip).
  Proof.
    intro.
    eapply tweak; eauto using tskip.
    firstorder.
  Qed.

  Lemma mgt_break:
    mgt (pbreak).
  Proof.
    intro.
    eapply tweak; eauto using tbreak.
    firstorder.
  Qed.

  Lemma mgt_base b:
    mgt (pbase b).
  Proof.
    intro.
    eapply tweak; eauto using tbase.
    - simpl. intros.
      assert (I m'). {
        replace m' with (memof (m', pskip, k)) by reflexivity.
        destruct H.
        apply (safe_preserve (m, pbase b, k) (m', pskip, k));
          repeat (eauto; econstructor).
      }
      intuition. pets H. assumption.
    - firstorder.
  Qed.

  Lemma mgt_call pn (PNOK: pmap pn ≠ None):
    mgt (pcall pn).
  Proof.
    intro.
    case_eq (pmap pn); [intros p PN | congruence].
    eapply tweak.
    eapply tcall with (ps := mgpspec p) (z := kcall k).
    - unfold mgc; rewrite PN; reflexivity.
    - reflexivity.
    - intros ? MGA; pets MGA; assumption.
    - intros ? MGA; pets MGA; assumption.
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
      + intros ? MGA; pets MGA.
      + intros ? MGA; pets MGA.
    - generalize (MGT2 k).
      clear MGT1 MGT2. intro MGT2.
      eapply tweak; eauto; simpl; eauto.
      intros ? MGA; pets MGA.
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
      simpl. intros ? MGA. pets MGA.
    - (* same proof *)
      generalize (MGT2 k).
      clear MGT1 MGT2. intro MGT.
      eapply tweak; eauto.
      intros ? MGA; pets MGA.
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
      assert (MGA: mga (ploop p) k m)
        by (pets H).
      pets MGA.
    - intros ? MGA; pets MGA.
    - intros ? MGA; pets MGA.
    - firstorder.
  Qed.

  Fixpoint defined p :=
    match p with
      | pseq p1 p2 => defined p1 ∧ defined p2
      | palt p1 p2 => defined p1 ∧ defined p2
      | ploop p => defined p
      | pcall pn => pmap pn <> None
      | _ => True
    end.

  Lemma key0: ∀ p, defined p → mgt p.
  Proof.
    induction p; simpl; intuition;
    eauto using mgt_skip, mgt_break, mgt_base,
                mgt_call, mgt_seq, mgt_alt,
                mgt_loop.
  Qed.

  Theorem completeness p (X: assn)
          (DEFM: ∀ pn p, pmap pn = Some p → defined p)
          (DEFP: defined p):
    (∀ m, X m → I m ∧ ∀ n, safe n (m, p, kstop)) →
    triple (λ _, None) (X) p (top) (top).
  Proof.
    unfold mgt. intros VALIDX.
    apply tctxt with (C' := mgc).
    - intros ? ? ? ? ?.
      unfold mgc in LOOKS.
      rewrite LOOKP in LOOKS.
      injection LOOKS.
      intros ? ? ? ? SPEC; subst.
      simpl in SPEC; injection SPEC;
      clear SPEC; intros; subst.
      apply ctxt_extensionality with (C := mgc).
      eapply tweak. apply key0.
      eauto using DEFM.
      eauto. eauto. firstorder.
      unfold ctxt_union. intros; simpl.
      reflexivity.
    - apply ctxt_extensionality with (C := mgc).
      eapply tweak. apply key0.
      assumption. eauto. firstorder. firstorder.
      unfold ctxt_union. intros; simpl.
      reflexivity.
  Qed.
  
End Toy.
