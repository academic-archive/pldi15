(* An abstract Clight language with
 * semantics instrumented to keep track
 * of resource consumption.
 *)
Require Export Utf8_core.

(* The Syntax. *)
Class BaseSyntax (fid var expr: Type) :=
  { fid_eq: forall (f f': fid), { f = f' } + { f ≠ f' } }.

Inductive stmt `{Syn: BaseSyntax}: Type :=
  | SSkip
  | SGSet (x: expr) (y: expr)
  | SLSet (v: var) (x: expr)
  | SReturn (r: option expr)
  | SBreak
  | SCall (v: option var) (f: fid) (l: list expr)
  | SSeq (s1 s2: stmt)
  | SIf (b: expr) (st sf: stmt)
  | SLoop (s: stmt).


(* Resource Events in a Program. *)
Inductive revent `{Syn: BaseSyntax} :=
  | EEvall: expr → revent
  | EEvalr: expr → revent
  | EGSet: revent
  | ELSet: revent
  | ECall: fid → revent
  | EReturn: fid → revent
  | EBreak: revent
  | ECond: bool → revent
  | ESeq: revent
  | ELoop: revent.


(* The Small-Step Semantics of Programs. *)
Class BaseSemantics `(Syn: BaseSyntax) (genv lval rval mem stack: Type) :=
  (* global environment *)
  { find_func: genv → fid → option stmt
  (* values *)
  ; val_bool: rval → bool → Prop
  (* memory *)
  ; mstate: Type := (stack * mem)%type
  ; heap_set: genv → lval → rval → mem → mem → Prop
  ; stack_set: genv → var → rval → stack → stack → Prop
  (* functions *)
  ; fun_init: genv → fid → list rval → stack → Prop
  ; fun_ret: genv → fid → option rval → option rval → Prop
  (* expressions *)
  ; evall: genv → mstate → expr → lval → Prop
  ; evalr: genv → mstate → expr → rval → Prop
  }.

Section SEMANTICS.

Inductive cont `{Sem: BaseSemantics}: Type :=
  | KCall (f: fid) (v: option var) (stk: stack) (k: cont)
  | KSeq (s: stmt) (k: cont)
  | KLoop (s: stmt) (k: cont)
  | KStop.

Context `{Sem: BaseSemantics}.
Open Scope list_scope.

Definition stack_seto (ge: genv) (vo: option var) (vx: rval) (s s': stack): Prop :=
  match vo with
  | Some v => stack_set ge v vx s s'
  | None => s = s'
  end.

Inductive eval_list (ge: genv) (m: mstate): list expr → list rval → Prop :=
  | evall_nil: eval_list ge m nil nil
  | evall_cons e v es vs:
      evalr ge m e v →
      eval_list ge m es vs →
      eval_list ge m (e :: es) (v :: vs).

Inductive evalo (ge: genv) (m: mstate): option expr → option rval → Prop :=
  | evalo_Some e v:
    evalr ge m e v →
    evalo ge m (Some e) (Some v)
  | evalo_None:
    evalo ge m None None.

Section STEP.
Variable ge: genv.

(* Caller's stack modification made after a return. *)
Inductive ret_stack (f: fid): option var → option rval → stack → stack → Prop :=
  | ret_stack_some v vr vr' σ σ':
      fun_ret ge f (Some vr) (Some vr') →
      stack_seto ge v vr' σ σ' →
      ret_stack f v (Some vr) σ σ'
  | ret_stack_none σ:
      fun_ret ge f None None →
      ret_stack f None None σ σ.

(* The step relation for program configurations. *)
Reserved Notation "T ▷ S1 ↦ S2" (at level  74).
Inductive step_base:
  list revent → (stmt * cont * mstate) → (stmt * cont * mstate) → Prop :=

  | step_GSet x lx y vy k σ θ θ':
    evall ge (σ, θ) x lx →
    evalr ge (σ, θ) y vy →
    heap_set ge lx vy θ θ' →
    (EEvall x :: EEvalr y :: EGSet :: nil) ▷
      (SGSet x y, k, (σ, θ)) ↦
      (SSkip, k, (σ, θ'))

  | step_LSet v x vx k σ θ σ':
    evalr ge (σ, θ) x vx →
    stack_set ge v vx σ σ' →
    (EEvalr x :: ELSet :: nil) ▷
      (SLSet v x, k, (σ, θ)) ↦
      (SSkip, k, (σ', θ))

  | step_Return_Call r vr f v σ' k σ θ σ'':
    evalo ge (σ, θ) r vr →
    ret_stack f v vr σ' σ'' →
    (EReturn f :: nil) ▷
      (SReturn r, KCall f v σ' k, (σ, θ)) ↦
      (SSkip, k, (σ'', θ))

  | step_Return_Seq r S k m:
    nil ▷
      (SReturn r, KSeq S k, m) ↦
      (SReturn r, k, m)

  | step_Return_Loop r S k m:
    nil ▷
      (SReturn r, KLoop S k, m) ↦
      (SReturn r, k, m)

  | step_Break_Loop S k m:
    (EBreak :: nil) ▷
      (SBreak, KLoop S k, m) ↦
      (SSkip, k, m)

  | step_Break_Seq S k m:
    nil ▷
      (SBreak, KSeq S k, m) ↦
      (SBreak, k, m)

  | step_Call v f l vl S k σ θ σ':
    find_func ge f = Some S →
    eval_list ge (σ, θ) l vl →
    fun_init ge f vl σ' →
    (ECall f :: nil) ▷
      (SCall v f l, k, (σ, θ)) ↦
      (S, KCall f v σ k, (σ', θ))

  | step_Skip_Seq S k m:
    (ESeq :: nil) ▷
      (SSkip, KSeq S k, m) ↦
      (S, k, m)

  | step_Seq S1 S2 k c:
    nil ▷
      (SSeq S1 S2, k, c) ↦
      (S1, KSeq S2 k, c)

  | step_If t vt b St Sf k m:
    evalr ge m t vt →
    val_bool vt b →
    (EEvalr t :: ECond b :: nil) ▷
      (SIf t St Sf, k, m) ↦
      (if b then St else Sf, k, m)

  | step_Skip_Loop S k m:
    (ELoop :: nil) ▷
      (SSkip, KLoop S k, m) ↦
      (SLoop S, k, m)

  | step_Loop S k m:
    nil ▷
      (SLoop S, k, m) ↦
      (S, KLoop S k, m)

where "T ▷ S1 ↦ S2" := (step_base T S1 S2).

End STEP.
End SEMANTICS.
