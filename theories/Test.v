Require Import Unicode.Utf8.
Require Import Relations.Relation_Operators.
Require Import Program.Equality List Lia.
Require Import Autosubst.Autosubst.

Print rename.
Print subst.

Inductive type : Type :=
| Bool
| Arr (t1 t2 : type).
Notation "S ⇒ T" := (Arr S T) (at level 80, right associativity).

Inductive term : Type :=
| TTrue
| TFalse
| TIf (e1 e2 e3: term)
| TVar (x : var)
| TLam (T : type) (e : {bind term})
| TApp (f e : term).

#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term → Prop :=
| value_true : value TTrue
| value_false : value TFalse
| value_lam : forall T e, value (TLam T e).

#[export] Hint Constructors value : core.

Reserved Notation "e '-->' e'" (at level 80).
Inductive step : term -> term -> Prop :=
| step_beta : ∀ T e v u, value v → u = e.[v .: ids] → TApp (TLam T e) v --> u
| step_app1 : ∀ e e' e2, e --> e' → TApp e e2 --> TApp e' e2
(* | step_app2 : ∀ T e e2 e2', e2 --> e2' → TApp (TLam T e) e2 --> TApp (TLam T e) e2' *)
| step_app2 : ∀ v e2 e2', value v → e2 --> e2' → TApp v e2 --> TApp v e2'
| step_if : ∀ e e' e1 e2, e --> e' → TIf e e1 e2 --> TIf e' e1 e2
| step_ifT : ∀ e1 e2, TIf TTrue e1 e2 --> e1
| step_ifF : ∀ e1 e2, TIf TFalse e1 e2 --> e2
where "e '-->' e'" := (step e e') : type_scope.

#[export] Hint Constructors step : core.

Definition multistep := clos_refl_trans_1n _ step.
Notation "e '-->*' e'" := (multistep e e') (at level 80).
#[export] Hint Constructors clos_refl_trans_1n : core.

Section Examples.
  Definition e_id := TLam Bool (TVar 0).
  Goal TApp e_id TTrue --> TTrue.
    constructor. apply value_true.
    simpl. reflexivity.
  Qed.

End Examples.

Section Deterministic.
  Definition nf (t : term) := ∀ t', ¬ (t --> t').
  Lemma value_is_nf : ∀ v, value v → nf v.
  Proof.
    intros v Hv.
    destruct Hv; intros t' Hstep; inversion Hstep.
  Qed.

  Ltac value_step :=
    match goal with
    | [ Hv : TLam ?T ?e --> _ |- _ ] => inversion Hv
    | [ Hv : TTrue --> _ |- _ ] => inversion Hv
    | [ Hv : TFalse --> _ |- _ ] => inversion Hv
    | [ Hv : value ?v, Hstep : ?v --> ?e  |- _ ] => exfalso; apply (value_is_nf _ Hv _ Hstep)
    end.

  Theorem step_deterministic : ∀ {s t₁ t₂ : term},
      s --> t₁ →
      s --> t₂ →
      t₁ = t₂.
  Proof.
    intros s t₁ t₂ Ht₁.
    generalize dependent t₂.
    induction Ht₁; intros t₂ Ht₂; inversion Ht₂; subst; auto; try value_step; solve [f_equal; apply IHHt₁; auto].
  Qed.
    (*
    - inversion Ht₂; subst. reflexivity. value_step. value_step.
    - inversion Ht₂; subst. value_step. rewrite (IHHt₁ e'0). reflexivity. assumption. value_step.
    - inversion Ht₂; subst. value_step. value_step. f_equal. auto.
    - inversion Ht₂; subst; auto; try value_step. f_equal. auto.
    - inversion Ht₂; subst; auto; try value_step.
    - inversion Ht₂; subst; auto; try value_step.
    *)

  Corollary confluence : ∀ {t u v : term},
      t -->* u →
      t -->* v →
      ∃ z, u -->* z ∧ v -->* z.
  Proof.
    intros t u v Hu.
    generalize dependent v.
    induction Hu; intros v Hv.
    - exists v; split. auto. constructor.
    - destruct Hv.
      * exists z. split. constructor. econstructor. apply H. assumption.
      * assert (Hy : y0 = y). { eapply step_deterministic. apply H0. assumption. }
        rewrite Hy in Hv.
        apply IHHu. apply Hv.
  Qed.
End Deterministic.



Definition context := var → option type.
Definition empty : context := fun _ => None.

#[export] Instance Rename_ctx : Rename context.
Proof.
  unfold Rename.
  intros ρ Γ x.
  exact (Γ (ρ x)).
Defined.

Print Rename.
Print Subst.
Definition shift_ctx : type → context → context :=
  fun T Γ x => match x with
               | O => Some T
               | S n => Γ n
               end.

Reserved Notation "Γ '⊢' e '∈' T'" (at level 85).
Inductive has_type : context → term → type → Prop :=
| type_true : ∀ Γ, Γ ⊢ TTrue ∈ Bool
| type_false : ∀ Γ, Γ ⊢ TFalse ∈ Bool
| type_lam : ∀ Γ e τ₁ τ₂, (shift_ctx τ₁ Γ) ⊢ e ∈ τ₂ → Γ ⊢ TLam τ₁ e ∈ τ₁ ⇒ τ₂
| type_app : ∀ Γ f e τ τ₂, Γ ⊢ f ∈ τ₂ ⇒ τ → Γ ⊢ e ∈ τ₂ → Γ ⊢ TApp f e ∈ τ
| type_if : ∀ Γ e e₁ e₂ τ, Γ ⊢ e ∈ Bool → Γ ⊢ e₁ ∈ τ → Γ ⊢ e₂ ∈ τ → Γ ⊢ TIf e e₁ e₂ ∈ τ
where "Γ '⊢' e '∈' T" := (has_type Γ e T).

Check subst_comp.
