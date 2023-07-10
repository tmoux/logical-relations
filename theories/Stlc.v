Require Import Unicode.Utf8.
Require Import Relations.Relation_Operators.
Require Import List.
Require Import Autosubst.Autosubst.

(* We present a simple proof of type safety for STLC using logical relations.
   We use the Autosubst library to handle binding/substitutions.
   It also makes it easy to state and prove details about substitutions in the fundamental lemma. *)

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

(* Autosubst black magic. *)
#[export] Instance Ids_term : Ids term. derive. Defined.
#[export] Instance Rename_term : Rename term. derive. Defined.
#[export] Instance Subst_term : Subst term. derive. Defined.
#[export] Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term → Prop :=
| value_true : value TTrue
| value_false : value TFalse
| value_lam : forall T e, value (TLam T e).
#[export] Hint Constructors value : core.

Lemma value_dec : forall v, value v ∨ ¬ (value v).
Proof.
  destruct v; solve [auto; right; intros H; inversion H].
Qed.

Reserved Notation "e '-->' e'" (at level 80).
Inductive step : term -> term -> Prop :=
| step_beta : ∀ T e v u, value v → u = e.[v .: ids] → TApp (TLam T e) v --> u
| step_app1 : ∀ e e' e2, e --> e' → TApp e e2 --> TApp e' e2
| step_app2 : ∀ v e2 e2', value v → e2 --> e2' → TApp v e2 --> TApp v e2'
| step_if : ∀ e e' e1 e2, e --> e' → TIf e e1 e2 --> TIf e' e1 e2
| step_ifT : ∀ e1 e2, TIf TTrue e1 e2 --> e1
| step_ifF : ∀ e1 e2, TIf TFalse e1 e2 --> e2
where "e '-->' e'" := (step e e') : type_scope.
#[export] Hint Constructors step : core.

Definition multistep := clos_refl_trans_1n _ step.
Notation "e '-->*' e'" := (multistep e e') (at level 80).
#[export] Hint Constructors clos_refl_trans_1n : core.

Lemma multistep_step : ∀ x y, x --> y → x -->* y.
Proof.
  intros. econstructor; eauto.
Qed.
#[export] Hint Resolve multistep_step : core.

Lemma multistep_trans : ∀ x y z, x -->* y → y -->* z → x -->* z.
Proof.
  intros x y z H.
  induction H; intros; auto.
  econstructor. apply H. apply IHclos_refl_trans_1n; auto.
Qed.

Lemma if_cond_cong : ∀ e1 e2 e3 e1', e1 -->* e1' → TIf e1 e2 e3 -->* TIf e1' e2 e3.
Proof.
  intros ? ? ? ? H.
  induction H; auto; [constructor |].
  econstructor; [constructor; apply H | auto].
Qed.

Lemma app_cong1 : ∀ e1 e2 e1', e1 -->* e1' → TApp e1 e2 -->* TApp e1' e2.
Proof.
  intros ? ? ? H.
  induction H; [constructor |].
  econstructor; [constructor; apply H | auto].
Qed.

Lemma app_cong2 : ∀ τ e1 e2 e2', e2 -->* e2' → TApp (TLam τ e1) e2 -->* TApp (TLam τ e1) e2'.
Proof.
  intros ? ? ? ? H.
  induction H; [constructor |].
  econstructor; [apply step_app2; [constructor | apply H] | auto].
Qed.

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

Lemma value_multistep : ∀ {v v'}, value v → v -->* v' → v' = v.
Proof.
  intros v v' H1 H2.
  inversion H2; [auto | value_step].
Qed.

Definition irred (e : term) := forall e', ¬ (e --> e').
Ltac irred_step :=
  match goal with
  | [ H : irred ?e, Hstep : ?e --> ?e' |- _ ] => exfalso; apply H in Hstep; assumption
  end.

Lemma irred_dec : ∀ e, (∃ e', e --> e') ∨ irred e.
Proof.
  induction e; try solve [right; intros ? H; inversion H; value_step].
  - destruct e1; try solve [left; eexists; auto];
      repeat (destruct IHe1 as [[e1' ?] | ?]; [
            left; eexists; apply step_if; apply H |
      right; intros e' Hstep; inversion Hstep; subst; irred_step ]).
  - destruct IHe1 as [[e1' ?] | ?].
    left. eexists. constructor. apply H.
    destruct IHe2 as [[e2' ?] | ?].
    destruct (value_dec e1).
    * left. eexists. apply step_app2. apply H1. apply H0.
    * right. intros e' Hstep. inversion Hstep; subst. value_step. irred_step. apply H1. assumption.
    * destruct (value_dec e1).
      destruct H1; try (right; intros e' Hstep; inversion Hstep; subst; irred_step).
    + destruct (value_dec e2).
      ++ left. exists e.[e2/]. constructor; auto.
      ++ right. intros e' Hstep. inversion Hstep; subst. auto. inversion H5. irred_step.
    + right. intros e' Hstep. inversion Hstep; subst. apply H1. constructor. irred_step. irred_step.
Qed.

Section Deterministic.
  Theorem step_deterministic : ∀ {s t₁ t₂ : term},
      s --> t₁ → s --> t₂ → t₁ = t₂.
  Proof.
    intros s t₁ t₂ Ht₁.
    generalize dependent t₂.
    induction Ht₁; intros t₂ Ht₂; inversion Ht₂; subst; auto; try value_step; solve [f_equal; apply IHHt₁; auto].
  Qed.

  Corollary confluence : ∀ {t u v : term},
      t -->* u → t -->* v → ∃ z, u -->* z ∧ v -->* z.
  Proof.
    intros t u v Hu.
    generalize dependent v.
    induction Hu; intros v Hv.
    - exists v; split; [auto | constructor].
    - destruct Hv.
      * exists z. split; [constructor | econstructor; [apply H | assumption]].
      * replace y0 with y in *. auto.
        eapply step_deterministic; [apply H | assumption].
  Qed.

  Corollary irred_unique : ∀ {a b c : term}, a -->* b → a -->* c → irred b → c -->* b.
  Proof.
    intros a b c Hab Hac Hb.
    destruct (confluence Hab Hac) as [z [Hbz Hcz]].
    inversion Hbz; subst; [auto | irred_step].
  Qed.
End Deterministic.

(* A typing context is just represented as a list of types, where the i'th type is the type of the i'th debrujin index. *)
Definition context := list type.
Definition empty : context := nil.

Definition lookup : context → nat → option type := @nth_error type.

Reserved Notation "Γ '⊢' e '∈' T'" (at level 85).
Inductive has_type : context → term → type → Prop :=
| type_var : ∀ Γ x τ, lookup Γ x = Some τ → Γ ⊢ TVar x ∈ τ
| type_true : ∀ Γ, Γ ⊢ TTrue ∈ Bool
| type_false : ∀ Γ, Γ ⊢ TFalse ∈ Bool
| type_lam : ∀ Γ e τ₁ τ₂, (τ₁ :: Γ) ⊢ e ∈ τ₂ → Γ ⊢ TLam τ₁ e ∈ τ₁ ⇒ τ₂
| type_app : ∀ Γ f e τ τ₂, Γ ⊢ f ∈ τ₂ ⇒ τ → Γ ⊢ e ∈ τ₂ → Γ ⊢ TApp f e ∈ τ
| type_if : ∀ Γ e e₁ e₂ τ, Γ ⊢ e ∈ Bool → Γ ⊢ e₁ ∈ τ → Γ ⊢ e₂ ∈ τ → Γ ⊢ TIf e e₁ e₂ ∈ τ
where "Γ '⊢' e '∈' T" := (has_type Γ e T).
Notation "'⊢' e '∈' T" := (empty ⊢ e ∈ T) (at level 85).

Section TypeSafety.
  (* The key idea behind using logical relations here is that we want to show if a term t is syntactically well-typed, then it is "safe" (does not get stuck).
     Instead of proving progress/preservation theorems, we develop the notion of a term being semantically well-typed, which is carefully designed to easily imply the type safety result.
     The main effort is then proving the fundamental lemma, i.e., any syntactically well-typed term is also semantically well-typed. *)

  (* A term is _safe_ if for any term e' that it can step to, either e' is a value of e' can make another step. *)
  Definition safe (e : term) := forall e', e -->* e' → value e' ∨ ∃ e'', e' --> e''.

  (* Value and expression semantic interpretations are functions from term to Prop paramaterized by a type. Intuitively, they represent sets of terms that "behave" like values/expressions of a given type. *)
  (* The easiest way to define these is to avoid mutual recursion altogether, since Coq's termination checker isn't smart enough to see that this is well-founded. *)
  Fixpoint sem_value (T : type) : term → Prop :=
    match T with
    | Bool => fun t => t = TTrue ∨ t = TFalse
    | τ₁ ⇒ τ₂ => fun t => ∃ e, t = TLam τ₁ e ∧ (∀ v, sem_value τ₁ v →
                                                     (∀ e', e.[v/] -->* e' → irred e' → sem_value τ₂ e'))
    end.
  Definition sem_expr (τ : type) : term → Prop :=
    fun e => ∀ e', e -->* e' → irred e' → sem_value τ e'.

  Lemma sem_value_arr : ∀ τ₁ τ₂ t, sem_value (τ₁ ⇒ τ₂) t = ∃ e, t = TLam τ₁ e ∧ (∀ v, sem_value τ₁ v → sem_expr τ₂ e.[v/]).
  Proof.
    reflexivity.
  Qed.

  Notation "v '∈' '𝓥⟦' τ '⟧'" := (sem_value τ v) (at level 80).
  Notation "e '∈' '𝓔⟦' τ '⟧'" := (sem_expr τ e) (at level 80).

  Lemma sem_value_is_value : ∀ v τ, v ∈ 𝓥⟦ τ ⟧ → value v.
  Proof.
    intros v τ H.
    destruct τ.
    - destruct H; rewrite H; auto.
    - destruct H as [? [H ?]]; rewrite H; auto.
  Qed.

  Lemma sem_val_is_sem_expr : forall v τ, v ∈ 𝓥⟦ τ ⟧ → v ∈ 𝓔⟦ τ ⟧.
  Proof.
    intros v τ H.
    destruct τ.
    - destruct H; intros e' Hstep; subst; apply value_multistep in Hstep; subst; simpl; auto.
    - destruct H as [e [? ?]].
      subst.
      intros e' Hstep. apply value_multistep in Hstep; subst; simpl; auto.
      eexists; split; auto.
  Qed.

  (* A substitution is just a function var → term.
     A _valid substitution_ is inductively defined with respect to a context Γ in the natural way (γ is valid if it maps all variables in Γ to semantic values). *)
  Inductive valid_subst : context → (var → term) → Prop :=
  | subst_empty : valid_subst empty ids
  | subst_cons : ∀ Γ γ v τ, valid_subst Γ γ → v ∈ 𝓥⟦ τ ⟧ → valid_subst (τ :: Γ) (v .: γ).
  #[local] Hint Constructors valid_subst : core.

  Lemma valid_subst_var : ∀ Γ γ, valid_subst Γ γ → ∀ x τ, lookup Γ x = Some τ → γ x ∈ 𝓥⟦ τ ⟧.
  Proof.
    intros Γ γ H.
    induction H; intros.
    - destruct x; simpl in *; discriminate.
    - induction x. inversion H1. subst. assumption.
      apply IHvalid_subst. assumption.
  Qed.

  (* Finally, a (possibly open) term t is semantically well typed if for any valid substitution γ, γ(t) ∈ 𝓔⟦ τ ⟧. *)
  Definition sem_has_type (Γ : context) (e : term) (τ : type) :=
    ∀ (γ : var → term), valid_subst Γ γ → e.[γ] ∈ 𝓔⟦ τ ⟧.
  Notation "Γ '⊧' e '∈' τ" := (sem_has_type Γ e τ) (at level 80).
  Notation "'⊧' e '∈' T" := (empty ⊧ e ∈ T) (at level 85).

  (* We need a series of lemmas that state that if an elimination form terminates, then its subexpressions must necessarily terminate as well.
      This clearly relies on the determinism of the step relation.
      The induction hypothesis is tricky; inducting on the Hif doesn't seem to work. Instead we write it using a fixpoint, but we need to be careful to ensure the recursion is well founded. *)
  Fixpoint tif_lemma (e' e2 e3 : term) (H : irred e') (e1 : term) (Hif : TIf e1 e2 e3 -->* e') : ∃ e1', e1 -->* e1' ∧ irred e1'.
  Proof.
    destruct Hif.
    - exists e1. split. constructor.
      intros e1' Hstep.
      unfold irred in H. specialize H with (TIf e1' e2 e3). auto using H.
    - destruct (irred_dec e1).
      * destruct H1 as [e1' H1]. specialize tif_lemma with z e2 e3 e1'.
        apply tif_lemma in H.
        destruct H as [e1'' [? ?]].
        exists e1''. split; [| auto].
        econstructor; [apply H1 | ]; auto.
        replace y with (TIf e1' e2 e3) in *; [ | apply (@step_deterministic (TIf e1 e2 e3))]; auto.
      * exists e1; split; [constructor | auto].
  Qed.

  Fixpoint app_lemma1 {e1 e2 e' : term} (He' : irred e') (H : TApp e1 e2 -->* e') : ∃ e1', e1 -->* e1' ∧ irred e1'.
  Proof.
    destruct H.
    - exists e1. split. constructor.
      intros e1' Hstep.
      unfold irred in He'. specialize He' with (TApp e1' e2). auto.
    - destruct (irred_dec e1).
      * destruct H1 as [e1' H1]. specialize app_lemma1 with e1' e2 z.
        apply app_lemma1 in He'.
        destruct He' as [e1'' [? ?]].
        exists e1''. split; auto.
        econstructor; [apply H1 |]; auto.
        replace y with (TApp e1' e2) in *; [ | apply (@step_deterministic (TApp e1 e2))]; auto.
      * exists e1; split; [constructor | auto].
  Qed.

  Fixpoint app_lemma2 {τ} {e e2 e' : term} (He' : irred e') (H : TApp (TLam τ e) e2 -->* e') : ∃ e2', e2 -->* e2' ∧ irred e2'.
  Proof.
    destruct H.
    - exists e2. split. constructor.
      intros e2' Hstep.
      unfold irred in He'. specialize He' with (TApp (TLam τ e) e2'). auto.
    - destruct (irred_dec e2).
      * destruct H1 as [e2' H1]. specialize app_lemma2 with τ e e2' z.
        apply app_lemma2 in He'.
        destruct He' as [e2'' [? ?]].
        exists e2''. split; auto.
      + econstructor. apply H1. assumption.
      + replace y with (TApp (TLam τ e) e2') in *; [ | apply (@step_deterministic (TApp (TLam τ e) e2)) ]; auto.
        * exists e2. split. constructor. auto.
  Qed.

  (* To prove the fundamental lemma, induct on the typing derivation.
     The main challenges are proving the lambda and elimination forms cases.
     The App/If cases are mostly symbol pushing, using the subexpression-termination lemmas stated above.
     The lambda case pretty much follows the proof in the lecture notes. *)
  Lemma fund_lemma : ∀ e τ, ⊢ e ∈ τ → ⊧ e ∈ τ.
  Proof.
    intros e τ He.
    induction He; intros γ Hγ; simpl.
    - (* Var case *) eauto using sem_val_is_sem_expr, valid_subst_var.
    - (* True case *) apply sem_val_is_sem_expr; simpl; auto.
    - (* False case *) apply sem_val_is_sem_expr; simpl; auto.
    - (* Lambda case *) intros e' Hstep.
      rewrite (value_multistep (value_lam _ _) Hstep).
      rewrite sem_value_arr.
      eexists; split; auto.
      intros v Hv.
      unfold sem_has_type in IHHe.
      specialize IHHe with (v .: γ).
      replace e.[up γ].[v/] with e.[v .: γ]; [| autosubst].
      apply IHHe; auto.

    - (* App case *) unfold sem_has_type in IHHe1, IHHe2.
      specialize IHHe1 with γ. specialize IHHe2 with γ.
      intros e' Hstep He'.
      cut (∃ e'', e'' -->* e' ∧ e'' ∈ 𝓔⟦ τ ⟧); [intros [e'' [? ?]]; auto |].
      destruct (app_lemma1 He' Hstep) as [f' [H1 H2]].
      assert (TApp f.[γ] e.[γ] -->* TApp f' e.[γ]). { apply app_cong1; auto. }
      unfold sem_expr in IHHe1. specialize IHHe1 with f'.
      rewrite sem_value_arr in IHHe1.
      destruct IHHe1 as [f'' [Hf' Hf'']]; auto. clear H1. clear H2.
      subst.
      assert (TApp (TLam τ₂ f'') e.[γ] -->* e'). { eapply irred_unique; [apply Hstep | |]; auto. }
      destruct (app_lemma2 He' H0) as [e2' [? ?]].
      unfold sem_expr in IHHe2.
      specialize IHHe2 with e2'.
      exists (f''.[e2'/]); split.
      + eapply irred_unique; eauto.
        apply multistep_trans with (TApp (TLam τ₂ f'') e2').
        apply app_cong2; auto.
        econstructor; auto. constructor; [eapply sem_value_is_value; eauto | reflexivity].
      + apply Hf''. apply IHHe2; auto.

    - (* If case *) unfold sem_has_type in IHHe1, IHHe2, IHHe3.
      specialize IHHe1 with γ.
      intros e' Hstep He'.
      unfold sem_expr in IHHe1.
      destruct (tif_lemma _ _ _ He' _ Hstep) as [e1' [Hif1 Hif2]].
      assert (TIf e.[γ] e₁.[γ] e₂.[γ] -->* TIf e1' e₁.[γ] e₂.[γ]).
      { auto using if_cond_cong. }
      simpl in IHHe1.
      destruct (IHHe1 Hγ e1') as [? | ?]; auto; subst.
      * assert (e₁.[γ] -->* e').
        { eapply irred_unique; [| | auto].
          apply Hstep.
          apply multistep_trans with (TIf TTrue e₁.[γ] e₂.[γ]); auto. }
        eapply IHHe2; eauto.
      * assert (e₂.[γ] -->* e').
        { eapply irred_unique; [| | auto].
          apply Hstep.
          apply multistep_trans with (TIf TFalse e₁.[γ] e₂.[γ]); auto. }
        eapply IHHe3; eauto.
  Qed.

  Lemma sem_type_implies_safe : ∀ e τ, ⊧ e ∈ τ → safe e.
  Proof.
    intros e τ H.
    unfold sem_has_type in H.
    intros e' He'.
    destruct (irred_dec e').
    - right. assumption.
    - left. apply sem_value_is_value with τ.
      apply H with ids; [| rewrite subst_id |]; auto.
  Qed.

  Corollary type_safety : ∀ τ t, ⊢ t ∈ τ → safe t.
  Proof.
    eauto using fund_lemma, sem_type_implies_safe.
  Qed.
End TypeSafety.
