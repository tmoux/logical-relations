Require Import Unicode.Utf8.
Require Import Relations.Relation_Operators.
Require Import List.
Require Import Autosubst.Autosubst.

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

Lemma value_dec : forall v, value v ∨ ¬ (value v).
Proof.
  destruct v; auto; right; intros H; inversion H.
Qed.


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

Lemma value_multistep : ∀ v v', value v → v -->* v' → v' = v.
Proof.
  intros.
  inversion H0. auto.
  value_step.
Qed.

Section Examples.
  Definition e_id := TLam Bool (TVar 0).
  Goal TApp e_id TTrue --> TTrue.
    constructor. apply value_true.
    simpl. reflexivity.
  Qed.

End Examples.

Definition irred (e : term) := forall e', ¬ (e --> e').
Ltac irred_step :=
  match goal with
  | [ H : irred ?e, Hstep : ?e --> ?e' |- _ ] => exfalso; apply H in Hstep; assumption
  end.


Section Deterministic.
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


  Corollary irred_unique : ∀ a b c, a -->* b → a -->* c → irred b → c -->* b.
  Proof.
    intros.
    destruct (confluence H H0) as [z [? ?]].
    inversion H2; subst. auto. irred_step.
  Qed.

End Deterministic.


(*
Definition context := var → option type.
Definition empty : context := fun _ => None.

#[export] Instance Rename_ctx : Rename context.
Proof.
  unfold Rename.
  intros ρ Γ x.
  exact (Γ (ρ x)).
Defined.

Definition shift_ctx : type → context → context :=
  fun T Γ x => match x with
               | O => Some T
               | S n => Γ n
               end.
*)

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
  Definition safe (e : term) := forall e', e -->* e' → value e' ∨ ∃ e'', e' --> e''.

  (*
  This definition doesn't work: runs into positivity requirement for inductive types.
  Inductive sem_value : type → term → Prop :=
  | sem_value_true : sem_value Bool TTrue
  | sem_value_false : sem_value Bool TFalse
  | sem_value_arr : ∀ τ₁ τ₂ e, (∀ v, value v → sem_value τ₁ v → sem_expr τ₂ e.[v/]) → sem_value (τ₁ ⇒ τ₂) (TLam τ₁ e)
  with sem_expr : type → term → Prop :=
  | sem_exprC : ∀ τ e, (∀ e', e -->* e' → (* irred(e') → *) sem_value τ e') → sem_expr τ e.
  *)

  Lemma irred_decidable : ∀ e, (∃ e', e --> e') ∨ irred e.
  Proof.
    induction e.
    - right. intros e' H. value_step.
    - right. intros e' H. value_step.
    - destruct e1; try solve [left; eexists; auto];
        repeat (destruct IHe1 as [[e1' ?] | ?]; [
        left; eexists; apply step_if; apply H |
        right; intros e' Hstep; inversion Hstep; subst; irred_step ]).
    - right. intros e' H. inversion H.
    - right. intros e' H. value_step.
    - destruct IHe1 as [[e1' ?] | ?].
      left. eexists. constructor. apply H.
      destruct IHe2 as [[e2' ?] | ?].
      destruct (value_dec e1).
      * left. eexists. apply step_app2. apply H1. apply H0.
      * right. intros e' Hstep. inversion Hstep; subst. value_step. irred_step. apply H1. assumption.
      * destruct (value_dec e1).
        destruct H1.
        + right. intros e' Hstep. inversion Hstep; subst. irred_step. irred_step.
        + right. intros e' Hstep. inversion Hstep; subst. irred_step. irred_step.
        + destruct (value_dec e2).
          ++ left. exists e.[e2/]. constructor; auto.
          ++ right. intros e' Hstep. inversion Hstep; subst. auto. inversion H5. irred_step.
        + right. intros e' Hstep. inversion Hstep; subst. apply H1. constructor. irred_step. irred_step.
  Qed.

  (* The easiest way to write this is to avoid mutual recursion altogether, since Coq's termination checker isn't smart enough to see that this is well-founded. *)
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

  Lemma sem_val_is_sem_expr : forall v τ, v ∈ 𝓥⟦ τ ⟧ → v ∈ 𝓔⟦ τ ⟧.
  Proof.
    intros v τ H.
    destruct τ.
    - destruct H; intros e' Hstep; subst; apply value_multistep in Hstep; subst; simpl; auto.
    - simpl in H.
      destruct H as [e [H1 H2]].
      subst.
      intros e' Hstep. apply value_multistep in Hstep; subst; simpl; auto.
      intros.
      eexists. split. reflexivity.
      apply H2.
  Qed.

  Definition id_subst : var → term := ids.
  Inductive valid_subst : context → (var → term) → Prop :=
  | subst_empty : valid_subst empty id_subst
  | subst_cons : ∀ Γ γ v τ, valid_subst Γ γ → v ∈ 𝓥⟦ τ ⟧ → valid_subst (τ :: Γ) (v .: γ).
  #[local] Hint Constructors valid_subst : core.

  Lemma valid_subst_var : ∀ Γ γ, valid_subst Γ γ → ∀ x τ, lookup Γ x = Some τ → γ x ∈ 𝓥⟦ τ ⟧.
  Proof.
    intros Γ γ H.
    induction H; intros.
    - destruct x; simpl in *; discriminate.
    - induction x. simpl in *. inversion H1. subst. assumption.
      simpl in *. apply IHvalid_subst. assumption.
  Qed.

    (* Lemma: if e has type τ in Γ, and γ is a valid substitution, then e.[γ] is closed term and has type τ in empty context*)

  Definition sem_has_type (Γ : context) (e : term) (τ : type) :=
    ∀ (γ : var → term), valid_subst Γ γ → e.[γ] ∈ 𝓔⟦ τ ⟧.
  Notation "Γ '⊧' e '∈' τ" := (sem_has_type Γ e τ) (at level 80).
  Notation "'⊧' e '∈' T" := (empty ⊧ e ∈ T) (at level 85).

  Lemma sem_value_is_value : ∀ v τ, v ∈ 𝓥⟦ τ ⟧ → value v.
  Proof.
    intros v τ H.
    destruct τ.
    - unfold sem_value in H.
      destruct H; rewrite H; auto.
    - destruct H as [H1 [H2 H3]].
      rewrite H2.
      auto.
  Qed.


  (* Need a bunch of congruence step lemmas: *)
  Lemma if_cond_step : ∀ e1 e2 e3 e1', e1 -->* e1' → TIf e1 e2 e3 -->* TIf e1' e2 e3.
  Proof.
    intros.
    induction H; auto.
    constructor.
    econstructor.
    constructor. apply H.
    assumption.
  Qed.

  Lemma app_cong1 : ∀ e1 e2 e1', e1 -->* e1' → TApp e1 e2 -->* TApp e1' e2.
  Proof.
    intros.
    induction H.
    constructor.
    econstructor.
    constructor. apply H.
    assumption.
  Qed.

  Lemma app_cong2 : ∀ τ e1 e2 e2', e2 -->* e2' → TApp (TLam τ e1) e2 -->* TApp (TLam τ e1) e2'.
  Proof.
    intros.
    induction H.
    constructor.
    econstructor.
    apply step_app2. constructor. apply H.
    assumption.
  Qed.

  (* When If takes a step, either we take a step to another If, or we step to one of the branches.
   If the whole expression steps to a reducible value, e1 must have stepped to a reducible value.
   The induction principle is tricky, naively inducting on the Hif doesn't seem to work. Instead we write it using a fixpoint, but we need to be careful to ensure the arguments are decreasing. *)
  Fixpoint tif_lemma (e' e2 e3 : term) (H : irred e') (e1 : term) (Hif : TIf e1 e2 e3 -->* e') {struct Hif} : ∃ e1', e1 -->* e1' ∧ irred e1'.
  Proof.
    destruct Hif.
    - exists e1. split. constructor.
      intros e1' Hstep.
      assert (TIf e1 e2 e3 --> TIf e1' e2 e3). constructor. auto.
      unfold irred in H. specialize H with (TIf e1' e2 e3). apply H. auto.
    - destruct (irred_decidable e1).
      * destruct H1 as [e1' ?]. specialize tif_lemma with z e2 e3 e1'.
        apply tif_lemma in H.
        destruct H as [e1'' [? ?]].
        exists e1''. split.
        econstructor. apply H1. apply H.
        apply H2.
        assert (TIf e1 e2 e3 --> TIf e1' e2 e3). constructor. auto.
        assert (y = TIf e1' e2 e3). apply (step_deterministic H0 H2).
        rewrite H3 in *. apply Hif.
      * exists e1. split. constructor. auto.
   Qed.

  Fixpoint app_lemma1 {e1 e2 e' : term} (He' : irred e') (H : TApp e1 e2 -->* e') : ∃ e1', e1 -->* e1' ∧ irred e1'.
  Proof.
    destruct H.
    - exists e1. split. constructor.
      intros e1' Hstep.
      assert (TApp e1 e2 --> TApp e1' e2). constructor; auto.
      unfold irred in He'. specialize He' with (TApp e1' e2). auto.
    - destruct (irred_decidable e1).
      * destruct H1 as [e1' ?]. specialize app_lemma1 with e1' e2 z.
        apply app_lemma1 in He'.
        destruct He' as [e1'' [? ?]].
        exists e1''. split.
        econstructor. apply H1. apply H2.
        assumption.
        assert (TApp e1 e2 --> TApp e1' e2). constructor. auto.
        assert (y = TApp e1' e2). apply (step_deterministic H H2).
        rewrite H3 in *. apply H0.
      * exists e1. split. constructor. auto.
  Qed.

  Fixpoint app_lemma2 {τ} {e e2 e' : term} (He' : irred e') (H : TApp (TLam τ e) e2 -->* e') {struct H} : ∃ e2', e2 -->* e2' ∧ irred e2'.
  Proof.
    destruct H.
    - exists e2. split. constructor.
      intros e2' Hstep.
      assert (TApp (TLam τ e) e2 --> TApp (TLam τ e) e2'). apply step_app2; auto.
      unfold irred in He'. specialize He' with (TApp (TLam τ e) e2'). auto.
    - destruct (irred_decidable e2).
      * destruct H1 as [e2' ?]. specialize app_lemma2 with τ e e2' z.
        apply app_lemma2 in He'.
        destruct He' as [e2'' [? ?]].
        exists e2''. split.
        + econstructor. apply H1. assumption.
        + assumption.
        + assert (TApp (TLam τ e) e2 --> TApp (TLam τ e) e2'). apply step_app2; auto.
          assert (y = TApp (TLam τ e) e2'). apply (step_deterministic H H2).
          rewrite H3 in *.
          assumption.
      * exists e2. split. constructor. auto.
  Qed.

  Lemma fund_lemma : ∀ e τ, ⊢ e ∈ τ → ⊧ e ∈ τ.
  Proof.
    intros e τ He.
    induction He; intros γ Hγ; simpl.
    - (* Var case *)
      apply sem_val_is_sem_expr.
      eapply valid_subst_var; eauto.
    - apply sem_val_is_sem_expr; simpl; auto.
    - apply sem_val_is_sem_expr; simpl; auto.
    - (* Lambda case *) intros e' Hstep.
      assert (e' = TLam τ₁ e.[up γ]). { apply value_multistep; auto. }
      rewrite H.
      intros.
      rewrite sem_value_arr.
      eexists; split; auto.
      intros v Hv.
      unfold sem_has_type in IHHe.
      specialize IHHe with (v .: γ).
      assert (e.[up γ].[v/] = e.[v .: γ]). { autosubst. }
      rewrite H1.
      apply IHHe.
      constructor; auto.
    - (* App case *) unfold sem_has_type in IHHe1, IHHe2.
      specialize IHHe1 with γ.
      specialize IHHe2 with γ.
      unfold sem_expr in IHHe1.
      intros e' Hstep He'.
      destruct (app_lemma1 He' Hstep) as [f' [? ?]].
      assert (TApp f.[γ] e.[γ] -->* TApp f' e.[γ]). { apply app_cong1; auto. }
      specialize IHHe1 with f'.
      rewrite sem_value_arr in IHHe1.
      destruct IHHe1 as [f'' [? ?]]; auto.
      subst.
      destruct (app_lemma1 He' Hstep) as [f' [? ?]].
      assert (TApp (TLam τ₂ f'') e.[γ] -->* e'). {
        eapply irred_unique. apply Hstep. assumption. assumption. }
      destruct (app_lemma2 He' H5) as [e2' [? ?]].
      unfold sem_expr in IHHe2.
      specialize IHHe2 with e2'.

      assert (e2' ∈ 𝓥⟦ τ₂ ⟧). { apply IHHe2; auto. }
      assert (value e2'). { eapply sem_value_is_value; eauto. }
      assert (TApp (TLam τ₂ f'') e.[γ] -->* TApp (TLam τ₂ f'') e2'). { apply app_cong2; auto. }
      assert (TApp (TLam τ₂ f'') e2' -->* f''.[e2'/]). { econstructor; auto. }
      assert (f''.[e2'/] ∈ 𝓔⟦ τ ⟧). { apply H3. auto. }
      assert (f''.[e2'/] -->* e').
      { eapply irred_unique; eauto.
        apply Operators_Properties.clos_rt_rt1n_iff.
        eapply rt_trans.
        apply Operators_Properties.clos_rt_rt1n_iff. apply H10.
        apply Operators_Properties.clos_rt_rt1n_iff. apply H11. }
      apply H12; auto.
    - (* If case *) unfold sem_has_type in IHHe1, IHHe2, IHHe3.
      specialize IHHe1 with γ.
      intros e' Hstep He'.
      unfold sem_expr in IHHe1.
      destruct (tif_lemma _ _ _ He' _ Hstep) as [e1' [Hif1 Hif2]].
      assert (TIf e.[γ] e₁.[γ] e₂.[γ] -->*
                                    TIf e1' e₁.[γ] e₂.[γ]). { auto using if_cond_step. }
      simpl in IHHe1.
      destruct (IHHe1 Hγ e1') as [? | ?]; auto.
      * subst.
        assert (TIf TTrue e₁.[γ] e₂.[γ] --> e₁.[γ]). auto.
        assert (e₁.[γ] -->* e'). {
          eapply irred_unique.
          apply Hstep.
          eapply multistep_trans.
          apply H. econstructor. apply H0. auto. auto.
        }
        eapply IHHe2; eauto.
      * subst.
        assert (TIf TFalse e₁.[γ] e₂.[γ] --> e₂.[γ]). auto.
        assert (e₂.[γ] -->* e'). {
          eapply irred_unique.
          apply Hstep.
          eapply multistep_trans.
          apply H. econstructor. apply H0. auto. auto.
        }
        eapply IHHe3; eauto.
  Qed.

  Lemma sem_type_implies_safe : ∀ e τ, ⊧ e ∈ τ → safe e.
  Proof.
    intros e τ H.
    unfold sem_has_type in H.
    specialize H with id_subst.
    unfold id_subst in H.
    rewrite subst_id in H.
    intros e' He'.
    destruct (irred_decidable e').
    - right. assumption.
    - left.
      eapply sem_value_is_value. apply H; auto.
  Qed.

  Print sem_type_implies_safe.
  Print Assumptions irred_decidable.

  Print Assumptions sem_type_implies_safe.

  Theorem type_safety : ∀ τ t, ⊢ t ∈ τ → safe t.
  Proof.
    eauto using fund_lemma, sem_type_implies_safe.
  Qed.

  Print Assumptions type_safety.

End TypeSafety.
