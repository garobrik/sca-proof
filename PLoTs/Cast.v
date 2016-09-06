Require Import cFJ.
Require Import FJ_tactics.
Require Import List.

Section Cast_Definitions.

  Variables (C : Set)
    (ty_ext : Set).
  
  Definition N := cFJ.FJ_Ty C ty_ext.
  
  Variable Ty : Set.
  Variable N_Wrap : N -> Ty.
  Coercion N_Wrap : N >-> Ty.

  Variable Context : Set.
  Variable E : Set.

  Inductive Cast_E : Set :=
    cast : N -> E -> Cast_E.

  Variable Cast_EWrap : Cast_E -> E.
  Coercion Cast_EWrap : Cast_E >-> E.

  Inductive Cast_map_e_ext' : E -> E -> Prop := 
    case_map_e_ext : forall e, Cast_map_e_ext' e e.

  Variable (E_WF : Context -> E -> Ty -> Prop)
    (WF_Cast_Map : Context -> Ty -> Ty -> Prop).

  Variable subtype : Context -> Ty -> Ty -> Prop.
  
  Definition Cast_WF_Cast_Map : Context -> Ty -> Ty -> Prop := id_map_1.

  Inductive Cast_E_WF : Context -> E -> Ty -> Prop :=
  | T_UCast : forall gamma (S : N) (T T': Ty) e,  
    E_WF gamma e T -> WF_Cast_Map gamma T T' -> subtype gamma T' S -> Cast_E_WF gamma (cast S e) S
  | T_DCast : forall gamma (S : N) (T T': Ty) e, E_WF gamma e T -> WF_Cast_Map gamma T T' -> 
    subtype gamma S T' -> (N_Wrap S) <> T' -> Cast_E_WF gamma (cast S e) S
  | T_SCast : forall gamma (S : N) (T T' : Ty) e, E_WF gamma e T -> WF_Cast_Map gamma T T' -> 
    ~ (subtype gamma S T') -> ~ (subtype gamma T' S) -> Cast_E_WF gamma (cast S e) S.
  
  Variable (Cast_E_WF_Wrap : forall {gamma e ty}, Cast_E_WF gamma e ty -> E_WF gamma e ty).
  Coercion Cast_E_WF_Wrap : Cast_E_WF >-> E_WF.
  
  Section Cast_E_WF_recursion.
    
    Variable (P : forall gamma e ty, E_WF gamma e ty -> Prop).
    
    Hypothesis (H1 : forall gamma S T T' e WF_e map_T sub_T_S, P _ _ _ WF_e -> 
      P _ _ _ (T_UCast gamma S T T' e WF_e map_T sub_T_S))
    (H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, P _ _ _ WF_e -> 
      P _ _ _ (T_DCast gamma S T T' e WF_e map_T sub_S_T neq_S_T))
    (H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, P _ _ _ WF_e ->
      P _ _ _ (T_SCast gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S)).
    
    Definition Cast_E_WF_rect' gamma e ty (WF_e : Cast_E_WF gamma e ty) 
      (E_WF_rect' : forall gamma e ty WF_e, P gamma e ty WF_e) : 
      P _ _ _ (Cast_E_WF_Wrap _ _ _ WF_e) :=
      match WF_e return  P _ _ _ (Cast_E_WF_Wrap _ _ _ WF_e) with
        | T_UCast gamma S' T T' e WF_e map_T sub_T_S' => 
          H1 gamma S' T T' e WF_e map_T sub_T_S' (E_WF_rect' _ _ _ WF_e)
        | T_DCast gamma S' T T' e WF_e map_T sub_S'_T neq_S'_T =>
          H2 gamma S' T T' e WF_e map_T sub_S'_T neq_S'_T (E_WF_rect' _ _ _ WF_e)
        | T_SCast gamma S' T T' e WF_e map_T Nsub_S'_T Nsub_T_S' => 
          H3 gamma S' T T' e WF_e map_T Nsub_S'_T Nsub_T_S' (E_WF_rect' _ _ _ WF_e)
      end.
  
  End Cast_E_WF_recursion.
  
  Definition pass_e (f_E : E -> E) (e : Cast_E) :=
    match e with 
      cast n e' => cast n (f_E e')
    end.
  
  Variable Reduce : E -> E -> Prop.
  
  Variables (F M X m_call_ext md_ext cld_ext : Set)
    (FJ_E_Wrap : FJ_E C F M X ty_ext E m_call_ext -> E)
    (CT : C -> option (L C F M X ty_ext Ty E md_ext cld_ext))
    (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (Empty : Context).
  
  Definition new := cFJ.new C F M X ty_ext E m_call_ext.
  
  Inductive Cast_Reduce : E -> E -> Prop :=
  | R_Cast : forall (S T : N) es, subtype Empty T S -> 
    Cast_Reduce (cast S (FJ_E_Wrap (new T es))) (FJ_E_Wrap (new T es)).
  
  Variable (C_Reduce : E -> E -> Prop).

  Inductive Cast_C_Reduce : E -> E -> Prop :=
    RC_Cast : forall S e e', C_Reduce e e' -> Cast_C_Reduce (cast S e) (cast S e').

  Variable (Cast_Reduce_Wrap : forall e e', Cast_Reduce e e' -> Reduce e e')
    (Cast_C_Reduce_Wrap : forall e e', Cast_C_Reduce e e' -> C_Reduce e e').

  Variables (update : Context -> Var X -> Ty -> Context)
    (lookup : Context -> Var X -> Ty -> Prop)
    (lookup_update_eq : forall gamma X ty, lookup (update gamma X ty) X ty) 
    (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
      lookup (update gamma Y ty') X ty)
    (lookup_update_neq' : forall gamma Y X ty ty',     lookup (update gamma Y ty') X ty -> X <> Y -> 
      lookup gamma X ty)
    (lookup_Empty : forall X ty, ~ lookup Empty X ty)
    (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty').

  Definition update_list := cFJ.update_list _ _ _ update.
  Definition FJ_subtype := cFJ.FJ_subtype _ _ _ _ _ _ N_Wrap _ _ _ CT Context
    subtype build_te.

  Variable (FJ_subtype_Wrap : forall gamma S T, FJ_subtype gamma S T -> subtype gamma S T).

  Variable (Weaken_Subtype_update_list : forall gamma S T (sub_S_T : subtype gamma S T)
    vars gamma', gamma = (update_list Empty vars) -> subtype (update_list gamma' vars) S T)
  (subtype_dec : forall gamma S T, subtype gamma S T \/ ~ subtype gamma S T)
  (Ty_eq_dec : forall (S T : Ty), {S = T} + {S <> T})
  (WF_Cast_Map_Weaken : forall gamma vars T T', WF_Cast_Map (update_list Empty vars) T T' -> 
    WF_Cast_Map (update_list gamma vars) T T'). 

  Lemma Cast_WF_Cast_Map_Weaken : forall gamma vars T T', 
    Cast_WF_Cast_Map (update_list Empty vars) T T' -> 
    Cast_WF_Cast_Map (update_list gamma vars) T T'.
    intros; inversion H; subst; constructor.
  Qed.

  Definition Weakening_def e ty gamma (WF_e : E_WF gamma e ty) :=
    forall gamma' vars, gamma = (update_list Empty vars) -> E_WF (update_list gamma' vars) e ty.

  Lemma Cast_Weakening_H1 : forall gamma S T T' e WF_e map_T sub_T_S, Weakening_def _ _ _ WF_e -> 
    Weakening_def _ _ _ (T_UCast gamma S T T' e WF_e map_T sub_T_S).
    unfold Weakening_def; intros; subst.
    apply Cast_E_WF_Wrap; econstructor; eauto.
  Qed.
  
  Lemma Cast_Weakening_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, Weakening_def _ _ _ WF_e -> 
    Weakening_def _ _ _ (T_DCast gamma S T T' e WF_e map_T sub_S_T neq_S_T).
    unfold Weakening_def; intros; subst.
    apply Cast_E_WF_Wrap; econstructor 2; eauto.
  Qed.

  Lemma Cast_Weakening_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, Weakening_def _ _ _ WF_e ->
    Weakening_def _ _ _ (T_SCast gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S).
    unfold Weakening_def; intros; subst.
    apply Cast_E_WF_Wrap.
    destruct (subtype_dec (update_list gamma' vars) T' S) as [sub_S_T | Nsub_S_T'].
    econstructor; eauto.
    destruct (Ty_eq_dec S T'); subst.
    elimtype False; eapply Nsub_S_T'; apply FJ_subtype_Wrap; constructor.
    destruct (subtype_dec (update_list gamma' vars) S T') as [sub_T_S | Nsub_T_S'].
    econstructor 2; eauto.
    econstructor 3; eauto.
  Qed.

  Definition Cast_Weakening := Cast_E_WF_rect' _ Cast_Weakening_H1 Cast_Weakening_H2 Cast_Weakening_H3.

  Variable (trans : E -> list (Var X) -> list E -> E).

  Definition Cast_E_trans e vars es := pass_e (fun e => trans e vars es) e.

  Lemma NSubtype_trans : forall gamma S T, subtype gamma S T -> 
    forall U, ~ subtype gamma S U -> ~ subtype gamma T U.
    unfold not; intros; apply H0.
    apply FJ_subtype_Wrap; econstructor 2; eassumption.
  Qed.

  Variable (E_trans_Wrap : forall e vars es', trans (Cast_EWrap e) vars es' = Cast_E_trans e vars es')
    (Subtype_Update_list_id : forall gamma S T sub_S_T, 
      cFJ.Subtype_Update_list_id_P _ _ _ subtype update gamma S T sub_S_T)
    (Subtype_Update_list_id' : forall gamma S T, subtype gamma S T -> forall vars,
      subtype (update_list gamma vars) S T)
    (WF_Cast_map_update_list : forall delta ty ty', WF_Cast_Map delta ty ty' -> 
      forall delta' vars, delta = update_list delta' vars -> WF_Cast_Map delta' ty ty')
    (WF_Cast_Map_total : forall gamma S T (sub_S_T : subtype gamma S T),
      forall T', WF_Cast_Map gamma T T' -> exists S' , WF_Cast_Map gamma S S')
    (sub_WF_Cast_Map : forall delta S T (sub_S_T : subtype delta S T),
      forall S' T', WF_Cast_Map delta T T' -> WF_Cast_Map delta S S' -> subtype delta S' T').

  Lemma Cast_WF_Cast_map_update_list : forall delta ty ty', Cast_WF_Cast_Map delta ty ty' -> 
    forall delta' vars, delta = update_list delta' vars -> Cast_WF_Cast_Map delta' ty ty'.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma Cast_WF_Cast_Map_total : forall gamma S T (sub_S_T : subtype gamma S T),
    forall T', Cast_WF_Cast_Map gamma T T' -> exists S' , Cast_WF_Cast_Map gamma S S'.
    intros; eexists; constructor.
  Qed.
  
  Lemma Cast_sub_WF_Cast_Map : forall delta S T (sub_S_T : subtype delta S T),
    forall S' T', Cast_WF_Cast_Map delta T T' -> Cast_WF_Cast_Map delta S S' -> subtype delta S' T'.
    intros; inversion H; inversion H0; subst; assumption.
  Qed.

  Definition Term_subst_pres_typ_P := 
    cFJ.Term_subst_pres_typ_P _ _ _ _ subtype E_WF update trans.
  
  Lemma Term_subst_pres_typ_H1 : forall gamma S T T' e WF_e map_T sub_T_S, 
    Term_subst_pres_typ_P _ _ _ WF_e -> 
    Term_subst_pres_typ_P _ _ _ (T_UCast gamma S T T' e WF_e map_T sub_T_S).
    unfold Term_subst_pres_typ_P; unfold cFJ.Term_subst_pres_typ_P;
      intros; subst.
    destruct (H _ _ _ _ _ _ (refl_equal _) H1 H2 H3) as [E' [wf_trans_e sub_E_T]].
    eapply WF_Cast_map_update_list in map_T; try reflexivity.
    destruct (WF_Cast_Map_total _ _ _ sub_E_T _ map_T) as [S' map_S].
    exists S; split.
    generalize (sub_WF_Cast_Map _ _ _ sub_E_T _ _ map_T map_S); intros sub_S'_T'.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor; try eassumption.
    apply FJ_subtype_Wrap; econstructor 2; eauto; eapply Subtype_Update_list_id; eauto.
    apply FJ_subtype_Wrap; econstructor.
  Defined.
  
  Lemma Term_subst_pres_typ_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, 
    Term_subst_pres_typ_P _ _ _ WF_e -> 
    Term_subst_pres_typ_P _ _ _ (T_DCast gamma S T T' e WF_e map_T sub_S_T neq_S_T).
    unfold Term_subst_pres_typ_P; unfold cFJ.Term_subst_pres_typ_P; intros; subst.
    destruct (H _ _ _ _ _ _ (refl_equal _) H1 H2 H3) as [V [wf_trans_e sub_V_T]].
    eapply WF_Cast_map_update_list in map_T; try reflexivity.
    destruct (WF_Cast_Map_total _ _ _ sub_V_T _ map_T) as [V' map_V].
    destruct (subtype_dec delta V' S).
    exists S; split.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor; eauto.
    apply FJ_subtype_Wrap; econstructor.
    destruct (Ty_eq_dec V' S); subst.
    elimtype False; apply H0; apply FJ_subtype_Wrap; econstructor.
    destruct (subtype_dec delta S V').
    generalize (sub_WF_Cast_Map _ _ _ sub_V_T _ _ map_T map_V); intros sub_V'_T'.
    exists S; split.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor 2; eauto.
    apply FJ_subtype_Wrap; econstructor.
    exists S; split.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor 3; eauto.
    apply FJ_subtype_Wrap; econstructor.
  Qed.

  Lemma Term_subst_pres_typ_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, 
    Term_subst_pres_typ_P _ _ _ WF_e ->
    Term_subst_pres_typ_P _ _ _ (T_SCast gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S).
    unfold Term_subst_pres_typ_P; unfold cFJ.Term_subst_pres_typ_P; intros; subst.
    exists S; split.
    destruct (H _ _ _ _ _ _ (refl_equal _) H1 H2 H3) as [V [wf_trans_e sub_V_T]].
    eapply WF_Cast_map_update_list in map_T; try reflexivity.
    destruct (WF_Cast_Map_total _ _ _ sub_V_T _ map_T) as [V' map_V].
    generalize (sub_WF_Cast_Map _ _ _ sub_V_T _ _ map_T map_V); intros sub_V'_T'.
    destruct (subtype_dec (update_list delta Vars) V' S).
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor; eauto;
      eapply Subtype_Update_list_id; eauto.
    destruct (subtype_dec (update_list delta Vars) S V').
    destruct (Ty_eq_dec V' S); subst.
    elimtype False; eauto.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor 2; eauto;
      eapply Subtype_Update_list_id; eauto.
    rewrite E_trans_Wrap; simpl; apply Cast_E_WF_Wrap; econstructor 3; eauto.
    apply FJ_subtype_Wrap; econstructor.
  Qed.

  Definition Cast_Term_subst_pres_typ := Cast_E_WF_rect' _ Term_subst_pres_typ_H1
    Term_subst_pres_typ_H2 Term_subst_pres_typ_H3.

  Definition Subtype_Update_list_id'_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall vars, subtype (update_list gamma vars) S T.

  Lemma Subtype_Update_list_id'_H1 : forall (ty : Ty) (gamma : Context), 
    Subtype_Update_list_id'_P _ _ _ (FJ_subtype_Wrap _ _ _ 
      (sub_refl _ _ _ _ _ _ N_Wrap _ _ _ CT _ subtype build_te ty gamma)).
    unfold Subtype_Update_list_id'_P; intros; apply FJ_subtype_Wrap.
    constructor.
  Qed.

  Lemma Subtype_Update_list_id'_H2 : forall c d e gamma sub_c sub_d, 
    Subtype_Update_list_id'_P _ _ _ sub_c -> 
    Subtype_Update_list_id'_P _ _ _ sub_d -> 
    Subtype_Update_list_id'_P _ _ _ (FJ_subtype_Wrap _ _ _ 
      (sub_trans _ _ _ _ _ _ N_Wrap _ _ _ CT _ subtype build_te c d e gamma sub_c sub_d)).
    unfold Subtype_Update_list_id'_P; intros; apply FJ_subtype_Wrap.
    econstructor 2.
    eapply H; eauto.
    eauto.
  Qed.

  Lemma Subtype_Update_list_id'_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
    Subtype_Update_list_id'_P _ _ _ (FJ_subtype_Wrap _ _ _
      (sub_dir _ _ _ _ _ _ N_Wrap _ _ _ CT _ subtype build_te ce c d fs k' ms te te' te'' gamma CT_c bld_te)).
    unfold Subtype_Update_list_id'_P; intros; apply FJ_subtype_Wrap.
    econstructor 3; eauto.
  Qed.

  Definition FJ_Subtype_Update_list_id' := 
    FJ_subtype_rect _ _ _ _ _ _ N_Wrap _ _ _ CT _ subtype build_te FJ_subtype_Wrap _
    Subtype_Update_list_id'_H1 Subtype_Update_list_id'_H2 Subtype_Update_list_id'_H3.

  Definition preservation_P := cFJ.preservation Ty E Context subtype E_WF Reduce.

  Variable (Cast_E_WF_invert : forall gamma (e : Cast_E) c0, E_WF gamma e c0 -> 
    Cast_E_WF gamma e c0)
  (Cast_E_inject : forall e e', Cast_EWrap e = Cast_EWrap e' -> e = e')
  (FJ_E_Wrap_inject : forall e e', FJ_E_Wrap e = FJ_E_Wrap e' -> e = e').

  Variables (mty_ext : Set)
    (WF_Type : Context -> Ty -> Prop)
    (fields : Context -> Ty -> list (FD F Ty) -> Prop)
    (mtype_build_te : cld_ext -> ty_ext -> ty_ext -> Prop)
    (mtype_build_tys : cld_ext ->
      ty_ext -> list Ty -> list Ty -> Prop)
    (mtype_build_mtye : cld_ext ->
      ty_ext -> md_ext -> mty_ext -> Prop)
    (WF_fields_map WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_ext -> Prop).

  Variable (FJ_E_WF_new_invert : forall gamma e T T0, E_WF gamma (FJ_E_Wrap (new T e)) T0 ->
    N_Wrap T = T0)
  (subtype_sym_self : forall gamma S T, subtype gamma S T -> subtype gamma T S -> T = S)
  (Subtype_Weaken : forall gamma S T sub_S_T, Subtype_Weaken_P Ty Context subtype Empty gamma S T sub_S_T)
  (WF_Cast_Map_sub : forall gamma ty ty', WF_Cast_Map gamma ty ty' -> subtype gamma ty ty').

  Lemma Cast_WF_Cast_Map_sub : forall gamma ty ty', Cast_WF_Cast_Map gamma ty ty' -> subtype gamma ty ty'.
    intros; inversion H; subst; eapply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma Cast_preservation : forall S T es sub_T_S , 
    preservation_P _ _ (Cast_Reduce_Wrap _ _ (R_Cast S T es sub_T_S)).
    unfold preservation_P; unfold cFJ.preservation; intros.
    apply Cast_E_WF_invert in H; inversion H; subst;
      apply Cast_E_inject in H0; injection H0; intros; subst;
        generalize (WF_Cast_Map_sub _ _ _ H2) as sub_T0_T'; intro.
    exists T0; split; try eassumption; apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    generalize (FJ_E_WF_new_invert _ _ _ _ H1); intros; subst.
    exists T; split; auto.
    generalize (FJ_E_WF_new_invert _ _ _ _ H1); intros; subst;
      eapply Subtype_Weaken; eauto.
    generalize (FJ_E_WF_new_invert _ _ _ _ H1); intros; subst.
    exists T; split; auto; eapply Subtype_Weaken; eauto.
  Qed.

  Lemma Cast_preservation' : forall e e' (red_e : Cast_Reduce e e'), 
    preservation_P e e' (Cast_Reduce_Wrap _ _ red_e).
    intros; inversion red_e; subst.
    apply Cast_preservation with (sub_T_S := H).
  Qed.

  Definition C_preservation_P := cFJ.C_preservation Ty E Context subtype E_WF C_Reduce.

  Lemma Cast_C_preservation : forall S e e' red_e, C_preservation_P _ _ red_e -> 
    C_preservation_P _ _ (Cast_C_Reduce_Wrap _ _ (RC_Cast S e e' red_e)).
    cbv beta delta; intros.
    exists (N_Wrap S); split.
    apply Cast_E_WF_invert in H0; inversion H0; subst;
      apply Cast_E_inject in H1; injection H1; intros; subst; clear H1;
        destruct (H _ _ H2) as [V [WF_e' sub_V_T]].
    destruct (WF_Cast_Map_total _ _ _ sub_V_T _ H3) as [V' map_V].
    generalize (sub_WF_Cast_Map _ _ _ sub_V_T _ _ H3 map_V); intros sub_V'_T'.
    eapply Cast_E_WF_Wrap; econstructor; try eassumption.
    eapply FJ_subtype_Wrap; econstructor 2; eauto.
    destruct (WF_Cast_Map_total _ _ _ sub_V_T _ H3) as [V' map_V].
    generalize (sub_WF_Cast_Map _ _ _ sub_V_T _ _ H3 map_V); intros sub_V'_T'.
    destruct (subtype_dec gamma V' (N_Wrap S)).
    eapply Cast_E_WF_Wrap; econstructor; try eassumption.
    destruct (Ty_eq_dec (N_Wrap S) V'); subst.
    elimtype False; apply H1; eapply FJ_subtype_Wrap; econstructor.
    destruct (subtype_dec gamma (N_Wrap S) V').
    eapply Cast_E_WF_Wrap; econstructor 2; eauto.
    eapply Cast_E_WF_Wrap; econstructor 3; eauto.
    destruct (WF_Cast_Map_total _ _ _ sub_V_T _ H3) as [V' map_V].
    generalize (sub_WF_Cast_Map _ _ _ sub_V_T _ _ H3 map_V); intros sub_V'_T'.
    destruct (subtype_dec gamma V' (N_Wrap S)).
    eapply Cast_E_WF_Wrap; econstructor; eauto.
    destruct (Ty_eq_dec V' (N_Wrap S)); subst.
    elimtype False; eauto.
    destruct (subtype_dec gamma (N_Wrap S) V').
    elimtype False; apply H4; eapply FJ_subtype_Wrap; econstructor 2; eauto.
    eapply Cast_E_WF_Wrap; econstructor 3; eauto.
    apply Cast_E_WF_invert in H0; inversion H0; subst;
      apply Cast_E_inject in H1; injection H1; intros; subst.
    eapply FJ_subtype_Wrap; constructor.
    eapply FJ_subtype_Wrap; constructor.
    eapply FJ_subtype_Wrap; constructor.    
  Qed.

  Definition Cast_C_preservation' e e' (red_e : Cast_C_Reduce e e') 
    (Cast_C_rect' : forall e e' red_e, C_preservation_P e e' red_e) : 
    C_preservation_P e e' (Cast_C_Reduce_Wrap _ _ red_e) :=
    match red_e return C_preservation_P _ _ (Cast_C_Reduce_Wrap _ _ red_e) with
      | RC_Cast s e e' red_e => Cast_C_preservation s e e' red_e (Cast_C_rect' _ _ red_e)
    end.

  Variable (subexpression : E -> E -> Prop).

  Inductive Cast_subexpression : E -> E -> Prop :=
  | subexp_cast : forall S e' e, subexpression e' e ->
    Cast_subexpression e' (cast S e).

  Variable (Cast_subexpression_Wrap : forall e' e, Cast_subexpression e' e -> subexpression e' e).

  Definition progress_1_P := cFJ.progress_1_P _ _ _ _ _ _ N_Wrap _ _ FJ_E_Wrap _ fields
    E_WF Empty subexpression.

  Variables (mbody_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (mb_ext : Set)
    (build_mb_ext : cld_ext -> ty_ext -> m_call_ext -> md_ext -> mb_ext -> Prop)
    (map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop)
    (Cast_subexp_invert : forall e' S e, subexpression e' (cast S e) -> 
      Cast_subexpression e' (cast S e) \/ e' = (cast S e))
    (FJ_Cast_discriminate : forall e S e', ~ FJ_E_Wrap e = cast S e').

  Definition progress_2_P := cFJ.progress_2_P _ _ _ _ _ _ N_Wrap _ _ FJ_E_Wrap _ _ CT _ 
    mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty subexpression.

  Lemma Cast_progress_1_H1 : forall gamma S T T' e WF_e map_T sub_T_S, 
    progress_1_P _ _ _ WF_e -> 
    progress_1_P _ _ _ (T_UCast gamma S T T' e WF_e map_T sub_T_S).
    unfold progress_1_P; unfold cFJ.progress_1_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Lemma Cast_progress_1_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, progress_1_P _ _ _ WF_e -> 
    progress_1_P _ _ _ (T_DCast gamma S T T' e WF_e map_T sub_S_T neq_S_T).
    unfold progress_1_P; unfold cFJ.progress_1_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Lemma Cast_progress_1_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, progress_1_P _ _ _ WF_e ->
    progress_1_P _ _ _ (T_SCast gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S).
    unfold progress_1_P; unfold cFJ.progress_1_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Definition Cast_progress_1 := Cast_E_WF_rect' _ Cast_progress_1_H1 Cast_progress_1_H2 Cast_progress_1_H3.

  Lemma Cast_progress_2_H1 : forall gamma S T T' e WF_e map_T sub_T_S, 
    progress_2_P _ _ _ WF_e -> 
    progress_2_P _ _ _ (T_UCast gamma S T T' e WF_e map_T sub_T_S).
    unfold progress_2_P; unfold cFJ.progress_2_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Lemma Cast_progress_2_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, progress_2_P _ _ _ WF_e -> 
    progress_2_P _ _ _ (T_DCast gamma S T T' e WF_e map_T sub_S_T neq_S_T).
    unfold progress_2_P; unfold cFJ.progress_2_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Lemma Cast_progress_2_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, progress_2_P _ _ _ WF_e ->
    progress_2_P _ _ _ (T_SCast gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S).
    unfold progress_2_P; unfold cFJ.progress_2_P; intros.
    apply Cast_subexp_invert in H0; destruct H0 as [H0 | H0].
    inversion H0; subst; apply Cast_E_inject in H1; injection H1; intros; subst; clear H1; eauto.
    elimtype False; eapply FJ_Cast_discriminate; eauto.
  Qed.

  Definition Cast_progress_2 := Cast_E_WF_rect' _ Cast_progress_2_H1 Cast_progress_2_H2 Cast_progress_2_H3.

End Cast_Definitions.
