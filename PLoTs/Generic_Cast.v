Require Import FJ_tactics.
Require Import cFJ.
Require Import Cast.
Require Import Generic.

Require Import List.
Require Import Arith.

Section Generic_Cast.

  Variables (TX C F M X Ty ty_ext E m_call_ext : Set).

  Variable N : Set.
  Variable N_Wrap : N -> Ty.
  Coercion N_Wrap : N >-> Ty.
  
  Definition FJ_Ty := Cast.N C ty_ext.
  Variable FJ_N_Wrap : FJ_Ty -> N.

  Definition FJ_Ty_Wrap := Generic.FJ_Ty_Wrap Ty ty_ext C N N_Wrap FJ_N_Wrap.
  
  Definition Cast_E := Cast.Cast_E C ty_ext E.

  Variable FJ_E_Wrap : FJ_E C F M X ty_ext E m_call_ext -> E.
  Variable Ty_trans : Ty -> list TX -> list Ty -> Ty.
  Variable Cast_E_Wrap : Cast_E -> E.
  Coercion Cast_E_Wrap : Cast_E >-> E.
  Variable TE_trans : ty_ext -> list TX -> list Ty -> ty_ext.

  Definition TyP_List := Generic.TyP_List TX N.

  Inductive E_Ty_Trans (E_Ty_Trans' : TyP_List -> list Ty -> E -> E -> Prop) :
    TyP_List -> list Ty -> E -> E -> Prop :=
  | FGJ_E_Ty_Trans_cast : forall XNs Us te c e e',
    E_Ty_Trans' XNs Us e e' -> E_Ty_Trans E_Ty_Trans' XNs Us 
    (Cast_E_Wrap (cast _ _ _ (ty_def _ _ te c) e)) 
    (Cast_E_Wrap (cast _ _ _ (ty_def _ _ (TE_trans te (Extract_TyVar _ _ XNs) Us) c) e')).

  Variable Context : Set.
  Variable app_context : Context -> Context -> Context.
  Variable Exp_WF : Context -> E -> Ty -> Prop.
  Variable WF_Cast_Map : Context -> Ty -> Ty -> Prop.
  Variable subtype : Context -> Ty -> Ty -> Prop.

  Definition Weakening_2_1_3_1_P := Generic.Weakening_2_1_3_1_P Ty Context app_context E Exp_WF.

  Definition Cast_E_WF := Cast.Cast_E_WF _ _ _ FJ_Ty_Wrap _ _ Cast_E_Wrap Exp_WF WF_Cast_Map subtype.

  Variable Cast_E_WF_Wrap : forall {gamma e ty}, Cast_E_WF gamma e ty -> Exp_WF gamma e ty.
  Coercion Cast_E_WF_Wrap : Cast_E_WF >-> Exp_WF.

  Variable WF_Cast_Map_app_Weaken : forall gamma ty ty', WF_Cast_Map gamma ty ty' ->
    forall gamma', WF_Cast_Map (app_context gamma gamma') ty ty'.
  Variable Weakening_2_1_1 : forall gamma S T sub_S_T, Weakening_2_1_1_P _ _ subtype app_context gamma S T sub_S_T.
  Variable subtype_dec : forall gamma S T, subtype gamma S T \/ ~ subtype gamma S T.
  Variable Ty_eq_dec : forall (S T : Ty), {S = T} + {S <> T}.

  Lemma Weakening_2_1_3_1_H1 : forall gamma S T T' e WF_e map_T sub_T_S, 
    Weakening_2_1_3_1_P _ _ _ WF_e -> 
    Weakening_2_1_3_1_P _ _ _ (Cast_E_WF_Wrap _ _ _ (T_UCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T sub_T_S)).
    unfold Weakening_2_1_3_1_P; unfold Generic.Weakening_2_1_3_1_P;
      intros; subst.
    apply Cast_E_WF_Wrap; econstructor; eauto.
    eapply Weakening_2_1_1; eassumption.
  Defined.
  
  Lemma Weakening_2_1_3_1_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, 
    Weakening_2_1_3_1_P _ _ _ WF_e -> 
    Weakening_2_1_3_1_P _ _ _ (Cast_E_WF_Wrap _ _ _  (T_DCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T sub_S_T neq_S_T)).
    unfold Weakening_2_1_3_1_P; unfold Generic.Weakening_2_1_3_1_P; intros; subst.
    apply Cast_E_WF_Wrap; econstructor 2; eauto.
    eapply Weakening_2_1_1; eassumption.
  Defined.

  Variable md_ext : Set.
  Variable cld_ext : Set.
  Variable CT : C -> option (L C F M X ty_ext Ty E md_ext cld_ext).
  Variable build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop.
  Variable FJ_subtype_Wrap : forall gamma S T,
    cFJ.FJ_subtype _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT _ subtype build_te gamma S T -> subtype gamma S T.

  Lemma Weakening_2_1_3_1_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, 
    Weakening_2_1_3_1_P _ _ _ WF_e ->
    Weakening_2_1_3_1_P _ _ _ (Cast_E_WF_Wrap _ _ _ (T_SCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S)).
    unfold Weakening_2_1_3_1_P; unfold Generic.Weakening_2_1_3_1_P; intros; subst.
    destruct (subtype_dec (app_context gamma gamma0) T' (FJ_Ty_Wrap S)).
    apply Cast_E_WF_Wrap; econstructor; eauto.
    destruct (Ty_eq_dec T' (FJ_Ty_Wrap S)); subst.
    elimtype False; apply H0; apply FJ_subtype_Wrap.
    econstructor.
    destruct (subtype_dec (app_context gamma gamma0) (FJ_Ty_Wrap S) T').
    apply Cast_E_WF_Wrap; econstructor 2; eauto.
    apply Cast_E_WF_Wrap; econstructor 3; eauto.
  Defined.

  Definition Weakening_2_1_3_1 := Cast_E_WF_rect' _ _ _ FJ_Ty_Wrap _ _ Cast_E_Wrap Exp_WF 
    WF_Cast_Map subtype Cast_E_WF_Wrap _ Weakening_2_1_3_1_H1
    Weakening_2_1_3_1_H2 Weakening_2_1_3_1_H3.

  Variable TLookup : Context -> TX -> N -> Prop.
  Variable  GJ_Ty_Wrap : GTy TX -> Ty.

  Definition GJ_subtype := Generic.GJ_subtype TX Ty GJ_Ty_Wrap N N_Wrap Context TLookup.

  Variable GJ_subtype_Wrap : forall delta S T, GJ_subtype delta S T -> subtype delta S T.
  Variable Update : Context -> Var X -> Ty -> Context.
  Variable TLookup_Update' : forall gamma Y X ty ty',  
    TLookup gamma X ty -> TLookup (Update gamma Y ty') X ty.

  Lemma Subtype_Update_list_id' : forall gamma S T (sub_S_T : GJ_subtype gamma S T), 
    Subtype_Update_list_id'_P _ _ subtype X Update gamma S T (GJ_subtype_Wrap _ _ _ sub_S_T).
    unfold Subtype_Update_list_id'_P; intros; inversion sub_S_T; subst.
    eapply GJ_subtype_Wrap; constructor.
    generalize H TLookup_Update'; clear; induction vars; simpl; intros; eauto.
    destruct a; eapply TLookup_Update'; eauto.
  Qed.

  Variable E_Ty_trans' : TyP_List -> list Ty -> E -> E -> Prop.
  Variable TUpdate : Context -> TX -> N -> Context.
  Variable WF_Type : Context -> Ty -> Prop.
  Variable Empty : Context.

  Definition update_list := cFJ.update_list _ _ _ Update.
  Definition update_Tlist := Generic.update_Tlist _ N _ TUpdate.

  Variable map_e_invert : forall XNs Us e e', 
    E_Ty_trans' XNs Us (Cast_E_Wrap e) e' -> E_Ty_Trans E_Ty_trans' XNs Us (Cast_E_Wrap e) e'.
  Variable Cast_E_Wrap_inject : forall e e', (Cast_E_Wrap e) = (Cast_E_Wrap e') -> e = e'.
  Variable WF_Cast_Map_total : forall gamma S T (sub_S_T : subtype gamma S T),
    forall T', WF_Cast_Map gamma T T' -> exists S' , WF_Cast_Map gamma S S'.
  Variable Trans_WF_Cast_map : forall ty delta delta' ty' Xs Us, 
    WF_Cast_Map delta ty ty' -> WF_Cast_Map delta' (Ty_trans ty' Xs Us) (Ty_trans ty' Xs Us).
  Variable Subtype_Update_list_id : forall gamma S T sub_S_T, 
    Subtype_Update_list_id_P X _ _ subtype Update gamma S T sub_S_T.
  Variable subtype_update_Tupdate : forall gamma S T, subtype gamma S T -> forall XNs Vars delta,
    gamma = update_Tlist (update_list delta Vars) XNs -> 
    subtype (update_list (update_Tlist delta XNs) Vars) S T.
  Variable subst_context : Context -> list TX -> list Ty -> Context.
  Variable Type_Subst_Sub_2_5' : forall gamma S T sub_S_T,
    Type_Subst_Sub_2_5_P' _ _ _ N_Wrap _ Empty subtype Ty_trans
    WF_Type TUpdate app_context subst_context gamma S T sub_S_T.
  Variable WF_Cast_map_sub : forall delta S S', WF_Cast_Map delta S S' -> subtype delta S S'.
  Variable subst_context_Empty : forall Xs Us, subst_context Empty Xs Us = Empty.
  Variable app_context_Empty : forall gamma, app_context gamma Empty = gamma.
  Variable Strengthen_WF_Cast_map : forall S delta vars T, 
    WF_Cast_Map delta S T -> WF_Cast_Map (update_list delta vars) S T.
  Variable update_list_subtype : forall gamma S T, subtype gamma S T -> forall vars,
    subtype (update_list gamma vars) S T.
  Variable sub_WF_Cast : forall delta S T (sub_S_T : subtype delta S T),
    forall S' T', WF_Cast_Map delta T T' -> WF_Cast_Map delta S S' -> subtype delta S' T'.
  Variable FJ_NTy_trans_invert : forall ty txs tys, 
    Ty_trans (FJ_Ty_Wrap ty) txs tys = FJ_Ty_Trans _ _ _ _ _ FJ_Ty_Wrap id TE_trans ty txs tys.

  Definition Lem_2_11_P e ty gamma (WF_e : Exp_WF gamma e ty) := 
    Generic.Lem_2_11_P _ _ _ N_Wrap _ Empty subtype Ty_trans WF_Type _
    TUpdate Update E Exp_WF E_Ty_trans' _ _ _ WF_e.
  
  Lemma Cast_Lem_2_11_H1 : forall gamma S T T' e WF_e map_T sub_T_S, Lem_2_11_P _ _ _ WF_e -> 
    Lem_2_11_P _ _ _ (Cast_E_WF_Wrap _ _ _ 
      (T_UCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T sub_T_S)).
    unfold Lem_2_11_P; unfold Generic.Lem_2_11_P; intros; subst.
    apply map_e_invert in H6; inversion H6; subst.
    apply Cast_E_Wrap_inject in H2; injection H2; intros; subst.
    destruct (H _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 H9) as [S [WF_e' sub_S_T]].
    generalize (WF_Cast_map_sub _ _ _ map_T) as sub_T_T'; intro.
    generalize (Type_Subst_Sub_2_5' _ _ _ (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_T_T' _ _ _ (refl_equal _)) _ _ (refl_equal _))
    _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5).
    rewrite subst_context_Empty; rewrite app_context_Empty; intro.
    assert (subtype delta_1 S (Ty_trans T' Xs Us)) by 
      (eapply FJ_subtype_Wrap; econstructor 2; eassumption).
    destruct (WF_Cast_Map_total _ _ _ H8 _ (Trans_WF_Cast_map _ _ _ _ _ _ map_T)) as 
      [S' map_S].
    exists (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c)); split.
    apply Cast_E_WF_Wrap; econstructor; eauto.
    eapply update_list_subtype; auto.
    generalize (sub_WF_Cast _ _ _ H8 _ _ (Trans_WF_Cast_map _ _ _ _ _ _ map_T) map_S);
      intros.
    eapply FJ_subtype_Wrap; econstructor 2; try eassumption.
    generalize (Type_Subst_Sub_2_5' _ _ _ (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_T_S _ _ _ (refl_equal _)) _ _ (refl_equal _))
    _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5); rewrite subst_context_Empty; 
    rewrite app_context_Empty; intro; auto.
    rewrite FJ_NTy_trans_invert in H11; simpl in H11; unfold FJ_Ty_Wrap in H11;
      unfold id in H11; auto.
    assert (Extract_TyVar _ _ XNs = Xs) by 
      (generalize XNs Ns H1; clear; induction Xs; destruct Ns; simpl; intros; try discriminate;
        injection H1; intros; subst; simpl; auto;
          caseEq (zip Xs Ns (fun x : TX => pair (TyVar TX x))); intros; rewrite H0 in H;
            try discriminate; injection H; intros; subst; simpl; erewrite IHXs; eauto).
    rewrite H12; auto.
    rewrite FJ_NTy_trans_invert; simpl; unfold FJ_Ty_Wrap; unfold id; auto.
    assert (Extract_TyVar _ _ XNs = Xs) by 
      (generalize XNs Ns H1; clear; induction Xs; destruct Ns; simpl; intros; try discriminate;
        injection H1; intros; subst; simpl; auto;
          caseEq (zip Xs Ns (fun x : TX => pair (TyVar TX x))); intros; rewrite H0 in H;
            try discriminate; injection H; intros; subst; simpl; erewrite IHXs; eauto).
    rewrite H10; eapply FJ_subtype_Wrap; constructor.
  Qed.
  
  Lemma Cast_Lem_2_11_H2 : forall gamma S T T' e WF_e map_T sub_S_T neq_S_T, Lem_2_11_P _ _ _ WF_e -> 
    Lem_2_11_P _ _ _ (Cast_E_WF_Wrap _ _ _ 
      (T_DCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T sub_S_T neq_S_T)).
    unfold Lem_2_11_P; intros; subst.
    unfold Lem_2_11_P; unfold Generic.Lem_2_11_P; intros; subst.
    apply map_e_invert in H6; inversion H6; subst.
    apply Cast_E_Wrap_inject in H2; injection H2; intros; subst.
    destruct (H _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 H9) as [S [WF_e' sub_S_T']].
    generalize (WF_Cast_map_sub _ _ _ map_T) as sub_T_T'; intro.
    generalize (Type_Subst_Sub_2_5' _ _ _ (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_T_T' _ _ _ (refl_equal _)) _ _ (refl_equal _))
    _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5).
    rewrite subst_context_Empty; rewrite app_context_Empty; intro.
    assert (subtype delta_1 S (Ty_trans T' Xs Us)) by 
      (eapply FJ_subtype_Wrap; econstructor 2; eassumption).
    destruct (WF_Cast_Map_total _ _ _ H8 _ (Trans_WF_Cast_map _ _ _ _ _ _ map_T)) as 
      [S' map_S].
    exists (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c)); split.
    destruct (subtype_dec delta_1 S' (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c))).
    apply Cast_E_WF_Wrap; econstructor; eauto.
    destruct (Ty_eq_dec S' (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c))); subst.
    elimtype False; apply H10; apply FJ_subtype_Wrap; econstructor.
    destruct (subtype_dec delta_1 (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c)) S').
    apply Cast_E_WF_Wrap; econstructor 2; eauto.
    apply Cast_E_WF_Wrap; econstructor 3; eauto.
    unfold not; intros; eapply H11.
    eapply Subtype_Update_list_id; auto.
    rewrite app_context_Empty; eassumption.
    unfold not; intros; eapply H10.
    eapply Subtype_Update_list_id; auto.
    rewrite app_context_Empty; eassumption.
    rewrite FJ_NTy_trans_invert; simpl; unfold FJ_Ty_Wrap; unfold id; auto.
    assert (Extract_TyVar _ _ XNs = Xs) by 
      (generalize XNs Ns H1; clear; induction Xs; destruct Ns; simpl; intros; try discriminate;
        injection H1; intros; subst; simpl; auto;
          caseEq (zip Xs Ns (fun x : TX => pair (TyVar TX x))); intros; rewrite H0 in H;
            try discriminate; injection H; intros; subst; simpl; erewrite IHXs; eauto).
    rewrite H10; eapply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma Cast_Lem_2_11_H3 : forall gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S, Lem_2_11_P _ _ _ WF_e ->
    Lem_2_11_P _ _ _ (Cast_E_WF_Wrap _ _ _ 
      (T_SCast _ _ _ _ _ _ _ _ _ _ gamma S T T' e WF_e map_T Nsub_S_T Nsub_T_S)).
    unfold Lem_2_11_P; intros; subst.
    unfold Lem_2_11_P; unfold Generic.Lem_2_11_P; intros; subst.
    apply map_e_invert in H6; inversion H6; subst.
    apply Cast_E_Wrap_inject in H2; injection H2; intros; subst.
    destruct (H _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 H9) as [S [WF_e' sub_S_T']].
    generalize (WF_Cast_map_sub _ _ _ map_T) as sub_T_T'; intro.
    generalize (Type_Subst_Sub_2_5' _ _ _ (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_T_T' _ _ _ (refl_equal _)) _ _ (refl_equal _))
    _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5).
    rewrite subst_context_Empty; rewrite app_context_Empty; intro.
    assert (subtype delta_1 S (Ty_trans T' Xs Us)) by 
      (eapply FJ_subtype_Wrap; econstructor 2; eassumption).
    destruct (WF_Cast_Map_total _ _ _ H8 _ (Trans_WF_Cast_map _ _ _ _ _ _ map_T)) as 
      [S' map_S].
    exists (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c)); split.
    destruct (subtype_dec delta_1 S' (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c))).
    apply Cast_E_WF_Wrap; econstructor; eauto.
    destruct (Ty_eq_dec S' (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c))); subst.
    elimtype False; apply H10; apply FJ_subtype_Wrap; econstructor.
    destruct (subtype_dec delta_1 (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te (Extract_TyVar TX N XNs) Us) c)) S').
    apply Cast_E_WF_Wrap; econstructor 2; eauto.
    apply Cast_E_WF_Wrap; econstructor 3; eauto.
    unfold not; intros; eapply H11.
    eapply Subtype_Update_list_id; auto.
    rewrite app_context_Empty; eassumption.
    unfold not; intros; eapply H10.
    eapply Subtype_Update_list_id; auto.
    rewrite app_context_Empty; eassumption.
    rewrite FJ_NTy_trans_invert; simpl; unfold FJ_Ty_Wrap; unfold id; auto.
    assert (Extract_TyVar _ _ XNs = Xs) by 
      (generalize XNs Ns H1; clear; induction Xs; destruct Ns; simpl; intros; try discriminate;
        injection H1; intros; subst; simpl; auto;
          caseEq (zip Xs Ns (fun x : TX => pair (TyVar TX x))); intros; rewrite H0 in H;
            try discriminate; injection H; intros; subst; simpl; erewrite IHXs; eauto).
    rewrite H10; eapply FJ_subtype_Wrap; constructor.
  Qed.

  Definition Cast_Lem_2_11 := Cast_E_WF_rect' _ _ _ FJ_Ty_Wrap _ _ 
    Cast_E_Wrap Exp_WF WF_Cast_Map subtype Cast_E_WF_Wrap _ Cast_Lem_2_11_H1 Cast_Lem_2_11_H2 Cast_Lem_2_11_H3.

  Variable E_Ty_trans'_Wrap : forall XNs Us e e', 
    E_Ty_Trans E_Ty_trans' XNs Us e e' -> E_Ty_trans' XNs Us e e'.

  Lemma Cast_E_Ty_Trans_tot (E_Ty_Trans_tot_rect : forall e, E_Ty_Trans_tot_P _ _ _ _ E_Ty_trans' e) :
    forall e, E_Ty_Trans_tot_P _ _ _ _ E_Ty_trans' (Cast_E_Wrap e).
    intros; unfold E_Ty_Trans_tot_P; intros; destruct e.
    destruct (E_Ty_Trans_tot_rect e XNs Ts) as [e' Trans_e].
    destruct n; eexists _; eapply E_Ty_trans'_Wrap; econstructor.
    eassumption.
  Defined.
 
End Generic_Cast.

