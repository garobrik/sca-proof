Require Import FJ_tactics.
Require Import cFJ.
Require Import Cast.
Require Import List.
Require Import Arith.

Definition CL := cFJ.CL nat.

Inductive Ty : Set :=
  cFJ : FJ_Ty nat (FJ_ty_ext) -> Ty.

Definition ty_ext := FJ_ty_ext.
Definition md_ext := FJ_md_ext.
Definition mty_ext := FJ_mty_ext.
Definition cld_ext := FJ_cld_ext.
Definition m_call_ext := FJ_m_call_ext.

Inductive E : Set :=
| cFJ_E : FJ_E nat nat nat nat ty_ext E m_call_ext -> E
| Cast_E : Cast.Cast_E nat ty_ext E -> E.

Definition mb_ext := FJ_mb_ext.
Definition FD := cFJ.FD nat Ty.
Definition MD := cFJ.MD nat nat Ty E md_ext.
Definition MTy := cFJ.Mty Ty mty_ext.
Definition MB := cFJ.MB nat E mb_ext.

Definition L := cFJ.L nat nat nat nat ty_ext Ty E md_ext cld_ext.

Parameter (CT : nat -> option L).

Definition build_te := FJ_build_te.

Variable (Context : Set)
  (Empty : Context).

Inductive subtype : Context -> Ty -> Ty -> Prop :=
  cFJ_sub : forall gamma ty ty', 
    cFJ.FJ_subtype nat nat nat nat _ Ty cFJ E md_ext cld_ext CT Context subtype build_te gamma ty ty' ->
    subtype gamma ty ty'.

Definition wf_class_ext := FJ_wf_class_ext Context.
Definition wf_object_ext := FJ_wf_object_ext Context.

Inductive WF_Type : Context -> Ty -> Prop :=
  cFJ_WF_Type : forall gamma ty, FJ_WF_Type _ _ _ _ _ _ cFJ _ _ _ CT Context 
    wf_class_ext wf_object_ext  gamma ty -> WF_Type gamma ty.

Definition fields_build_te := FJ_fields_build_te.
Definition fields_build_tys := FJ_fields_build_tys Ty.

Inductive fields : Context -> Ty -> list FD -> Prop :=
  FJ_fields : forall gamma ty fds, cFJ.FJ_fields _ _ _ _ _ Ty cFJ _ _ _
    CT Context fields fields_build_te fields_build_tys gamma ty fds -> fields gamma ty fds.

Definition mtype_build_te := FJ_mtype_build_te.

Definition mtype_build_tys := FJ_mtype_build_tys nat Ty.

Definition mtype_build_mtye := FJ_mtype_build_mtye nat Ty.

Inductive mtype : Context -> nat -> Ty -> MTy -> Prop :=
  FJ_mtype : forall gamma m ty mty, cFJ.FJ_mtype _ _ _ _ _ Ty cFJ _ _ _ _ CT Context mtype mtype_build_te
    mtype_build_tys mtype_build_mtye gamma m ty mty -> mtype gamma m ty mty.

Definition mbody_build_te := FJ_mbody_build_te.

Definition mbody_m_call_map := FJ_mbody_m_call_map. 

Definition mbody_new_map := FJ_mbody_new_map. 

Definition map_mbody := FJ_map_mbody E.
Definition build_mb_ext := FJ_build_mb_ext.

Inductive mbody : Context -> m_call_ext -> nat -> Ty -> MB -> Prop :=
  FJ_mbody : forall gamma Vs m ct mb, cFJ.mbody _ _ _ _ _ Ty cFJ E _ _ _ CT _ 
    mbody_build_te _ build_mb_ext map_mbody gamma Vs m ct mb -> mbody gamma Vs m ct mb.

Definition WF_mtype_Us_map := FJ_WF_mtype_Us_map Ty Context.
Definition WF_mtype_U_map := FJ_WF_mtype_U_map Ty Context.
Definition WF_mtype_ext := FJ_WF_mtype_ext Context.
Definition WF_fields_map := FJ_WF_fields_map Ty Context.
Definition WF_mtype_ty_0_map := FJ_WF_mtype_ty_0_map Ty Context.
Definition WF_Cast_map := Cast_WF_Cast_Map Ty Context.

Variable (lookup : Context -> Var nat -> Ty -> Prop).

Inductive E_WF: Context -> E -> Ty -> Prop :=
| FJ_E_WF : forall gamma e ty, cFJ.FJ_E_WF _ _ _ _ _ Ty cFJ _ _ cFJ_E mty_ext _ subtype WF_Type
  fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
  WF_mtype_ext Empty gamma e ty -> E_WF gamma e ty
| Cast_Exp_WF : forall gamma e ty, 
  Cast.Cast_E_WF _ _ _ cFJ _ _ Cast_E E_WF WF_Cast_map subtype gamma e ty ->
  E_WF gamma e ty.

Definition ce_build_cte := FJ_ce_build_cte.
Definition Meth_build_context := FJ_Meth_build_context Context.
Definition Meth_WF_Ext := FJ_Meth_WF_Ext Context.

Definition override := cFJ.FJ_override _ _ _ _ cFJ mty_ext Context mtype Empty.

Variable (Update : Context -> Var nat -> Ty -> Context).

Inductive Meth_WF : nat -> MD -> Prop :=
  FJ_Meth_WF : forall c md, cFJ.Meth_WF _ _ _ _ _ _ cFJ E _ _ CT Context 
    subtype WF_Type E_WF Empty Update ce_build_cte Meth_build_context 
    Meth_WF_Ext override c md -> Meth_WF c md.

Definition L_WF_Ext := FJ_L_WF_Ext nat Context. 
Definition L_build_context := FJ_L_build_context Context Empty.

Inductive L_WF : L -> Prop :=
  L_wf : forall cld, cFJ.L_WF _ _ _ _ _ _ cFJ _ _ _ CT _ subtype WF_Type 
    fields E_WF Empty Update  ce_build_cte Meth_build_context Meth_WF_Ext override
    L_WF_Ext L_build_context cld -> L_WF cld.

Fixpoint trans (e : E) (Vars : list (Var nat)) (Es : list E) : E :=
  match e with 
    | cFJ_E fj_e => cFJ.FJ_E_trans _ _ _ _ _ _ _ cFJ_E trans eq_nat_dec fj_e Vars Es
    | Cast_E cast_e => Cast_E (Cast.Cast_E_trans _ _ _ _ trans cast_e Vars Es)
  end.

Inductive Reduce : E -> E -> Prop :=
| FJ_S_Reduce : forall e e', FJ_Reduce _ _ _ _ _ _ cFJ _ _ cFJ_E _ _ CT _ fields mbody_build_te 
  mb_ext build_mb_ext map_mbody Empty trans e e' -> Reduce e e'
| FJ_C_Reduce : forall e e', 
  FJ_Congruence_Reduce _ _ _ _ ty_ext E _ cFJ_E Reduce Congruence_List_Reduce e e' -> Reduce e e'
| Cast_Reduce : forall e e', 
  Cast.Cast_Reduce _ _ _ cFJ _ _ Cast_E subtype nat nat nat m_call_ext cFJ_E Empty e e' ->
  Reduce e e'
| Cast_C_Reduce : forall e e', Cast_C_Reduce _ _ _ Cast_E Reduce e e' -> Reduce e e'
with Congruence_List_Reduce : list E -> list E -> Prop :=
| FJ_Reduce_List : forall es es', Reduce_List _ Reduce Congruence_List_Reduce es es' -> 
  Congruence_List_Reduce es es'.

Section Proofs.

  Variable (WF_CT : forall (c : nat) l,
    CT c = Some l ->
    cFJ.L_WF nat nat nat nat ty_ext Ty cFJ E md_ext cld_ext CT
    Context subtype WF_Type fields E_WF Empty Update ce_build_cte
    Meth_build_context Meth_WF_Ext override L_WF_Ext
    L_build_context l)
  (lookup_update_eq : forall gamma X ty, lookup (Update gamma X ty) X ty) 
  (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
    lookup (Update gamma Y ty') X ty)
  (lookup_update_neq' : forall gamma Y X ty ty', lookup (Update gamma Y ty') X ty -> X <> Y -> 
    lookup gamma X ty)
  (lookup_Empty : forall X ty, ~ lookup Empty X ty)
  (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty')
  (app_context : Context -> Context -> Context)
    (Lookup_dec : forall gamma x, (exists ty, lookup gamma x ty) \/ (forall ty, ~ lookup gamma x ty))
    (Lookup_app : forall gamma delta x ty, lookup gamma x ty -> lookup (app_context gamma delta) x ty)
    (Lookup_app' : forall gamma delta x ty, (forall ty', ~ lookup gamma x ty') -> lookup delta x ty -> 
      lookup (app_context gamma delta) x ty).

  Definition Fields_eq_def gamma ty fds (fields_fds : fields gamma ty fds) := 
    forall gamma' fds', fields gamma' ty fds' -> fds = fds'.

  Lemma cFJ_inject : forall ty ty', cFJ ty = cFJ ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.

  Lemma fields_invert : forall (gamma : Context) (ty : FJ_Ty nat ty_ext)
    (fds : list (cFJ.FD nat Ty)),
    fields gamma (cFJ ty) fds ->
    cFJ.FJ_fields nat nat nat nat ty_ext Ty cFJ E md_ext
    cld_ext CT Context fields fields_build_te fields_build_tys gamma
    (cFJ ty) fds.
    intros gamma ty fds fields_fds; inversion fields_fds; subst; assumption.
  Qed.

  Definition fields_build_te_id := FJ_fields_build_te_id.
  Definition fields_build_tys_id := FJ_fields_build_tys_id Ty.

  Fixpoint Fields_eq gamma ty fds (fields_fds : fields gamma ty fds) : Fields_eq_def _ _ _ fields_fds :=
    match fields_fds return Fields_eq_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_Fields_eq _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert
      fields_build_te_id fields_build_tys_id _ _ _ FJ_case Fields_eq
    end.

  Definition Fields_Build_tys_len := FJ_Fields_Build_tys_len Ty.
  Definition WF_fields_map_id' := FJ_WF_fields_map_id' _ _ _ cFJ Context.

  Definition WF_fields_map_sub := FJ_WF_fields_map_sub _ _ _ _ _ _ cFJ _ _ _ CT Context subtype build_te
    cFJ_sub fields Empty Fields_eq.

  Fixpoint WF_fields_map_id gamma ty fds (fields_fds : fields gamma ty fds) :=
    match fields_fds return WF_fields_map_id_P _ _ _ _ cFJ _ fields _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fields_map_id _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert
      Fields_Build_tys_len  _ _ _ FJ_case WF_fields_map_id
    end.

  Fixpoint parent_fields_names_eq gamma ty fds (fields_fds : fields gamma ty fds) :=
    match fields_fds return parent_fields_names_eq_P _ nat _ _ cFJ _ fields _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_parent_fields_names_eq _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert 
      Fields_Build_tys_len _ _ _ FJ_case parent_fields_names_eq
    end.

  Fixpoint fds_distinct gamma ty fds (fields_fds : fields gamma ty fds) :=
    match fields_fds return fds_distinct_P _ _ _ fields _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fds_distinct _ _ _ _ _ Ty cFJ _ _ _ CT Context
      subtype WF_Type fields fields_build_te fields_build_tys FJ_fields E_WF Empty Update
      ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
      WF_CT parent_fields_names_eq Fields_Build_tys_len _ _ _ FJ_case fds_distinct
    end.

  Definition update_list := cFJ.update_list nat Ty Context Update.

  Definition WF_mtype_map_sub :=  FJ_WF_mtype_map_sub _ _ _ _ _ _ cFJ _ _ _ CT Context
        subtype build_te cFJ_sub.

  Definition Weaken_WF_fields_map := FJ_Weaken_WF_fields_map _ _ _ Empty Update.
 
  Definition Weaken_WF_mtype_ty_0_map := FJ_Weaken_WF_mtype_ty_0_map _ _ _ Empty Update.

  Definition Weaken_WF_mtype_Us_map := FJ_Weaken_WF_mtype_Us_map _ _ _ Empty Update.

  Definition Weaken_WF_mtype_U_map := FJ_Weaken_WF_mtype_U_map _ _ _ Empty Update.

  Definition Weaken_WF_mtype_ext := FJ_Weaken_WF_mtype_ext _ _ _ Empty Update.

  Definition Weaken_WF_Class_Ext := FJ_Weaken_WF_Class_Ext nat Ty _ Empty Update.

  Definition Weaken_WF_Object_Ext := FJ_Weaken_WF_Object_Ext nat Ty _ Empty Update.

  Fixpoint Weaken_WF_Type_update_list gamma ty (WF_ty : WF_Type gamma ty) :
    FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty :=
    match WF_ty in WF_Type gamma ty return FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty with 
      | cFJ_WF_Type gamma' ty' wf_ty' => 
        FJ_Weaken_WF_Type_update_list nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type cFJ_WF_Type Empty Update Weaken_WF_Object_Ext
        (fun gamma cld te wf_cld gamma' Vars _ => Weaken_WF_Class_Ext gamma Vars cld te wf_cld) gamma' ty' wf_ty'
    end.

  Fixpoint Weaken_Subtype_update_list gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T return Weaken_Subtype_update_list_P _ _ _ subtype Empty Update _ _ _ sub_S_T with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_Weaken_Subtype_update_list _ _ _ _ _ _ 
        cFJ _ _ _ CT _ subtype build_te cFJ_sub Empty Update _ _ _ sub_S_T' Weaken_Subtype_update_list
    end.
  
  Definition WF_Cast_Map_Weaken := Cast_WF_Cast_Map_Weaken Ty Context nat Empty Update.

  Lemma Ty_eq_dec : forall (S T : Ty), {S = T} + {S <> T}.
    destruct S; destruct T; destruct f; destruct f0; 
      destruct f; destruct f0; destruct c; destruct c0;
        try destruct (eq_nat_dec n n0); subst; first [left; auto; fail | right; congruence].
  Qed.

  Variable (subtype_dec : forall gamma S T, subtype gamma S T \/ ~ subtype gamma S T).

  Fixpoint Weakening gamma e ty (WF_e : E_WF gamma e ty) :=
    match WF_e return Weakening_P _ _ _ _ E_WF Empty Update _ _ _ WF_e with
      | FJ_E_WF gamma e ty FJ_case => FJ_Weakening _ _ _ _ _ _ cFJ _ _ cFJ_E _ _
        subtype WF_Type fields mtype
        E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map
        WF_mtype_ext Empty FJ_E_WF Update eq_nat_dec lookup_update_eq
        lookup_update_neq lookup_update_neq' lookup_Empty lookup_id Weaken_WF_fields_map
        Weaken_WF_mtype_ty_0_map Weaken_WF_mtype_Us_map Weaken_WF_mtype_U_map
        Weaken_Subtype_update_list Weaken_WF_mtype_ext Weaken_WF_Type_update_list _ _ _ 
        FJ_case Weakening
      | Cast_Exp_WF gamma e ty Cast_case => Cast_Weakening _ _ _ cFJ _ _ Cast_E
        E_WF WF_Cast_map subtype Cast_Exp_WF _ _ _ _ _ CT build_te Empty Update cFJ_sub
        Weaken_Subtype_update_list subtype_dec Ty_eq_dec WF_Cast_Map_Weaken gamma e ty Cast_case Weakening
    end.

  Lemma E_trans_Wrap : forall e vars es', 
    trans (cFJ_E e) vars es' = cFJ.FJ_E_trans _ _ _ _ _ _ _ cFJ_E trans eq_nat_dec e vars es'.
    simpl; reflexivity.
  Qed.

  Definition WF_fields_map_update_list := FJ_WF_fields_map_update_list _ _ _ Update.

  Definition WF_mtype_ty_0_map_Weaken_update_list :=
    FJ_WF_mtype_ty_0_map_Weaken_update_list _ _ _ Update.
    
  Definition WF_mtype_U_map_Weaken_update_list :=
    FJ_WF_mtype_U_map_Weaken_update_list _ _ _ Update.

  Definition WF_mtype_Us_map_Weaken_update_list :=
    FJ_WF_mtype_Us_map_Weaken_update_list _ _ _ Update.
  
  Definition WF_mtype_ty_0_map_total : forall delta S T, subtype delta S T -> forall T',
    WF_mtype_ty_0_map delta T T' -> exists S', WF_mtype_ty_0_map delta S S' := 
      fun delta S T sub_S_T T' map_T => FJ_WF_mtype_ty_0_map_total Ty Context delta S.

  Fixpoint Subtype_Update_list_id gamma S T (sub_S_T : subtype gamma S T) := 
        match sub_S_T with
          | cFJ_sub gamma' S' T' sub_S_T' => 
            FJ_Subtype_Update_list_id _ _ _ _ _ _ cFJ _ _ _ CT _ subtype build_te
            cFJ_sub Update gamma' S' T' sub_S_T' Subtype_Update_list_id
        end.

  Definition WF_mtype_ext_update_list_id := FJ_WF_mtype_ext_update_list_id _ _ _ Update.

  Definition WF_Object_ext_Update_Vars_id := FJ_WF_Object_ext_Update_Vars_id _ _ _ Update.

  Definition WF_Class_ext_Update_Vars_id :=  FJ_WF_Class_ext_Update_Vars_id nat Ty _ Update.
  
  Fixpoint WF_Type_update_list_id gamma ty (WF_ty : WF_Type gamma ty) :=
    match WF_ty in WF_Type gamma ty return WF_Type_update_list_id_P _ _ _ WF_Type Update gamma ty WF_ty with 
      | cFJ_WF_Type gamma' ty' wf_ty' => FJ_WF_Type_update_list_id _ _ _ _ _ _ cFJ
        _ _ _ CT _ wf_class_ext wf_object_ext  WF_Type cFJ_WF_Type Update WF_Object_ext_Update_Vars_id 
        WF_Class_ext_Update_Vars_id gamma' ty' wf_ty'
    end.

  Definition WF_fields_map_tot := FJ_WF_fields_map_tot _ _ _ cFJ Context.

  Definition fields_build_te_tot := FJ_fields_build_te_tot.

  Definition fields_build_tys_tot := FJ_fields_build_tys_tot Ty.

  Definition WF_fields_map_id'' := FJ_WF_fields_map_id'' Ty Context.

  Definition fields_build_te_id' := fun gamma ce c d te te' te'' te3 te4 te5 => 
    FJ_fields_build_te_id' nat ty_ext Ty cFJ Context id 
    gamma ce c d te te' te'' te3 te4 te5.
    
   Fixpoint fields_id gamma ty fds (ty_fields : fields gamma ty fds) := 
    match ty_fields with 
      | FJ_fields gamma' ty' fds' FJ_ty'_fields =>
        FJ_fields_id _ _ _ _ _ _ cFJ _ _ _ CT Context fields fields_build_te 
        fields_build_tys FJ_fields cFJ_inject fields_invert  
        fields_build_te_id fields_build_tys_id  gamma' ty' fds' FJ_ty'_fields fields_id
    end.

   Definition WF_mtype_ty_0_map_id := FJ_WF_mtype_ty_0_map_id Ty Context.
   
   Definition WF_mtype_ty_0_map_tot := FJ_WF_mtype_ty_0_map_tot Ty Context subtype.

   Definition WF_mtype_ty_0_map_cl_id := 
     FJ_WF_mtype_ty_0_map_cl_id _ _ _ cFJ Context cFJ_inject.

   Definition WF_mtype_ty_0_map_cl_id' := 
     FJ_WF_mtype_ty_0_map_cl_id' _ _ _ cFJ Context. 

   Definition m_eq_dec := eq_nat_dec.
   
   Definition build_te_build_ty_0_id := FJ_build_te_build_ty_0_id nat _ _ cFJ Context (@id _).

   Definition WF_mtype_Us_map_len := FJ_WF_mtype_Us_map_len Ty Context.

   Definition mtype_build_tys_len := FJ_mtype_build_tys_len nat Ty.

   Definition methods_build_te_id := FJ_methods_build_te_id.

   Definition WF_Obj_ext_Lem := FJ_WF_Obj_ext_Lem Context.
   
   Definition WF_cld_ext_Lem := FJ_WF_Cld_ext_Lem Context.
   
   Fixpoint WF_Type_par_Lem gamma ty (WF_ty : WF_Type gamma ty) :=
     match WF_ty return WF_Type_par_Lem_P _ _ _ _ ty_ext Ty cFJ _ _ _ CT Context 
       wf_object_ext WF_Type mtype_build_te L_build_context _ _ WF_ty with 
       cFJ_WF_Type gamma ty WF_base => 
       FJ_WF_Type_par_Lem _ _ _ _ _ _ cFJ _ _ _ CT Context wf_class_ext
       wf_object_ext WF_Type cFJ_WF_Type mtype_build_te
       L_build_context cFJ_inject 
       (fun gamma a b c te d e f g h i j k l m => WF_Obj_ext_Lem gamma te)
       gamma ty WF_base
     end.

   Definition WF_Type_par_Lem' delta ty (WF_ty : WF_Type delta ty) := 
     match WF_ty in (WF_Type delta ty) return 
       WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty cFJ E _ _ CT _ wf_class_ext
       WF_Type mtype_build_te L_build_context delta ty WF_ty with 
       | cFJ_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par_Lem' _ _ _ _ _ _ cFJ
         _ _ _ CT Context wf_class_ext wf_object_ext WF_Type cFJ_WF_Type
         mtype_build_te L_build_context cFJ_inject 
         (fun gamma ce te0 _ te'' c0 fds k' mds c1 gamma0 ce' te' cld' _ _ _ _ _ _ => 
           WF_cld_ext_Lem gamma0 ce' te'')
         gamma ty WF_base
     end.     

   Definition WF_Type_par delta ty (WF_ty : WF_Type delta ty) := 
     match WF_ty in (WF_Type delta ty) return 
       WF_Type_par_P _ _ _ _ ty_ext Ty cFJ E _ _ CT _ WF_Type mtype_build_te
       L_build_context delta ty WF_ty with 
       | cFJ_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par _ _ _ _ _ _ cFJ _ _ _ CT Context 
         wf_class_ext wf_object_ext WF_Type cFJ_WF_Type mtype_build_te
         L_build_context cFJ_inject WF_Type_par_Lem WF_Type_par_Lem' gamma ty WF_base
     end.

   Definition build_te_id := FJ_build_te_id.

   Definition bld_te_eq_fields_build_te := FJ_bld_te_eq_fields_build_te.

   Definition FJ_WF_fields_map_id := FJ_WF_fields_map_id _ _ _ cFJ Context.

   Fixpoint Lem_2_8 gamma S T (sub_S_T : subtype gamma S T) :=
     match sub_S_T with
       | cFJ_sub gamma' S' T' sub_S_T' =>
         FJ_Lem_2_8 nat nat nat nat ty_ext Ty cFJ E _ _
         CT Context subtype build_te cFJ_sub fields fields_build_te
         fields_build_tys FJ_fields WF_fields_map Empty WF_fields_map_tot
         fields_build_tys_tot WF_fields_map_id'' FJ_WF_fields_map_id bld_te_eq_fields_build_te gamma' S' T' sub_S_T' Lem_2_8
     end.

    Fixpoint Weaken_mtype gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
      match mtype_m with 
        FJ_mtype gamma' m' ty' mty' fj_mtype_m => FJ_Weaken_mtype _ _ _ _ _ _ cFJ _ _ _ _ 
        CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye FJ_mtype Empty 
        gamma' m' ty' mty' fj_mtype_m Weaken_mtype
      end.

    Fixpoint Subtype_Weaken gamma S T (sub_S_T : subtype gamma S T) :=
        match sub_S_T with
          | cFJ_sub gamma' S' T' sub_S_T' => 
            FJ_Subtype_Weaken _ _ _ _ _ _ cFJ _ _ _ CT _ subtype build_te
            cFJ_sub Empty gamma' S' T' sub_S_T' Subtype_Weaken
        end.

    Definition WF_mtype_ty_0_map_cl_refl := FJ_WF_mtype_ty_0_map_cl_refl _ _ _ cFJ Context.

    Definition build_te_refl := FJ_build_te_refl.

    Definition WF_mtype_U_map_trans := FJ_WF_mtype_U_map_trans Ty Context.
    Definition WF_mtype_Us_map_trans := FJ_WF_mtype_Us_map_trans Ty Context.
    Definition WF_mtype_ext_trans := FJ_WF_mtype_ext_trans Context.
    Definition mtype_build_tys_refl := FJ_mtype_build_tys_refl nat Ty.

    Definition build_V' := FJ_build_V' _ _ _ _ _ _ cFJ _ _ _ _ _ CT _ subtype build_te
      cFJ_sub wf_class_ext wf_object_ext WF_Type mtype mtype_build_tys mtype_build_mtye
      WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty Update
      Meth_build_context Meth_WF_Ext L_build_context WF_mtype_ty_0_map_id
      WF_mtype_ty_0_map_cl_refl build_te_refl WF_mtype_U_map_trans WF_mtype_Us_map_trans
      WF_mtype_ext_trans mtype_build_tys_refl id.

    Definition mtype_build_tys_tot := FJ_mtype_build_tys_tot nat Ty.
    Definition mtype_build_mtye_tot := FJ_mtype_build_mtye_tot nat Ty.

    Lemma WF_Type_invert : forall delta S, WF_Type delta (cFJ S) -> 
      FJ_WF_Type _ _ _ _ _ _ cFJ _ _ _ CT Context wf_class_ext wf_object_ext delta (cFJ S).
      intros; inversion H; subst; assumption.
    Qed.

  Fixpoint Lem_2_9 gamma S T (sub_S_T : subtype gamma S T) : 
    Lem_2_9_P _ _ _ _ _ subtype mtype WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T :=
    match sub_S_T return Lem_2_9_P _ _ _ _ _ subtype mtype WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T with
      | cFJ_sub gamma S' T' sub_S_T' => cFJ.FJ_Lem_2_9 _ _ _ _ _ _ cFJ
        _ _ _ _ _ CT _ subtype build_te cFJ_sub wf_class_ext wf_object_ext
        WF_Type fields mtype mtype_build_te mtype_build_tys
        mtype_build_mtye FJ_mtype E_WF WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty
        Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
        WF_CT cFJ_inject WF_mtype_ty_0_map_total mtype_build_tys_len
        WF_Type_invert WF_mtype_ty_0_map_id eq_nat_dec
        build_te_build_ty_0_id WF_mtype_ty_0_map_cl_refl mtype_build_tys_tot 
        mtype_build_mtye_tot build_V' gamma S' T' sub_S_T' Lem_2_9
    end.
                     
  Definition sub_WF_Cast_Map := Cast_sub_WF_Cast_Map _ _ subtype.
      
  Fixpoint Subtype_Update_list_id' gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T in (subtype gamma S T) return 
      (Cast.Subtype_Update_list_id'_P _ _ subtype nat Update gamma S T sub_S_T) with
      | cFJ_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Update_list_id' _ _ _ _ _ _ subtype _ _ _ _ _ CT
        build_te Update cFJ_sub gamma' S' T' sub_S_T' Subtype_Update_list_id'
    end.

  Lemma Cast_E_trans_Wrap : forall (e : Cast.Cast_E nat ty_ext E) (vars : list (Var nat)) (es' : list E),
    trans (Cast_E e) vars es' =
    Cast_E (Cast_E_trans nat ty_ext E nat trans e vars es').
    simpl; reflexivity.
  Qed.

  Definition WF_Cast_map_update_list := Cast_WF_Cast_map_update_list Ty _ nat Update.

    Fixpoint Term_subst_pres_typ gamma e T (WF_e : E_WF gamma e T) :=
      match WF_e in E_WF gamma e T return
        cFJ.Term_subst_pres_typ_P _ _ _ _ subtype E_WF Update trans gamma e T WF_e with 
        | FJ_E_WF gamma e ty FJ_case => FJ_Term_subst_pres_typ _ _ _ _ _ _ 
          cFJ _ _ cFJ_E mty_ext _ _ CT _ subtype build_te
          cFJ_sub WF_Type fields mtype 
          E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
          WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF Update
          trans eq_nat_dec lookup_update_eq lookup_update_neq'
          lookup_id E_trans_Wrap Lem_2_8 Lem_2_9 WF_fields_map_update_list
          WF_mtype_ty_0_map_Weaken_update_list WF_mtype_U_map_Weaken_update_list
          WF_mtype_Us_map_Weaken_update_list WF_mtype_ext_update_list_id
          WF_mtype_ty_0_map_total Subtype_Update_list_id WF_Type_update_list_id 
          gamma e ty FJ_case Term_subst_pres_typ
        | Cast_Exp_WF gamma e ty Cast_case => Cast_Term_subst_pres_typ _ _ _ _
          _ _ Cast_E E_WF WF_Cast_map subtype Cast_Exp_WF _ _ _ _ _ CT build_te Update
          cFJ_sub subtype_dec Ty_eq_dec trans Cast_E_trans_Wrap 
          Subtype_Update_list_id Subtype_Update_list_id'
          WF_Cast_map_update_list WF_mtype_ty_0_map_total sub_WF_Cast_Map
          _ _ _ Cast_case Term_subst_pres_typ
      end.
     
    Lemma mtype_invert : forall (gamma : Context) (m0 : nat) (te : FJ_ty_ext) 
      (c : nat) (mty : Mty Ty mty_ext),
      mtype gamma m0 (cFJ (ty_def nat FJ_ty_ext te (cl nat c))) mty ->
      cFJ.FJ_mtype nat nat nat nat FJ_ty_ext Ty cFJ E mty_ext
      md_ext cld_ext CT Context mtype mtype_build_te mtype_build_tys
      mtype_build_mtye gamma m0
      (cFJ (ty_def nat FJ_ty_ext te (cl nat c))) mty.
      intros; inversion H; subst; assumption.
    Qed.

    Definition WF_mtype_ty_0_map_tot' := FJ_WF_mtype_ty_0_map_tot' _ _ _ cFJ Context.
    
    Definition WF_mtype_ty_0_map_cl_id'' := FJ_WF_mtype_ty_0_map_cl_id'' _ _ _ cFJ Context.

    Definition Build_S0'' := FJ_Build_S0'' _ _ _ _ cFJ _ _ subtype WF_Type
      E_WF Empty Update Subtype_Weaken Weakening Subtype_Update_list_id FJ_te_eq (@id _).
    
    Definition WF_mb_ext := FJ_WF_mb_ext Context.

    Definition WF_Build_mb_ext : forall (ce : cld_ext) (me : md_ext) 
                       (gamma : Context) (te te' : ty_ext) 
                       (c : _) (vds : list (cFJ.VD _ Ty)) 
                       (T0 : Ty) (delta : Context) 
                       (D D' : Ty) (mtye : mty_ext) 
                       (mce : m_call_ext) (mbe : mb_ext) 
                       (Ds Ds' : list Ty) (te'' : ty_ext)
                       (Vars : list (Var _ * Ty)),
                     Meth_WF_Ext gamma ce me ->
                     Meth_build_context ce me
                       (update_list Empty
                          ((this _, cFJ (ty_def _ ty_ext te' (cl _ c)))
                           :: map
                                (fun Tx : cFJ.VD _ Ty =>
                                 match Tx with
                                 | vd ty x => (var _ x, ty)
                                 end) vds)) gamma ->
                     WF_Type delta (cFJ (ty_def _ ty_ext te (cl _ c))) ->
                     build_mb_ext ce te mce me mbe ->
                     mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) ->
                     WF_mtype_U_map delta mce mtye D D' ->
                     WF_mtype_ext delta mce mtye ->
                     WF_mtype_Us_map delta mce mtye Ds Ds' ->
                     List_P1
                       (fun Tx : cFJ.VD _ Ty =>
                        match Tx with
                        | vd ty _ => WF_Type gamma ty
                        end) vds ->
                     zip
                       (this _
                        :: map
                             (fun Tx : cFJ.VD _ Ty =>
                              match Tx with
                              | vd _ x => var _ x
                              end) vds)
                       (cFJ (ty_def _ ty_ext te'' (cl _ c)) :: Ds') (@pair _ _) =
                     Some Vars ->
                     mtype_build_tys ce te'' T0 vds me
                       (map
                          (fun vd'  =>
                           match vd' with
                           | vd ty _ => ty
                           end) vds) Ds ->
                     WF_mb_ext
                       (update_list delta Vars) mbe. 
    intros; constructor.
  Qed.

    Definition Lem_2_12 := FJ_Lem_2_12 _ _ _ _ _ _ _ _ _ _ _ _ CT 
      Context subtype build_te cFJ_sub _ _ WF_Type cFJ_WF_Type fields mtype mtype_build_te
      mtype_build_tys mtype_build_mtye mbody_build_te
      mb_ext build_mb_ext map_mbody E_WF WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext
      Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context WF_CT cFJ_inject 
      Build_S0'' WF_mb_ext WF_Build_mb_ext WF_mtype_Us_map_len mtype_build_tys_len methods_build_te_id WF_Type_par
      build_te_id mtype_invert WF_mtype_ty_0_map_cl_id'' WF_mtype_ty_0_map_tot' WF_Type_invert.
    
    Lemma EWrap_inject : forall e e', cFJ_E e = cFJ_E e' -> e = e'.
      intros; injection H; intros; assumption.
    Qed.
    
    Lemma FJ_E_WF_invert : forall gamma (e : FJ_E _ _ _ _ _ _ _ ) c0, 
      E_WF gamma (cFJ_E e) c0 -> cFJ.FJ_E_WF _ _ _ _ _ Ty cFJ _ _ cFJ_E mty_ext
      Context subtype WF_Type fields mtype
      E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
      WF_mtype_ext Empty gamma (cFJ_E e) c0.
      intros; inversion H; subst; try assumption.
      inversion H0.
    Qed.

    Definition preservation_def := cFJ.preservation Ty E Context subtype E_WF Reduce.
    
    Definition Reduce_List_preservation es es' (red_es : Congruence_List_Reduce es es') :=
      cFJ.Reduce_List_preservation _ _ _ subtype E_WF Congruence_List_Reduce es es' red_es.

    Lemma FJ_E_WF_new_invert : forall gamma e T T0, 
      E_WF gamma (cFJ_E (cFJ.new nat nat nat nat ty_ext E m_call_ext T e)) T0 ->
      cFJ T = T0.
      intros; inversion H; subst.
      inversion H0; subst.
      destruct te; reflexivity.
      inversion H0.
    Qed.

    Lemma Cast_E_WF_invert : forall gamma e c0, E_WF gamma (Cast_E e) c0 -> 
      Cast.Cast_E_WF _ _ _ cFJ _ _ Cast_E E_WF WF_Cast_map subtype gamma (Cast_E e) c0.
      intros; inversion H; subst.
      inversion H0.
      assumption.
    Qed.

    Lemma Cast_E_inject : forall e e', Cast_E e = Cast_E e' -> e = e'.
      intros; congruence.
    Qed.

    
    Definition WF_Cast_Map_total := Cast_WF_Cast_Map_total _ _ subtype.

    Fixpoint preservation e e' (red_e : Reduce e e') : preservation_def _ _ red_e :=
      match red_e with 
        |  FJ_S_Reduce t t' red_t => FJ_pres _ _ _ _ _ _ cFJ _ _ 
          cFJ_E _ _ _ CT _ subtype build_te cFJ_sub WF_Type fields
          mtype mbody_build_te mb_ext build_mb_ext map_mbody E_WF lookup
          WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map
          WF_mtype_ext Empty FJ_E_WF Update trans
          Reduce FJ_S_Reduce FJ_E_WF_invert EWrap_inject
          Fields_eq fds_distinct WF_fields_map_id WF_fields_map_id'
          WF_fields_map_sub Subtype_Weaken WF_mtype_map_sub Term_subst_pres_typ WF_mb_ext
          Lem_2_12 t t' red_t
        | FJ_C_Reduce e e' fj_red_e' => FJ_C_preservation _ _ _ _ ty_ext _ cFJ _ _ cFJ_E _ _ _ CT
          _ subtype build_te cFJ_sub WF_Type fields mtype E_WF lookup WF_fields_map
          WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF 
          Reduce Congruence_List_Reduce FJ_C_Reduce FJ_E_WF_invert EWrap_inject
          Lem_2_8 Lem_2_9 WF_mtype_ty_0_map_tot e e' fj_red_e'
          preservation (fix preservation_list (es es' : list E) (red_es : Congruence_List_Reduce es es') : 
            Reduce_List_preservation _ _ red_es :=
            match red_es return Reduce_List_preservation _ _ red_es with
              FJ_Reduce_List es es' red_es' => FJ_C_List_preservation _ _ _ _ _ _ cFJ _ _ _ 
              CT _ subtype build_te cFJ_sub E_WF Reduce Congruence_List_Reduce FJ_Reduce_List 
              es es' red_es' preservation preservation_list end)      
        | Cast_Reduce e e' cast_red_e => Cast_preservation' _ _ _ cFJ _ _ Cast_E
          E_WF WF_Cast_map subtype Reduce _ _ _ _ _ _ cFJ_E CT build_te Empty Cast_Reduce 
          cFJ_sub Cast_E_WF_invert Cast_E_inject FJ_E_WF_new_invert
          Subtype_Weaken WF_mtype_map_sub e e' cast_red_e
        | Cast_C_Reduce e e' cast_c_red_e => Cast_C_preservation' _ _ _ _ _ _ Cast_E
          E_WF WF_Cast_map subtype Cast_Exp_WF _ _ _ _ _ CT build_te Reduce Cast_C_Reduce
          cFJ_sub subtype_dec Ty_eq_dec WF_Cast_Map_total sub_WF_Cast_Map Cast_E_WF_invert Cast_E_inject
          e e' cast_c_red_e preservation       
      end.

    Inductive subexpression : E -> E -> Prop :=
      FJ_subexpression_Wrap : forall e e', 
        FJ_subexpression _ _ _ _ _ _ _ cFJ_E subexpression subexpression_list e e' -> subexpression e e'
  | Cast_subexpression_Wrap : forall e e', 
    Cast_subexpression _ _ _ Cast_E subexpression e e' -> subexpression e e'
    with subexpression_list : E -> list E -> Prop :=
      subexpression_list_Wrap : forall e es, FJ_subexpression_list _ subexpression subexpression_list e es ->
        subexpression_list e es.

    Definition progress_1_P := cFJ.progress_1_P _ _ _ _ _ _ cFJ _ _ cFJ_E _ fields
      E_WF Empty subexpression.

    Definition progress_1_list_P := cFJ.progress_1_list_P _ _ _ _ _ _ cFJ _ _ cFJ_E 
      _ fields E_WF Empty subexpression_list.
        
    Lemma subexp_invert : forall (e : E) e',
      subexpression e (cFJ_E e') ->
      FJ_subexpression nat nat nat nat ty_ext E m_call_ext cFJ_E subexpression subexpression_list e (cFJ_E e').
      clear; intros; inversion H; subst; auto.
      inversion H0.
    Qed.
    
    Lemma subexpression_list_nil : forall e : E, ~ subexpression_list e nil.
      clear; unfold not; intros; inversion H; subst;
        eapply (FJ_subexpression_list_nil E subexpression subexpression_list _ H0).
    Qed.
    
    Lemma subexpression_list_destruct : forall e e' es, subexpression_list e (e' :: es) -> 
      (subexpression e e') \/ (subexpression_list e es).
      clear; intros; inversion H; subst; eapply FJ_subexpression_list_destruct; eassumption.
    Qed.
    
    Lemma FJ_Cast_discriminate : forall (e : FJ_E _ _ _ _ ty_ext E m_call_ext)
      (S : FJ_Ty _ ty_ext) (e' : E), cFJ_E e <> Cast_E (cast _ ty_ext E S e').
      congruence.
    Qed.

  Lemma Cast_subexp_invert : forall (e : E) S e',
    subexpression e (Cast_E (cast _ _ _ S e')) -> 
    Cast_subexpression _ _ _ Cast_E subexpression e (Cast_E (cast _ _ _ S e')) \/ e = Cast_E (cast _ _ _ S e').
    clear; intros; inversion H; subst; auto; inversion H0; tauto.
  Qed.

    Fixpoint progress_1 gamma e T (WF_e : E_WF gamma e T) :
      progress_1_P gamma e T WF_e :=
      match WF_e with 
        | FJ_E_WF gamma e ty FJ_case => cFJ.progress_1 _ _ _ _ _ _ cFJ _ _ cFJ_E _ _ subtype
          WF_Type fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
          WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert EWrap_inject
          WF_fields_map_id WF_fields_map_id' subexpression subexpression_list 
          subexp_invert subexpression_list_nil subexpression_list_destruct gamma e ty FJ_case progress_1
        | Cast_Exp_WF gamma e ty Cast_case => Cast_progress_1 _ _ _ _
          _ _ Cast_E E_WF WF_Cast_map subtype Cast_Exp_WF _ _ _ _ cFJ_E Empty Cast_E_inject fields 
          subexpression Cast_subexp_invert FJ_Cast_discriminate gamma e ty Cast_case progress_1
      end.
    
    Definition progress_2_P := cFJ.progress_2_P _ _ _ _ _ _ cFJ _ _ cFJ_E _ _ CT _ 
      mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty subexpression.
    
    Definition progress_2_list_P := cFJ.progress_2_list_P _ _ _ _ _ _ cFJ _ _ cFJ_E _ _ 
      CT _ mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty 
      subexpression_list.
    
    Definition WF_mtype_ty_0_map_Empty_refl := FJ_WF_mtype_ty_0_map_Empty_refl _ _ _ cFJ Context.
    
    Definition mtype_mbody_build_te := FJ_mtype_mbody_build_te.
        
    Definition map_mbody_tot := FJ_map_mbody_tot nat Ty E.

    Definition build_mb_ext_tot := FJ_build_mb_ext_tot nat Ty.

  Fixpoint mtype_implies_mbody gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
    match mtype_m with 
      FJ_mtype gamma' m' ty' mty' fj_mtype_m => FJ_mtype_implies_mbody _ _ _ _ _ _ cFJ
      _ _ _ _ _ CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye
      FJ_mtype mbody_build_te mb_ext build_mb_ext map_mbody 
      Empty cFJ_inject mtype_build_tys_len map_mbody_tot
      mtype_mbody_build_te build_mb_ext_tot gamma' m' ty' mty' fj_mtype_m mtype_implies_mbody
    end.

  Fixpoint progress_2 gamma e T (WF_e : E_WF gamma e T) :
    progress_2_P gamma e T WF_e :=
    match WF_e with 
      | FJ_E_WF gamma e ty FJ_case => FJ_progress_2 _ _ _ _ _ _ cFJ _ _ cFJ_E 
        _ _ _ CT _ subtype WF_Type fields mtype mbody_build_te mb_ext build_mb_ext
        map_mbody E_WF lookup WF_fields_map WF_mtype_ty_0_map
        WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert
        EWrap_inject WF_mtype_Us_map_len subexpression subexpression_list
        subexp_invert subexpression_list_nil subexpression_list_destruct
        WF_mtype_ty_0_map_Empty_refl mtype_implies_mbody gamma e ty FJ_case progress_2
      | Cast_Exp_WF gamma e ty Cast_case => Cast_progress_2 _ _ _ _
        _ _ Cast_E E_WF WF_Cast_map subtype Cast_Exp_WF _ _ _ _ _ _ cFJ_E CT Empty Cast_E_inject  
        subexpression mbody_build_te mb_ext build_mb_ext map_mbody
        Cast_subexp_invert FJ_Cast_discriminate gamma e ty Cast_case progress_2
    end.

  End Proofs.
