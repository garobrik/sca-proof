Require Import FJ_tactics.
Require Import cFJ.
Require Import State.
Require Import List.
Require Import Arith.

Definition CL := cFJ.CL nat.

Inductive Ty : Set :=
  cFJ : FJ_Ty nat (FJ_ty_ext) -> Ty.


Definition ty_ext := FJ_ty_ext.
Definition mty_ext := FJ_mty_ext.
Definition cld_ext := FJ_cld_ext.
Definition m_call_ext := FJ_m_call_ext.

Inductive E : Set :=
  Base_E : FJ_E nat nat nat nat ty_ext E m_call_ext -> E.

Inductive S : Set :=
  Base_S : LJ_S nat nat E S -> S.

Definition md_ext := LJ_md_ext S FJ_md_ext.
Definition mb_ext := LJ_mb_ext S FJ_mb_ext.

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
  cFJ_sub : forall gamma ty ty', cFJ.FJ_subtype nat nat nat nat _ Ty cFJ E md_ext cld_ext 
    CT Context subtype build_te gamma ty ty' ->
    subtype gamma ty ty'.

Definition wf_class_ext := FJ_wf_class_ext Context.
Definition wf_object_ext := FJ_wf_object_ext Context.

Inductive WF_Type : Context -> Ty -> Prop :=
  Base_WF_Type : forall gamma ty, FJ_WF_Type _ _ _ _ _ _ cFJ _ _ _ CT Context 
    wf_class_ext wf_object_ext  gamma ty -> WF_Type gamma ty.

Definition fields_build_te := FJ_fields_build_te.
Definition fields_build_tys := FJ_fields_build_tys Ty.

Inductive fields : Context -> Ty -> list FD -> Prop :=
  FJ_fields : forall gamma ty fds, cFJ.FJ_fields _ _ _ _ _ Ty cFJ _ _ _
    CT Context fields fields_build_te fields_build_tys gamma ty fds -> fields gamma ty fds.

Definition mtype_build_te := FJ_mtype_build_te.

Definition mtype_build_tys := fun ce te ty vds (mde : md_ext) tys => FJ_mtype_build_tys nat Ty ce te ty vds (snd mde) tys.

Definition mtype_build_mtye := fun ce te ty vds (mde : md_ext) mtye => 
  FJ_mtype_build_mtye nat Ty ce te ty vds (snd mde) mtye.

Inductive mtype : Context -> nat -> Ty -> MTy -> Prop :=
  FJ_mtype : forall gamma m ty mty, cFJ.FJ_mtype _ _ _ _ _ Ty cFJ _ _ _ _ CT Context mtype mtype_build_te
    mtype_build_tys mtype_build_mtye gamma m ty mty -> mtype gamma m ty mty.

Definition mbody_build_te := FJ_mbody_build_te.

Definition map_mbody ce te mce (mde : md_ext) := FJ_map_mbody E ce te mce (snd mde).

Inductive map_s ce te mce mde : S -> S -> Prop :=
  Base_map_s : forall s s', LJ_map_S _ _ _ _ _ Base_S _ _ _ map_mbody map_s ce te mce mde s s' -> 
    map_s ce te mce mde s s'.

Definition build_mb_ext := LJ_build_mb_ext _ _ FJ_mb_ext _ _ _ map_s (@fst _ _).

Inductive mbody : Context -> m_call_ext -> nat -> Ty -> MB -> Prop :=
  FJ_mbody : forall gamma Vs m ct mb, cFJ.mbody _ _ _ _ _ Ty cFJ E _ _ _ CT _ 
    mbody_build_te _ build_mb_ext map_mbody gamma Vs m ct mb -> mbody gamma Vs m ct mb.

Definition WF_mtype_Us_map := FJ_WF_mtype_Us_map Ty Context.
Definition WF_mtype_U_map := FJ_WF_mtype_U_map Ty Context.
Definition WF_mtype_ext := FJ_WF_mtype_ext Context.
Definition WF_fields_map := FJ_WF_fields_map Ty Context.
Definition WF_mtype_ty_0_map := FJ_WF_mtype_ty_0_map Ty Context .

Variable (lookup : Context -> Var nat -> Ty -> Prop).

Inductive Exp_WF: Context -> E -> Ty -> Prop :=
  FJ_Exp_WF : forall gamma e ty, cFJ.FJ_E_WF _ _ _ _ _ Ty cFJ _ _ Base_E mty_ext _ subtype WF_Type
    fields mtype Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty gamma e ty -> Exp_WF gamma e ty.

Definition ce_build_cte := FJ_ce_build_cte.
Definition Meth_build_context := fun ce (mde : md_ext) => FJ_Meth_build_context Context ce (snd mde).

Inductive S_WF : Context -> S -> Prop :=
  Base_S_WF : forall gamma s, LJ_S_WF _ _ _ _ _ Base_S _ subtype Exp_WF S_WF Empty 
    lookup WF_fields_map fields gamma s -> S_WF gamma s.

Definition Meth_WF_Ext := @LJ_Meth_WF_Ext _ _ _ S_WF _ (FJ_Meth_WF_Ext Context).

Definition override gamma m ty (mde : md_ext) := 
  cFJ.FJ_override _ _ _ _ cFJ mty_ext Context mtype Empty gamma m ty (snd mde).

Variable (Update : Context -> Var nat -> Ty -> Context).

Inductive Meth_WF : nat -> MD -> Prop :=
  FJ_Meth_WF : forall c md, cFJ.Meth_WF _ _ _ _ _ _ cFJ E _ _ CT Context 
    subtype WF_Type Exp_WF Empty Update ce_build_cte Meth_build_context 
    Meth_WF_Ext override c md -> Meth_WF c md.

Definition L_WF_Ext := FJ_L_WF_Ext nat Context. 
Definition L_build_context := FJ_L_build_context Context Empty.

Inductive L_WF : L -> Prop :=
  L_wf : forall cld, cFJ.L_WF _ _ _ _ _ _ cFJ _ _ _ CT _ subtype WF_Type 
    fields Exp_WF Empty Update  ce_build_cte Meth_build_context Meth_WF_Ext override
    L_WF_Ext L_build_context cld -> L_WF cld.

Fixpoint trans (e : E) (Vars : list (Var nat)) (Es : list E) : E :=
  match e with 
    Base_E fj_e => cFJ.FJ_E_trans _ _ _ _ _ _ _ Base_E trans eq_nat_dec fj_e Vars Es
  end.

Definition FJ_Ty := FJ_Ty nat (FJ_ty_ext).
Definition O := nat.
Definition F := nat.
Definition C := nat.
Definition M := nat.
Definition X := nat.

Inductive Exception : Set :=
  Base_Exception : NPE -> Exception.

Inductive Value : Set :=
  Base_Value : LJ_Val O -> Value.

Variables (Config : Set)
  (SLookup : Config -> Var nat -> Value -> Prop)
  (SUpdate : Config -> Var nat -> Value -> Config)
  (HLookup_Type : Config -> O -> FJ_Ty -> Prop)
  (HLookup_Field : Config -> O -> F -> Value -> Prop) 
  (HUpdate : Config -> O -> FJ_Ty -> list (F * Value) -> Config)
  (HUpdate_Field : Config -> O -> F -> Value -> Config)
  (Push_mb_ext : Config -> S -> Config)
  (Set_Exception : Config -> Exception -> Config)
  (Check_NPE_Exception : Config -> bool)
  (Pop_mb_ext : Config -> S -> Config -> Prop).

Definition MB_ext_S (mbe : mb_ext) := Base_S (block _ _ _ _ (fst mbe)).

Fixpoint S_trans (s : S) vars xs := 
  match s with 
    | Base_S s' => LJ_S_trans _ _ _ _ _ _ _ eq_nat_dec Base_S _ Base_E trans S_trans s' vars xs
  end.

Inductive Reduce : Config -> E -> Config -> E -> Prop :=
| Base_Field_Reduce : forall sigma e sigma' e', LJ_Field_Reduce _ _ _ _ _ _ _ _ _ _ _ SLookup SUpdate HLookup_Field 
  Set_Exception Base_Exception Base_E Base_Value sigma e sigma' e' -> Reduce sigma e sigma' e'
| Base_New_Reduce : forall sigma e sigma' e', LJ_New_Reduce _ _ _ _ _ _ _ _ _ Empty fields _ _ _ SLookup SUpdate
  HLookup_Type HLookup_Field HUpdate Base_E Base_Value cFJ sigma e sigma' e' -> 
  Reduce sigma e sigma' e'
| Base_M_Call_Reduce : forall sigma e sigma' e', LJ_M_Call_Reduce _ _ _ _ _ _ _ _ _ _ _ Empty _ _ _ _ SLookup
  SUpdate HLookup_Type Push_mb_ext Set_Exception Base_Exception Base_E Base_Value cFJ MB_ext_S 
  mbody trans S_trans sigma e sigma' e' -> Reduce sigma e sigma' e'
| Base_Congruence_Reduce : forall sigma e sigma' e', FJ_Congruence_Reduce _ _ _ _ _ _ _ _ Base_E Reduce 
  Reduce_List sigma e sigma' e' -> Reduce sigma e sigma' e'
  with Reduce_List : Config -> Es E -> Config -> Es E -> Prop :=
    Base_Reduce_List : forall sigma es sigma' es', 
      State.Reduce_List _ _ _ _ _ _ _ _ Base_E Reduce Reduce_List sigma es sigma' es' ->
      Reduce_List sigma es sigma' es'.

Inductive S_Reduce : Config -> list S -> Config -> list S -> Prop :=
| Base_S_Reduce : forall sigma Ss sigma' Ss', 
    LJ_S_Reduce _ _ _ _ _ _ _ Base_S _ _ _ _ _ SLookup SUpdate HUpdate_Field Set_Exception 
    Base_Exception Base_E Base_Value Check_NPE_Exception sigma Ss sigma' Ss' ->
    S_Reduce sigma Ss sigma' Ss'
| Base_C_S_Reduce : forall sigma Ss sigma' Ss',
  LJ_C_S_Reduce _ _ _ _ Base_S _ Reduce Check_NPE_Exception Pop_mb_ext sigma Ss sigma' Ss' ->
  S_Reduce sigma Ss sigma' Ss'.

Definition WF_Config := LJ_WF_Config _ _ _ _ _ _ subtype Empty lookup fields _ _ _ SLookup HLookup_Type
  HLookup_Field Base_Value cFJ WF_Type.

Section Proofs.

  Variable (WF_CT : forall (c : nat) l,
    CT c = Some l ->
    cFJ.L_WF nat nat nat nat ty_ext Ty cFJ E md_ext cld_ext CT
    Context subtype WF_Type fields Exp_WF Empty Update ce_build_cte
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

  Lemma Base_inject : forall ty ty', cFJ ty = cFJ ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.

  Lemma fields_invert : forall (gamma : Context) (ty : FJ_Ty)
    (fds : list (cFJ.FD nat Ty)),
    fields gamma (cFJ ty) fds ->
    cFJ.FJ_fields nat nat nat nat ty_ext Ty cFJ E md_ext
    cld_ext CT Context fields fields_build_te fields_build_tys gamma
    (cFJ ty) fds.
    intros gamma ty fds fields_fds; inversion fields_fds; subst; assumption.
  Qed.

  Definition fields_build_te_id := FJ_fields_build_te_id.
  Definition fields_build_tys_id := FJ_fields_build_tys_id Ty.

  Lemma cFJ_inject : forall ty ty', cFJ ty = cFJ ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.

  Fixpoint Fields_eq gamma ty fds (fields_fds : fields gamma ty fds) : Fields_eq_def _ _ _ fields_fds :=
    match fields_fds return Fields_eq_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_Fields_eq _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert
      fields_build_te_id fields_build_tys_id _ _ _ FJ_case Fields_eq
    end.

  Definition fds_distinct_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall cl1 cl2 f m n fds',
      map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
      nth_error fds' m = Some (fd nat Ty cl1 f) -> nth_error fds n = Some (fd nat Ty cl2 f) -> m = n.

  Definition Fields_Build_tys_len := FJ_Fields_Build_tys_len Ty.
  Definition WF_fields_map_id' := FJ_WF_fields_map_id' _ _ _ cFJ Context.

  Definition WF_fields_map_sub := FJ_WF_fields_map_sub _ _ _ _ _ _ cFJ _ _ _ CT Context subtype build_te
    cFJ_sub fields Empty Fields_eq.

  Definition WF_fields_map_id_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall tye c tye' fds' fds'', cl' = cFJ (ty_def nat ty_ext tye c) -> fds'' = fds -> 
      fields gamma (cFJ (ty_def nat ty_ext tye' c)) fds' -> 
      map (fun fd' => match fd' with fd _ f => f end) fds' = 
      map (fun fd' => match fd' with fd _ f => f end) fds.
 
  Fixpoint WF_fields_map_id gamma ty fds (fields_fds : fields gamma ty fds) :
    WF_fields_map_id_def _ _ _ fields_fds :=
    match fields_fds return WF_fields_map_id_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fields_map_id _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields Base_inject fields_invert
      Fields_Build_tys_len  _ _ _ FJ_case WF_fields_map_id
    end.

  Fixpoint parent_fields_names_eq gamma ty fds (fields_fds : fields gamma ty fds) :=
    match fields_fds return parent_fields_names_eq_P _ nat _ _ cFJ _ fields _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_parent_fields_names_eq _ _ _ _ _ Ty cFJ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert 
      Fields_Build_tys_len _ _ _ FJ_case parent_fields_names_eq
    end.

  Fixpoint fds_distinct gamma ty fds (fields_fds : fields gamma ty fds) : fds_distinct_def _ _ _ fields_fds :=
    match fields_fds return fds_distinct_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fds_distinct _ _ _ _ _ Ty cFJ _ _ _ CT Context
      subtype WF_Type fields fields_build_te fields_build_tys FJ_fields Exp_WF Empty Update
      ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
      WF_CT parent_fields_names_eq Fields_Build_tys_len _ _ _ FJ_case fds_distinct
    end.

  Definition update_list := cFJ.update_list nat Ty Context Update.

  Definition Weakening_def e ty gamma (WF_e : Exp_WF gamma e ty) :=
    forall gamma' vars, gamma = (update_list Empty vars) -> Exp_WF (update_list gamma' vars) e ty.

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
      | Base_WF_Type gamma' ty' wf_ty' => 
        FJ_Weaken_WF_Type_update_list nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type Base_WF_Type Empty Update Weaken_WF_Object_Ext
        (fun gamma cld te wf_cld gamma' Vars _ => Weaken_WF_Class_Ext gamma Vars cld te wf_cld) gamma' ty' wf_ty'
    end.

  Definition Weaken_Subtype_update_list_def := 
    cFJ.Weaken_Subtype_update_list_P _ _ _ subtype Empty Update.

  Fixpoint Weaken_Subtype_update_list gamma S T (sub_S_T : subtype gamma S T) : 
    Weaken_Subtype_update_list_def _ _ _ sub_S_T :=
    match sub_S_T return Weaken_Subtype_update_list_def _ _ _ sub_S_T with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_Weaken_Subtype_update_list _ _ _ _ _ _ 
        cFJ _ _ _ CT _ subtype build_te cFJ_sub Empty Update _ _ _ sub_S_T' Weaken_Subtype_update_list
    end.
  
  Fixpoint Weakening gamma e ty (WF_e : Exp_WF gamma e ty) : Weakening_def _ _ _ WF_e :=
    match WF_e return Weakening_def _ _ _ WF_e with
      FJ_Exp_WF gamma e ty FJ_case => FJ_Weakening _ _ _ _ _ _ cFJ _ _ Base_E _ _
      subtype WF_Type fields mtype
      Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map
      WF_mtype_ext Empty FJ_Exp_WF Update eq_nat_dec lookup_update_eq
      lookup_update_neq lookup_update_neq' lookup_Empty lookup_id Weaken_WF_fields_map
      Weaken_WF_mtype_ty_0_map Weaken_WF_mtype_Us_map Weaken_WF_mtype_U_map
      Weaken_Subtype_update_list Weaken_WF_mtype_ext Weaken_WF_Type_update_list _ _ _ 
      FJ_case Weakening
    end.

  Lemma E_trans_Wrap : forall e vars es', 
    trans (Base_E e) vars es' = cFJ.FJ_E_trans _ _ _ _ _ _ _ Base_E trans eq_nat_dec e vars es'.
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
      | Base_WF_Type gamma' ty' wf_ty' => FJ_WF_Type_update_list_id _ _ _ _ _ _ cFJ
        _ _ _ CT _ wf_class_ext wf_object_ext  WF_Type Base_WF_Type Update WF_Object_ext_Update_Vars_id 
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
        fields_build_tys FJ_fields Base_inject fields_invert  
        fields_build_te_id fields_build_tys_id  gamma' ty' fds' FJ_ty'_fields fields_id
    end.

   Definition WF_mtype_ty_0_map_id := FJ_WF_mtype_ty_0_map_id Ty Context.
   
   Definition WF_mtype_ty_0_map_tot := FJ_WF_mtype_ty_0_map_tot Ty Context subtype.

   Definition WF_mtype_ty_0_map_cl_id := 
     FJ_WF_mtype_ty_0_map_cl_id _ _ _ cFJ Context Base_inject.

   Definition WF_mtype_ty_0_map_cl_id' := 
     FJ_WF_mtype_ty_0_map_cl_id' _ _ _ cFJ Context. 

   Definition m_eq_dec := eq_nat_dec.
   
   Definition build_te_build_ty_0_id := FJ_build_te_build_ty_0_id nat _ _ cFJ Context (@id _).

   Definition WF_mtype_Us_map_len := FJ_WF_mtype_Us_map_len Ty Context.

   Definition mtype_build_tys_len ce te ty vds (mde : md_ext) := 
     FJ_mtype_build_tys_len nat Ty ce te ty vds (snd mde).

   Definition methods_build_te_id := FJ_methods_build_te_id.

   Definition WF_Obj_ext_Lem := FJ_WF_Obj_ext_Lem Context.
   
   Definition WF_cld_ext_Lem := FJ_WF_Cld_ext_Lem Context.

   Definition WF_Type_par_Lem_def := WF_Type_par_Lem_P
     _ _ _ _ ty_ext Ty cFJ _ _ _ CT Context 
       wf_object_ext WF_Type mtype_build_te
       L_build_context.

   Fixpoint WF_Type_par_Lem gamma ty (WF_ty : WF_Type gamma ty) :=
     match WF_ty return WF_Type_par_Lem_def _ _ WF_ty with 
       Base_WF_Type gamma ty WF_base => 
       FJ_WF_Type_par_Lem _ _ _ _ _ _ cFJ _ _ _ CT Context wf_class_ext
       wf_object_ext WF_Type Base_WF_Type mtype_build_te
       L_build_context Base_inject 
       (fun gamma a b c te d e f g h i j k l m => WF_Obj_ext_Lem gamma te)
       gamma ty WF_base
     end.

   Definition WF_Type_par_Lem_def' := 
     WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty cFJ E _ _ CT Context wf_class_ext
     WF_Type mtype_build_te L_build_context.

   Definition WF_Type_par_Lem' delta ty (WF_ty : WF_Type delta ty) :
     WF_Type_par_Lem_def' delta ty WF_ty := 
     match WF_ty in (WF_Type delta ty) return WF_Type_par_Lem_def' delta ty WF_ty with 
       | Base_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par_Lem' _ _ _ _ _ _ cFJ
         _ _ _ CT Context wf_class_ext wf_object_ext WF_Type Base_WF_Type
         mtype_build_te L_build_context Base_inject 
         (fun gamma ce te0 _ te'' c0 fds k' mds c1 gamma0 ce' te' cld' _ _ _ _ _ _ => 
           WF_cld_ext_Lem gamma0 ce' te'')
         gamma ty WF_base
     end.     

   Definition WF_Type_par delta ty (WF_ty : WF_Type delta ty) := 
     match WF_ty in (WF_Type delta ty) return 
       WF_Type_par_P _ _ _ _ ty_ext Ty cFJ E _ _ CT _ WF_Type mtype_build_te
       L_build_context delta ty WF_ty with 
       | Base_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par _ _ _ _ _ _ cFJ _ _ _ CT Context 
         wf_class_ext wf_object_ext WF_Type Base_WF_Type mtype_build_te
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
   
   Lemma mtye_eq : forall (mtye mtye' : mty_ext), mtye = mtye'.
     intros; destruct mtye; destruct mtye'; reflexivity.
   Qed.
   
    Lemma te_eq : forall (te te' : ty_ext), te = te'.
      intros; destruct te; destruct te'; reflexivity.
    Qed.

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
    Definition mtype_build_tys_refl ce te ty U (mde : md_ext) := 
      FJ_mtype_build_tys_refl nat Ty ce te ty U (snd mde).

    Definition build_V' := FJ_build_V' _ _ _ _ _ _ cFJ _ _ _ _ _ CT _ subtype build_te
      cFJ_sub wf_class_ext wf_object_ext WF_Type mtype mtype_build_tys mtype_build_mtye
      WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty Update
      Meth_build_context Meth_WF_Ext L_build_context WF_mtype_ty_0_map_id
      WF_mtype_ty_0_map_cl_refl build_te_refl WF_mtype_U_map_trans WF_mtype_Us_map_trans
      WF_mtype_ext_trans mtype_build_tys_refl (@snd _ _).

    Definition mtype_build_tys_tot ce te te' te'' ty vds (mde : md_ext) := 
      FJ_mtype_build_tys_tot nat Ty ce te te' te'' ty vds (snd mde).


    Definition mtype_build_mtye_tot ce te te' te'' ty vds (mde : md_ext) := 
      FJ_mtype_build_mtye_tot nat Ty ce te te' te'' ty vds (snd mde).

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
        mtype_build_mtye FJ_mtype Exp_WF WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty
        Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
        WF_CT cFJ_inject WF_mtype_ty_0_map_total mtype_build_tys_len
        WF_Type_invert WF_mtype_ty_0_map_id eq_nat_dec
        build_te_build_ty_0_id WF_mtype_ty_0_map_cl_refl mtype_build_tys_tot 
        mtype_build_mtye_tot build_V' gamma S' T' sub_S_T' Lem_2_9
    end.

    Fixpoint Term_subst_pres_typ gamma e T (WF_e : Exp_WF gamma e T) :=
      match WF_e in Exp_WF gamma e T return
        cFJ.Term_subst_pres_typ_P _ _ _ _ subtype Exp_WF Update trans gamma e T WF_e with 
        FJ_Exp_WF gamma e ty FJ_case => FJ_Term_subst_pres_typ _ _ _ _ _ _ 
        cFJ _ _ Base_E mty_ext _ _ CT _ subtype build_te
        cFJ_sub WF_Type fields mtype 
        Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Empty FJ_Exp_WF Update
        trans eq_nat_dec lookup_update_eq lookup_update_neq'
        lookup_id E_trans_Wrap Lem_2_8 Lem_2_9 WF_fields_map_update_list
        WF_mtype_ty_0_map_Weaken_update_list WF_mtype_U_map_Weaken_update_list
        WF_mtype_Us_map_Weaken_update_list WF_mtype_ext_update_list_id
        WF_mtype_ty_0_map_total Subtype_Update_list_id WF_Type_update_list_id gamma e ty FJ_case Term_subst_pres_typ
      end.
      
    Lemma Weakening' :  forall (e : E) (ty : Ty) (vars : list (Var nat * Ty)) (gamma : Context),
      Exp_WF (cFJ.update_list nat Ty Context Update Empty vars) e ty ->
      Exp_WF (cFJ.update_list nat Ty Context Update gamma vars) e ty.
      intros; eapply Weakening; eauto.
    Qed.
      
    Lemma Subtype_Update_list_id' : forall (gamma : Context) 
      (vars : list (Var nat * Ty)) (S T : Ty),
      subtype (cFJ.update_list nat Ty Context Update gamma vars) S T ->
      subtype gamma S T.
      intros; eapply Subtype_Update_list_id; eauto.
    Qed.
      
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

    Definition Build_S0'' := fun ce me gamma te te' c vds S0 T0 delta e e' D D' mtye mce
    Ds Ds' te'' Vars => FJ_Build_S0'' _ _ _ _ cFJ _ _ subtype WF_Type
      Exp_WF Empty Update Subtype_Weaken Weakening Subtype_Update_list_id 
      ce me gamma te te' c vds S0 T0 delta e e' D D' mtye mce Ds Ds' te'' Vars.

    Lemma Build_S0''' : forall ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce
  Ds Ds' Vars (ce_WF : L_WF_Ext gamma' ce c)
  (build_gamma' : L_build_context ce gamma')
  (wf_me : Meth_WF_Ext gamma ce me)
  (build_te' : ce_build_cte ce te'),
  Meth_build_context ce me (update_list Empty ((this _, cFJ (ty_def _ _ te' (cl _ c))) :: 
    (map (fun Tx => match Tx with | vd ty x => (var _ x, ty) end) vds))) gamma -> 
  Exp_WF gamma e S0 -> subtype gamma S0 T0 -> wf_class_ext delta ce te -> 
  mtype_build_mtye ce te T0 vds me mtye -> 
  map_mbody ce te mce me e e' ->
  mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) -> WF_mtype_U_map delta mce mtye D D' ->
  WF_mtype_ext delta mce mtye ->
  WF_mtype_Us_map delta mce mtye Ds Ds' -> 
  List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
  zip (this _ :: (map (fun Tx => match Tx with | vd _ x => var _ x end) vds) ) 
  (cFJ (ty_def _ _ te (cl _ c)) :: Ds') (@pair _ _) = Some Vars ->
  mtype_build_tys ce te T0 vds me (map (fun vd' : VD _ _ => match vd' with
                                                          | vd ty _ => ty
                                                        end) vds) Ds -> 
  exists S0'', 
    subtype delta S0'' D' /\ 
      (**** WF_Type delta S0'' /\ ****) Exp_WF (update_list delta Vars) e' S0''.
      intros; eapply Build_S0''; eauto.
      intros; destruct te0; destruct te'0; reflexivity.
      inversion H4; subst; constructor.
      inversion H5; subst; constructor.
      inversion H11; subst; constructor.
      Existential 1 := (@id _).
    Qed.

    Lemma WF_Type_update_list_id' : 
      forall (delta : Context) (Vars : list (Var nat * Ty)) (ty : Ty),
        WF_Type (cFJ.update_list nat Ty Context Update delta Vars) ty ->
        WF_Type delta ty.
      intros; inversion H; subst; eapply WF_Type_update_list_id; eauto.
    Qed.

    
    Inductive WF_mb_ext : Context -> mb_ext -> Prop :=
    | Base_WF_mb_ext : forall gamma mbe, LJ_WF_mb_ext _ _ _ S_WF gamma mbe -> WF_mb_ext gamma mbe.

    Variable (Weaken_S_WF : forall s Vars delta, S_WF (update_list Empty Vars) s -> 
      S_WF (update_list delta Vars) s).
      
    Variable (WF_Build_mb_ext : forall (ce : cld_ext) (me : md_ext) (gamma : Context) 
    (te te' : ty_ext) (c : nat) (vds : list (cFJ.VD nat Ty)) 
    (T0 : Ty) (delta : Context) (D D' : Ty) (mtye : mty_ext)
    (mce : FJ_m_call_ext) (mbe : mb_ext) (Ds Ds' : list Ty) 
    (te'' : ty_ext) (Vars : list (cFJ.Var nat * Ty)),
  Meth_WF_Ext gamma ce me ->
  Meth_build_context ce me
    (cFJ.update_list nat Ty Context Update Empty
       ((cFJ.this nat, cFJ (ty_def nat ty_ext te' (cl nat c)))
        :: map
             (fun Tx : cFJ.VD nat Ty =>
              match Tx with
              | vd ty x => (cFJ.var nat x, ty)
              end) vds)) gamma ->
  WF_Type delta (cFJ (ty_def nat ty_ext te (cl nat c))) ->
  build_mb_ext ce te mce me mbe ->
  mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) ->
  WF_mtype_U_map delta mce mtye D D' ->
  WF_mtype_ext delta mce mtye ->
  WF_mtype_Us_map delta mce mtye Ds Ds' ->
  List_P1
    (fun Tx : cFJ.VD nat Ty =>
     match Tx with
     | vd ty _ => WF_Type gamma ty
     end) vds ->
  zip
    (cFJ.this nat
     :: map
          (fun Tx : cFJ.VD nat Ty =>
           match Tx with
           | vd _ x => cFJ.var nat x
           end) vds) (cFJ (ty_def nat ty_ext te'' (cl nat c)) :: Ds') (@pair _ _) =
  Some Vars ->
  mtype_build_tys ce te'' T0 vds me
    (map (fun vd' : cFJ.VD nat Ty => match vd' with
                                     | vd ty _ => ty
                                     end) vds) Ds ->
  WF_mb_ext (cFJ.update_list nat Ty Context Update delta Vars) mbe).

    Definition Lem_2_12 := FJ_Lem_2_12 _ _ _ _ _ _ _ _ _ _ _ _ CT 
      Context subtype build_te cFJ_sub _ _ WF_Type Base_WF_Type fields mtype mtype_build_te
      mtype_build_tys mtype_build_mtye mbody_build_te
      mb_ext build_mb_ext map_mbody Exp_WF WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext
      Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context WF_CT cFJ_inject 
      Build_S0''' WF_mb_ext WF_Build_mb_ext WF_mtype_Us_map_len mtype_build_tys_len methods_build_te_id WF_Type_par
      build_te_id mtype_invert WF_mtype_ty_0_map_cl_id'' WF_mtype_ty_0_map_tot' WF_Type_invert.

    Lemma EWrap_inject : forall e e', Base_E e = Base_E e' -> e = e'.
      intros; injection H; intros; assumption.
    Qed.
    
    Lemma FJ_E_WF_invert : forall gamma (e : FJ_E _ _ _ _ _ _ _ ) c0, 
      Exp_WF gamma (Base_E e) c0 -> cFJ.FJ_E_WF _ _ _ _ _ Ty cFJ _ _ Base_E mty_ext
      Context subtype WF_Type fields mtype
      Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
      WF_mtype_ext Empty gamma (Base_E e) c0.
      intros; inversion H; subst; assumption.
    Qed.

    Variable (Conservative_Extension : Context -> Context -> Prop)
      (Conservative_Extension_id : forall gamma : Context,
        Conservative_Extension gamma gamma).

    Print E_Progress_P.

    Definition E_C_Reduce := Reduce.
    Definition FJ_E_Wrap := Base_E.
    Definition NPE_Wrap := Base_Exception.
    Definition E_WF := Exp_WF.
    Definition update := Update.
    Definition LJ_Val_Wrap := Base_Value.
    Definition FJ_Ty_Wrap := cFJ.
    Definition E_WF_Wrap := FJ_Exp_WF.
    Definition E_C_Reduce_List := Reduce_List.
    
    Inductive E_Val : E -> Prop := 
      LJ_E_Val_Wrap : forall e, LJ_E_Val C F M X ty_ext E m_call_ext FJ_E_Wrap e -> E_Val e.

    Definition E_Progress_P := E_Progress_P Ty E Context E_WF Config E_Val E_C_Reduce WF_Config.
    Definition E_Progress_Q := E_Progress_Q Ty E Context E_WF Config E_Val E_C_Reduce_List WF_Config.

    Definition FJ_progress_1_H1 := FJ_progress_1_H1 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields Config FJ_E_Wrap E_Val FJ_Ty_Wrap E_C_Reduce 
      WF_Config mtype WF_Type FJ_Exp_WF LJ_E_Val_Wrap.

    Lemma E_Val_invert : forall e : E, E_Val e -> LJ_E_Val C F M X ty_ext E m_call_ext FJ_E_Wrap e.
      intros; inversion H; subst; assumption.
    Qed.
      
    Lemma LJ_imp_WF_Config : forall (gamma : Context) (sigma : Config), 
      WF_Config gamma sigma -> LJ_WF_Config C F X ty_ext Ty
      Context subtype Empty lookup fields O Config Value SLookup
      HLookup_Type HLookup_Field LJ_Val_Wrap FJ_Ty_Wrap WF_Type gamma sigma.
      intros; auto.
    Qed.
    Print FJ_progress_1_H2.
    
    Definition SFresh := SFresh X Config Value SLookup.
    Definition HFresh := HFresh C F ty_ext O Config Value HLookup_Type HLookup_Field.
    Definition FJ_C_Reduce_Wrap := Base_Congruence_Reduce.
    Definition LJ_Field_Reduce_Wrap := Base_Field_Reduce.

    Variable (ex_SFresh : forall sigma, exists x, SFresh sigma x).
    Variable (ex_HFresh : forall sigma, exists o, HFresh sigma o).

    Definition FJ_progress_2_H2 := FJ_progress_1_H2 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields O Config Exception Value SLookup SUpdate 
      HLookup_Type HLookup_Field Set_Exception NPE_Wrap FJ_E_Wrap E_Val LJ_Val_Wrap 
      FJ_Ty_Wrap E_C_Reduce E_C_Reduce_List LJ_Field_Reduce_Wrap FJ_C_Reduce_Wrap
      WF_Config mtype WF_Type FJ_Exp_WF ex_SFresh LJ_imp_WF_Config E_Val_invert FJ_E_WF_invert 
      EWrap_inject Lem_2_8 WF_fields_map_id WF_fields_map_id'.

    Variables (SLookup_update_eq : forall (sigma : Config) (X0 : Var X) (ty : Value),
      SLookup (SUpdate sigma X0 ty) X0 ty)
    (SLookup_update_neq : forall (sigma : Config) (Y X0 : Var X) (ty ty' : Value), 
      SLookup sigma X0 ty ->  X0 <> Y -> SLookup (SUpdate sigma Y ty') X0 ty).
    
    Definition WF_mtype_ty_0_map_Empty_refl := FJ_WF_mtype_ty_0_map_Empty_refl _ _ _ cFJ Context.

    Definition mtype_mbody_build_te := FJ_mtype_mbody_build_te.

    Variable (build_mb_ext_tot : forall ce te mce me ty vds tys tys',
      mtype_build_tys ce te ty vds me tys tys' -> exists mb, build_mb_ext ce te mce me mb).

    Definition map_mbody_tot ce te mce (mde : md_ext) := 
      FJ_map_mbody_tot nat Ty E ce te mce (snd mde).

    Fixpoint mtype_implies_mbody gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
      match mtype_m with 
        FJ_mtype gamma' m' ty' mty' fj_mtype_m => FJ_mtype_implies_mbody _ _ _ _ _ _ cFJ
        _ _ _ _ _ CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye
        FJ_mtype mbody_build_te mb_ext build_mb_ext map_mbody 
        Empty cFJ_inject mtype_build_tys_len map_mbody_tot
        mtype_mbody_build_te build_mb_ext_tot gamma' m' ty' mty' fj_mtype_m mtype_implies_mbody
      end.

    Definition LJ_M_Call_Reduce_Wrap := Base_M_Call_Reduce.
    Definition X_eq_dec := eq_nat_dec.

    Definition FJ_progress_1_H3 := FJ_progress_1_H3 C F M X ty_ext Ty
      E S X_eq_dec Context mty_ext m_call_ext mb_ext subtype E_WF
      Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
      WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext O map_mbody Config Exception Value
      SLookup SUpdate HLookup_Type HLookup_Field Push_mb_ext
      Set_Exception NPE_Wrap FJ_E_Wrap E_Val LJ_Val_Wrap FJ_Ty_Wrap
      MB_ext_S mbody trans S_trans E_C_Reduce E_C_Reduce_List
      LJ_M_Call_Reduce_Wrap FJ_C_Reduce_Wrap WF_Config mtype WF_Type
      FJ_Exp_WF ex_SFresh LJ_imp_WF_Config E_Val_invert FJ_E_WF_invert
      EWrap_inject CT build_mb_ext mbody_build_te mtype_implies_mbody Lem_2_9
      WF_mtype_ty_0_map_Empty_refl WF_mtype_ty_0_map_total
      SLookup_update_eq SLookup_update_neq WF_mtype_Us_map_len FJ_mbody.

    Definition LJ_New_Reduce_Wrap := Base_New_Reduce.

    Definition FJ_progress_1_H4 := FJ_progress_1_H4 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields O Config Value SLookup SUpdate HLookup_Type 
      HLookup_Field HUpdate FJ_E_Wrap E_Val LJ_Val_Wrap FJ_Ty_Wrap E_C_Reduce 
      E_C_Reduce_List LJ_New_Reduce_Wrap FJ_C_Reduce_Wrap 
      WF_Config mtype WF_Type FJ_Exp_WF ex_SFresh ex_HFresh LJ_imp_WF_Config 
      E_Val_invert FJ_E_WF_invert EWrap_inject.

    Definition Reduce_List_Wrap := Base_Reduce_List.

    Definition FJ_progress_1_H5 := FJ_progress_1_H5 Ty E Context Exp_WF Config E_Val E_C_Reduce_List
      WF_Config.

    Definition FJ_progress_1_H6 := FJ_progress_1_H6 C F M X ty_ext Ty E Context m_call_ext 
      E_WF Config FJ_E_Wrap E_Val E_C_Reduce E_C_Reduce_List Reduce_List_Wrap 
      WF_Config E_Val_invert.

    Definition FJ_FJ_E_WF_rect' := FJ_FJ_E_WF_rect' C F M X ty_ext Ty  FJ_Ty_Wrap E m_call_ext Base_E mty_ext Context 
      subtype WF_Type fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty E_WF_Wrap.
      
    Definition FJ_progress_1 := FJ_FJ_E_WF_rect' _ _ FJ_progress_1_H1
    FJ_progress_2_H2 FJ_progress_1_H3 FJ_progress_1_H4 FJ_progress_1_H5 FJ_progress_1_H6.

  Fixpoint E_Progress gamma e ty (WF_e : Exp_WF gamma e ty) : E_Progress_P _ _ _ WF_e :=
    match WF_e return E_Progress_P _ _ _ WF_e with
      FJ_Exp_WF gamma e ty FJ_case => FJ_progress_1 _ _ _ FJ_case E_Progress
    end.

  Definition S_Progress_P := S_progress_P S Context S_WF Config WF_Config S_Reduce.
  
  Variable Pop_mb_ext_tot : forall sigma, exists s, exists sigma', Pop_mb_ext sigma s sigma'.

  Definition LJ_S_Reduce_Wrap := Base_S_Reduce.
  Definition LJ_C_S_Reduce_Wrap := Base_C_S_Reduce.
  Definition LJ_S_Wrap := Base_S.

  Definition LJ_progress_H1 := LJ_progress_H1 C F M X ty_ext Ty E S LJ_S_Wrap 
    Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
    WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields Base_S_WF O Config Exception Value 
    SLookup SUpdate HLookup_Type HLookup_Field HUpdate_Field Set_Exception 
    NPE_Wrap FJ_E_Wrap E_Val LJ_Val_Wrap FJ_Ty_Wrap E_C_Reduce Check_NPE_Exception 
    Pop_mb_ext WF_Config S_Reduce LJ_S_Reduce_Wrap LJ_C_S_Reduce_Wrap 
    mtype WF_Type LJ_imp_WF_Config E_Val_invert FJ_E_WF_invert EWrap_inject E_Progress Pop_mb_ext_tot.

  Definition LJ_progress_H2 := LJ_progress_H2 C F M X ty_ext Ty E S LJ_S_Wrap 
    Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
    WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields Base_S_WF O Config Exception Value 
    SLookup SUpdate HLookup_Type HLookup_Field HUpdate_Field Set_Exception 
    NPE_Wrap FJ_E_Wrap E_Val LJ_Val_Wrap FJ_Ty_Wrap E_C_Reduce Check_NPE_Exception 
    Pop_mb_ext WF_Config S_Reduce LJ_S_Reduce_Wrap LJ_C_S_Reduce_Wrap 
    mtype WF_Type LJ_imp_WF_Config E_Val_invert 
    FJ_E_WF_invert EWrap_inject E_Progress Pop_mb_ext_tot.

  Definition LJ_progress_H3 := LJ_progress_H3 C F M X ty_ext Ty E S LJ_S_Wrap 
    Context m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map fields 
    Base_S_WF O Config Exception Value SLookup SUpdate HUpdate_Field Set_Exception 
    NPE_Wrap FJ_E_Wrap LJ_Val_Wrap Check_NPE_Exception WF_Config S_Reduce LJ_S_Reduce_Wrap.

  Definition LJ_progress_H4 := LJ_progress_H4 S Context S_WF Config WF_Config S_Reduce.

  Definition LJ_progress_H5 := LJ_progress_H5 S Context S_WF Config WF_Config S_Reduce.

  Definition LJ_S_WF_Wrap := Base_S_WF.

  Definition LJ_S_WF_rect := LJ_S_WF_rect F X Ty E S LJ_S_Wrap Context subtype 
    E_WF S_WF Empty lookup WF_fields_map fields LJ_S_WF_Wrap.

  Definition S_Progress_1 := LJ_S_WF_rect _ _ LJ_progress_H1 LJ_progress_H2 LJ_progress_H3
    LJ_progress_H4 LJ_progress_H5.

    Fixpoint S_Progress gamma s (WF_s : S_WF gamma s) : S_Progress_P _ _ WF_s :=
      match WF_s return S_Progress_P _ _ WF_s with
        Base_S_WF gamma s S_case => S_Progress_1 _ _ S_case S_Progress
      end.

    Definition E_preservation_P := E_preservation_P Ty E Context subtype Exp_WF Config Reduce
      WF_Config Conservative_Extension.
    
    Definition E_preservation_Q := E_preservation_Q Ty E Context subtype Exp_WF Config Reduce_List
      WF_Config Conservative_Extension.

    Variable (WF_Config_Set_NPE : forall gamma sigma, 
    WF_Config gamma sigma -> WF_Config gamma (Set_Exception sigma (Base_Exception npe))).

    Definition LJ_Field_Reduce_H1 := State.LJ_Field_Reduce_H1 _ _ _ _ _ _ _ _ _ subtype Exp_WF
      _ _ nat _ _ _ SLookup SUpdate HLookup_Field Set_Exception Base_Exception Base_E Base_Value 
      cFJ Reduce Base_Field_Reduce WF_Config CT Conservative_Extension WF_Config_Set_NPE
      build_te cFJ_sub Conservative_Extension_id.

    Definition WF_Config_SUpdate_Fresh_P := 
      WF_Config_SUpdate_Fresh_P C F X ty_ext Ty Context subtype O Config 
      Value SLookup SUpdate HLookup_Type HLookup_Field LJ_Val_Wrap FJ_Ty_Wrap WF_Config WF_Type update.

    Lemma LJ_Val_Wrap_inject : forall v v' : LJ_Val O, LJ_Val_Wrap v = LJ_Val_Wrap v' -> v = v'.
      intros; injection H; auto.
    Qed.
 
    Print LJ_WF_Config_SUpdate_Fresh.

    Variable (SLookup_HUpdate : forall sigma x v o ty fds_vals, 
      SLookup sigma x v -> SLookup (HUpdate sigma o ty fds_vals) x v)
    (SLookup_HUpdate' : forall sigma x v o ty fds_vals, 
      SLookup (HUpdate sigma o ty fds_vals) x v -> SLookup sigma x v)
    (HTLookup_HUpdate_eq : forall sigma o ty fds_vals, 
      HLookup_Type (HUpdate sigma o ty fds_vals) o ty)
    (HTLookup_HUpdate_neq : forall sigma o o' ty ty' fds_vals, 
      HLookup_Type sigma o' ty' -> o <> o' -> 
      HLookup_Type (HUpdate sigma o ty fds_vals) o' ty')
    (HTLookup_HUpdate_neq' : forall sigma o o' ty ty' fds_vals, 
      HLookup_Type (HUpdate sigma o ty fds_vals) o' ty' -> o <> o' -> 
      HLookup_Type sigma o' ty')
    (HFLookup_HUpdate_eq : forall sigma o ty fds_vals n f val,
      nth_error fds_vals n = Some (f, val) -> 
      HLookup_Field (HUpdate sigma o ty fds_vals) o f val)
    (HFLookup_HUpdate_eq' : forall sigma o ty fds_vals f val,      
      HLookup_Field (HUpdate sigma o ty fds_vals) o f val ->
      exists n, nth_error fds_vals n = Some (f, val))
    (HFLookup_HUpdate_neq : forall sigma o o' ty fds_vals f val, 
      HLookup_Field sigma o' f val -> o <> o' -> 
      HLookup_Field (HUpdate sigma o ty fds_vals) o' f val)
    (HFLookup_HUpdate_neq' : forall sigma o o' ty fds_vals f val, 
      HLookup_Field (HUpdate sigma o ty fds_vals) o' f val -> o <> o' -> 
      HLookup_Field sigma o' f val)
    (HTLookup_id : forall sigma o ty ty', 
      HLookup_Type sigma o ty -> HLookup_Type sigma o ty' -> ty = ty')
    (WF_Type_update_id : forall gamma ty, WF_Type gamma ty -> 
      forall x ty', WF_Type (update gamma x ty') ty)
    (HLookup_Field_id : forall sigma oid f c c', 
      HLookup_Field sigma oid f c -> HLookup_Field sigma oid f c' -> c = c')
    (HTLookup_SUpdate : forall sigma x v o ty, 
      HLookup_Type sigma o ty -> HLookup_Type (SUpdate sigma x v) o ty)
    (HTLookup_SUpdate' : forall sigma x v o ty, 
      HLookup_Type (SUpdate sigma x v) o ty -> HLookup_Type sigma o ty)
    (HFLookup_SUpdate : forall sigma x v o f v', 
      HLookup_Field sigma o f v' -> HLookup_Field (SUpdate sigma x v) o f v')
    (HFLookup_SUpdate' : forall sigma x v o f v', 
      HLookup_Field (SUpdate sigma x v) o f v' -> HLookup_Field sigma o f v').

    Variable (Subtype_Update_list_id' : forall (gamma : Context) (S T : Ty),
                             subtype gamma S T ->
                             forall (x : Var X) (ty : Ty),
                             subtype (update gamma x ty) S T).

    Definition WF_Config_SUpdate_Fresh : forall sigma gamma, WF_Config_SUpdate_Fresh_P sigma gamma := 
      LJ_WF_Config_SUpdate_Fresh C F X ty_ext Ty X_eq_dec Context 
      subtype Empty lookup fields O Config Value SLookup SUpdate HLookup_Type 
      HLookup_Field LJ_Val_Wrap FJ_Ty_Wrap WF_Type SLookup_update_eq 
      SLookup_update_neq update HLookup_Field_id HTLookup_SUpdate HTLookup_SUpdate'
      HFLookup_SUpdate HFLookup_SUpdate' Subtype_Update_list_id'
      WF_Type_update_id lookup_update_eq lookup_update_neq' lookup_id.

    Variables (SLookup_id : forall sigma X ty ty', SLookup sigma X ty -> SLookup sigma X ty' -> ty = ty')
    (Conservative_Extension_update : forall gamma x ty, (forall ty, ~ lookup gamma x ty) -> 
    Conservative_Extension gamma (update gamma x ty)).

    Definition LJ_Field_Reduce_H2 := 
      LJ_Field_Reduce_H2  C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields O Config Exception Value SLookup SUpdate 
      HLookup_Type HLookup_Field Set_Exception NPE_Wrap FJ_E_Wrap LJ_Val_Wrap 
      FJ_Ty_Wrap E_C_Reduce Base_Field_Reduce WF_Config mtype WF_Type E_WF_Wrap 
      LJ_imp_WF_Config FJ_E_WF_invert EWrap_inject 
      Lem_2_8 WF_fields_map_id WF_fields_map_id' SLookup_id 
      Conservative_Extension update Conservative_Extension_update 
      Subtype_Update_list_id' lookup_update_eq LJ_Val_Wrap_inject WF_fields_map_sub 
      Subtype_Weaken WF_Config_SUpdate_Fresh.

    Definition O_eq_dec := eq_nat_dec.
    
    Lemma LJ_Val_invert : forall (v : Value), 
    {v = LJ_Val_Wrap (Null _)} + {exists oid, v = LJ_Val_Wrap (Oid _ oid)}.
      intros; destruct v; destruct l; first [left; reflexivity | right; eexists _; reflexivity].
    Qed.
      
    Definition FJ_subtype_Wrap := cFJ_sub.

    Definition LJ_WF_Config_SUpdate_Fresh' := LJ_WF_Config_SUpdate_Fresh' C F M X ty_ext Ty E X_eq_dec Context 
      subtype Empty lookup fields cld_ext md_ext O Config Value
      SLookup SUpdate HLookup_Type HLookup_Field HUpdate LJ_Val_Wrap
      FJ_Ty_Wrap WF_Type CT SLookup_update_eq SLookup_update_neq
      build_te update FJ_subtype_Wrap LJ_Val_invert HTLookup_SUpdate
      HTLookup_SUpdate' HFLookup_SUpdate HFLookup_SUpdate'
      Subtype_Update_list_id' WF_Type_update_id lookup_update_eq
      lookup_update_neq' lookup_id SLookup_HUpdate HTLookup_HUpdate_eq
      HTLookup_HUpdate_neq HTLookup_HUpdate_neq' HFLookup_HUpdate_eq
      HFLookup_HUpdate_neq HFLookup_HUpdate_neq' HTLookup_id O_eq_dec.
      
    Definition LJ_R_New_preservation := LJ_R_New_preservation C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext O Config Value SLookup 
      SUpdate HLookup_Type HLookup_Field HUpdate FJ_E_Wrap LJ_Val_Wrap FJ_Ty_Wrap 
      E_C_Reduce Base_New_Reduce WF_Config mtype WF_Type E_WF_Wrap 
      LJ_imp_WF_Config FJ_E_WF_invert EWrap_inject 
      CT SLookup_id Conservative_Extension build_te update FJ_subtype_Wrap 
      Conservative_Extension_update lookup_update_eq 
      LJ_Val_Wrap_inject LJ_WF_Config_SUpdate_Fresh' Fields_eq.
    
  Variable (Conservative_WF_fields_map : forall gamma ty ty', WF_fields_map gamma ty ty' -> 
    forall gamma', Conservative_Extension gamma gamma' -> WF_fields_map gamma' ty ty').

    Definition E_C_preservation_H1 := E_C_preservation_H1 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext Config FJ_E_Wrap FJ_Ty_Wrap 
      E_C_Reduce E_C_Reduce_List Base_Congruence_Reduce WF_Config mtype WF_Type 
      E_WF_Wrap FJ_E_WF_invert EWrap_inject Lem_2_8 CT Conservative_Extension 
      build_te FJ_subtype_Wrap Conservative_WF_fields_map.

    Variable (Conservative_WF_mtype_ty_0_map : forall gamma ty ty', WF_mtype_ty_0_map gamma ty ty' -> 
      forall gamma', Conservative_Extension gamma gamma' -> WF_mtype_ty_0_map gamma' ty ty')
    (Conservative_WF_mtype_Us_map : forall gamma mce mtye Us Us', WF_mtype_Us_map gamma mce mtye Us Us' -> 
      forall gamma', Conservative_Extension gamma gamma' -> WF_mtype_Us_map gamma' mce mtye Us Us')
    (Conservative_WF_mtype_U_map : forall gamma mce mtye U U', WF_mtype_U_map gamma mce mtye U U' -> 
      forall gamma', Conservative_Extension gamma gamma' -> WF_mtype_U_map gamma' mce mtye U U')
    (Conservative_WF_mtype_ext : forall gamma mce mtye, WF_mtype_ext gamma mce mtye -> 
      forall gamma', Conservative_Extension gamma gamma' -> WF_mtype_ext gamma' mce mtye)
    (Conservative_subtype : forall gamma S T, subtype gamma S T -> 
      forall gamma', Conservative_Extension gamma gamma' -> subtype gamma' S T)
    (Conservative_E_WF : forall gamma e T, E_WF gamma e T -> 
      forall gamma', Conservative_Extension gamma gamma' -> E_WF gamma' e T)
    (Conservative_WF_Type : forall gamma T, WF_Type gamma T -> 
      forall gamma', Conservative_Extension gamma gamma' -> WF_Type gamma' T).

    Definition E_C_preservation_H2 := E_C_preservation_H2 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields Config FJ_E_Wrap FJ_Ty_Wrap E_C_Reduce 
      E_C_Reduce_List Base_Congruence_Reduce WF_Config mtype WF_Type E_WF_Wrap 
      FJ_E_WF_invert EWrap_inject Lem_2_9 WF_mtype_ty_0_map_total 
      Conservative_Extension Conservative_WF_mtype_ty_0_map 
      Conservative_WF_mtype_Us_map Conservative_WF_mtype_U_map 
      Conservative_WF_mtype_ext Conservative_subtype Conservative_E_WF.

    Definition E_C_preservation_H3 := E_C_preservation_H3 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext Config FJ_E_Wrap FJ_Ty_Wrap 
      E_C_Reduce E_C_Reduce_List Base_Congruence_Reduce WF_Config mtype WF_Type 
      E_WF_Wrap FJ_E_WF_invert EWrap_inject CT Conservative_Extension 
      build_te FJ_subtype_Wrap Conservative_WF_mtype_ty_0_map
      Conservative_WF_mtype_Us_map Conservative_WF_mtype_U_map 
      Conservative_WF_mtype_ext Conservative_subtype Conservative_E_WF.

    Definition E_C_preservation_H4 := E_C_preservation_H4 C F M X ty_ext Ty E Context mty_ext m_call_ext 
      subtype E_WF Empty lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext Config FJ_E_Wrap FJ_Ty_Wrap 
      E_C_Reduce E_C_Reduce_List  Base_Congruence_Reduce WF_Config mtype WF_Type 
      E_WF_Wrap FJ_E_WF_invert EWrap_inject CT Conservative_Extension 
      build_te FJ_subtype_Wrap Conservative_subtype Conservative_WF_Type.
      
    Definition E_C_preservation_H5 := E_C_preservation_H5 C F M X ty_ext Ty E Context m_call_ext 
      subtype E_WF cld_ext md_ext Config FJ_E_Wrap FJ_Ty_Wrap E_C_Reduce E_C_Reduce_List 
      Base_Reduce_List WF_Config CT Conservative_Extension build_te FJ_subtype_Wrap 
      Conservative_E_WF.

    Definition E_C_preservation_H6 := E_C_preservation_H6 C F M X ty_ext Ty E Context m_call_ext 
      subtype E_WF cld_ext md_ext Config FJ_E_Wrap FJ_Ty_Wrap E_C_Reduce E_C_Reduce_List 
      Base_Reduce_List WF_Config CT Conservative_Extension build_te FJ_subtype_Wrap 
      Conservative_E_WF.

    Definition LJ_M_Call_Reduce_H1 := LJ_M_Call_Reduce_H1 C F M X ty_ext Ty E S Context m_call_ext mb_ext 
      subtype E_WF Empty cld_ext md_ext O Config Exception Value SLookup SUpdate 
      HLookup_Type Push_mb_ext Set_Exception NPE_Wrap FJ_E_Wrap LJ_Val_Wrap FJ_Ty_Wrap 
      MB_ext_S mbody trans S_trans E_C_Reduce  Base_M_Call_Reduce WF_Config CT 
      Conservative_Extension WF_Config_Set_NPE build_te FJ_subtype_Wrap Conservative_Extension_id.
    
    Definition S_trans_Wrap : forall s vars es', S_trans (LJ_S_Wrap s) vars es' = 
      LJ_S_trans _ _ _ _ _ _ _ eq_nat_dec Base_S _ Base_E trans S_trans s vars es' := 
      fun s vars es' => (refl_equal _).

    Print Term_subst_pres_typ_P.

    Definition Lem_2_10 := Term_subst_pres_typ.

    Definition Lem_2_10_S_H1 := Lem_2_10_S_H1 C F M X ty_ext Ty E S X_eq_dec 
      LJ_S_Wrap Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields LJ_S_WF_Wrap 
      cld_ext md_ext FJ_E_Wrap FJ_Ty_Wrap trans S_trans mtype WF_Type E_WF_Wrap 
      FJ_E_WF_invert EWrap_inject CT build_te update FJ_subtype_Wrap 
      lookup_update_eq lookup_update_neq lookup_update_neq'
      lookup_id Subtype_Update_list_id Lem_2_10 S_trans_Wrap.

    Definition Lem_2_10_S_H2 := Lem_2_10_S_H2 C F M X ty_ext Ty E S X_eq_dec 
      LJ_S_Wrap Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map 
      WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields LJ_S_WF_Wrap 
      cld_ext md_ext FJ_E_Wrap FJ_Ty_Wrap trans S_trans mtype WF_Type E_WF_Wrap 
      FJ_E_WF_invert EWrap_inject Lem_2_8 CT build_te update FJ_subtype_Wrap
      lookup_update_eq lookup_update_neq lookup_update_neq' lookup_id
      Subtype_Update_list_id Lem_2_10 S_trans_Wrap WF_fields_map_update_list.

    Definition Lem_2_10_S_H3 := Lem_2_10_S_H3 C F M X ty_ext Ty E S X_eq_dec 
      LJ_S_Wrap Context m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map 
      fields LJ_S_WF_Wrap FJ_E_Wrap FJ_Ty_Wrap trans S_trans update S_trans_Wrap.

    Definition Lem_2_10_S_H4 := Lem_2_10_S_H4 C F M X ty_ext Ty E S Context m_call_ext 
      subtype E_WF S_WF FJ_E_Wrap FJ_Ty_Wrap S_trans update.

    Definition Lem_2_10_S_H5 := Lem_2_10_S_H5 C F M X ty_ext Ty E S Context m_call_ext 
      subtype E_WF S_WF FJ_E_Wrap FJ_Ty_Wrap S_trans update.

    Fixpoint Lem_2_10_S gamma s (WF_s : S_WF gamma s) :=
      match WF_s with
        Base_S_WF gamma s S_case => LJ_S_WF_rect _ _ Lem_2_10_S_H1 Lem_2_10_S_H2 Lem_2_10_S_H3 
        Lem_2_10_S_H4 Lem_2_10_S_H5 _ _ S_case Lem_2_10_S
      end.

    Variables (WF_mb_ext_imp_WF_Ss : forall (gamma : Context) (mbe : mb_ext),
      WF_mb_ext gamma mbe -> S_WF gamma (MB_ext_S mbe))
      (WF_Config_push : forall (gamma : Context) (sigma : Config) (s : S),
      WF_Config gamma sigma -> S_WF gamma s -> WF_Config gamma (Push_mb_ext sigma s))
    (WF_Config_SUpdate_Fresh'' : forall (gamma : Context) (sigma : Config),
      WF_Config_SUpdate_Fresh_P'' C X ty_ext Ty Context subtype O Config Value SLookup
      SUpdate HLookup_Type LJ_Val_Wrap FJ_Ty_Wrap WF_Config update gamma sigma)
      (Update_WF_mtype_ty_0_map : forall (gamma : Context) 
      (ty_0 ty_0' : Ty) (x : Var X) (ty : Ty),
      WF_mtype_ty_0_map gamma ty_0 ty_0' -> WF_mtype_ty_0_map (update gamma x ty) ty_0 ty_0')
    (Update_WF_mtype_Us_map : forall (gamma : Context) 
      (mce : m_call_ext) (mtye : mty_ext) (Us Us' : list Ty) (x : Var X) (ty : Ty),
    WF_mtype_Us_map gamma mce mtye Us Us' -> WF_mtype_Us_map (update gamma x ty) mce mtye Us  Us')
    (Update_WF_mtype_U_map : forall (gamma : Context) (mce : m_call_ext) (mtye : mty_ext) 
      (U U' : Ty) (x : Var X) (ty : Ty), WF_mtype_U_map gamma mce mtye U U' ->
      WF_mtype_U_map (update gamma x ty) mce mtye U U')
    (Update_WF_mtype_ext : forall (gamma : Context) (mce : m_call_ext)
      (mtye : mty_ext) (x : Var X) (ty : Ty), WF_mtype_ext gamma mce mtye ->
      WF_mtype_ext (update gamma x ty) mce mtye)
      (Conservative_Extension_trans : forall gamma gamma' gamma'' : Context,
      Conservative_Extension gamma gamma' -> Conservative_Extension gamma' gamma'' ->
      Conservative_Extension gamma gamma'').

    Lemma Lem_2_12' : forall (m : M) (C_0 : Ty) (mce : m_call_ext) (mbe : mb_ext) 
      (xs : list X) (e : E),
      mbody Empty mce m C_0 (mb X E mb_ext mbe xs e) ->
      forall (C_0' : Ty) (delta : Context) (Ds Ds' : list Ty) 
        (D D' : Ty) (mtye : mty_ext),
        mtype Empty m C_0' (mty Ty mty_ext mtye Ds D) ->
        WF_mtype_ty_0_map delta C_0 C_0' ->
        WF_Type delta C_0 ->
        WF_mtype_ext delta mce mtye ->
        WF_mtype_Us_map delta mce mtye Ds Ds' ->
        WF_mtype_U_map delta mce mtye D D' ->
        exists S : Ty,
          exists Vars : list (cFJ.Var X * Ty),
            exists N : Ty,
              zip (this X :: Xs_To_Vars X xs) (N :: Ds') (@pair _ _) = Some Vars /\
              subtype delta C_0' N /\
              WF_Type delta N /\
              subtype delta S D' /\
              E_WF (State.update_list X Ty Context update delta Vars) e S /\
              WF_mb_ext (State.update_list X Ty Context update delta Vars) mbe.
      intros; eapply Lem_2_12; try eassumption; inversion H; subst; assumption.
    Qed.

    Definition LJ_M_Call_Reduce_H2 := LJ_M_Call_Reduce_H2 C F M X ty_ext Ty E S X_eq_dec 
      Context mty_ext m_call_ext mb_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields cld_ext md_ext O Config Exception Value 
      SLookup SUpdate HLookup_Type HLookup_Field Push_mb_ext Set_Exception NPE_Wrap 
      FJ_E_Wrap LJ_Val_Wrap FJ_Ty_Wrap MB_ext_S mbody trans S_trans E_C_Reduce 
      Base_M_Call_Reduce WF_Config mtype WF_Type E_WF_Wrap LJ_imp_WF_Config 
      FJ_E_WF_invert EWrap_inject CT Lem_2_9 WF_mtype_ty_0_map_total SLookup_id
      Conservative_Extension build_te update FJ_subtype_Wrap Conservative_Extension_id 
      Conservative_Extension_update Subtype_Update_list_id' WF_Type_update_id
      lookup_update_eq lookup_update_neq lookup_update_neq' LJ_Val_Wrap_inject 
      HTLookup_id WF_mb_ext Lem_2_10 Lem_2_12' Lem_2_10_S WF_mb_ext_imp_WF_Ss WF_Config_push 
      WF_Config_SUpdate_Fresh'' WF_mtype_ty_0_map_cl_id'' 
      Update_WF_mtype_ty_0_map Update_WF_mtype_Us_map Update_WF_mtype_U_map
      Update_WF_mtype_ext Conservative_Extension_trans.

    Definition S_preservation_H1 := 
      S_preservation_H1 C F M X ty_ext E S LJ_S_Wrap Context m_call_ext 
      S_WF O Config Exception Value SLookup SUpdate HUpdate_Field Set_Exception 
      NPE_Wrap FJ_E_Wrap LJ_Val_Wrap Check_NPE_Exception WF_Config S_Reduce
      Base_S_Reduce Conservative_Extension Conservative_Extension_id.

    Lemma LJ_S_Wrap_inject : forall s s' : LJ_S F X E S, LJ_S_Wrap s = LJ_S_Wrap s' -> s = s'.
      intros; injection H; auto.
    Qed.

    Lemma LJ_S_WF_invert : forall (gamma : Context) (s : LJ_S F X E S),
      S_WF gamma (LJ_S_Wrap s) ->
      LJ_S_WF F X Ty E S LJ_S_Wrap Context subtype E_WF S_WF Empty lookup WF_fields_map fields gamma 
      (LJ_S_Wrap s).
      intros; inversion H; subst; auto.
    Qed.

    Definition S_preservation_H2 := 
      S_preservation_H2 C F M X ty_ext Ty E S LJ_S_Wrap 
      Context m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map fields 
      O Config Exception Value SLookup SUpdate HUpdate_Field Set_Exception NPE_Wrap 
      FJ_E_Wrap LJ_Val_Wrap Check_NPE_Exception WF_Config S_Reduce Base_S_Reduce
      Conservative_Extension Conservative_Extension_id LJ_S_Wrap_inject LJ_S_WF_invert.

    Print LJ_WF_Config_SUpdate.

    Definition WF_Config_SUpdate := LJ_WF_Config_SUpdate C F M X ty_ext Ty E X_eq_dec Context 
      subtype Empty lookup fields cld_ext md_ext O Config Value SLookup SUpdate 
      HLookup_Type HLookup_Field LJ_Val_Wrap FJ_Ty_Wrap WF_Type CT SLookup_update_eq 
      SLookup_update_neq SLookup_id build_te FJ_subtype_Wrap HTLookup_SUpdate
      HTLookup_SUpdate' HFLookup_SUpdate HFLookup_SUpdate' lookup_id.

    Definition S_preservation_H3 := 
      S_preservation_H3 C F M X ty_ext Ty E S LJ_S_Wrap 
      Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields O Config Exception Value 
      SLookup SUpdate HUpdate_Field Set_Exception NPE_Wrap FJ_E_Wrap LJ_Val_Wrap 
      FJ_Ty_Wrap Check_NPE_Exception WF_Config S_Reduce Base_S_Reduce
      mtype WF_Type FJ_E_WF_invert EWrap_inject Conservative_Extension 
      Conservative_Extension_id LJ_S_Wrap_inject LJ_S_WF_invert WF_Config_SUpdate.

    Definition S_preservation_H4 := 
      S_preservation_H4 C F M X ty_ext E S LJ_S_Wrap Context m_call_ext 
      S_WF O Config Exception Value SLookup SUpdate HUpdate_Field Set_Exception 
      NPE_Wrap FJ_E_Wrap LJ_Val_Wrap Check_NPE_Exception WF_Config S_Reduce Base_S_Reduce
      Conservative_Extension WF_Config_Set_NPE Conservative_Extension_id.

    Print LJ_WF_Config_HFUpdate.

    Variables (SLookup_HFUpdate : forall sigma x v o f v', 
    SLookup sigma x v -> SLookup (HUpdate_Field sigma o f v') x v)
  (SLookup_HFUpdate' : forall sigma x v o f v', 
    SLookup (HUpdate_Field sigma o f v') x v -> SLookup sigma x v)
  (HTLookup_HFUpdate : forall sigma o ty o' f v', 
    HLookup_Type sigma o ty -> HLookup_Type (HUpdate_Field sigma o' f v') o ty)
  (HTLookup_HFUpdate' : forall sigma o ty o' f v', 
    HLookup_Type (HUpdate_Field sigma o' f v') o ty -> HLookup_Type sigma o ty)
  (HFLookup_HFUpdate_eq : forall sigma o f v, HLookup_Field (HUpdate_Field sigma o f v) o f v)
  (HFLookup_HFUpdate_o_neq : forall sigma o f v o' f' v', 
    HLookup_Field (HUpdate_Field sigma o' f' v') o f v -> o <> o' -> HLookup_Field sigma o f v)
  (HFLookup_HFUpdate_o_neq' : forall sigma o f v o' f' v', 
    HLookup_Field sigma o f v -> o <> o' -> HLookup_Field (HUpdate_Field sigma o' f' v') o f v)
  (HFLookup_HFUpdate_f_neq : forall sigma o f v f' v', 
    HLookup_Field (HUpdate_Field sigma o f' v') o f v -> f <> f' -> HLookup_Field sigma o f v)
  (HFLookup_HFUpdate_f_neq' : forall sigma o f v f' v', 
    HLookup_Field sigma o f v -> f <> f' -> HLookup_Field (HUpdate_Field sigma o f' v') o f v)
 (fds_distinct : forall (gamma : Context) (cl' : Ty)
      (fds : list (State.FD F Ty)),
      fields gamma cl' fds ->
      forall (cl1 cl2 : Ty) (f : F) (m n : nat)
        (fds' : list (cFJ.FD F Ty)),
        map
        (fun fd' : cFJ.FD F Ty =>
          match fd' with
            | fd _ f0 => f0
          end) fds' =
        map
        (fun fd' : cFJ.FD F Ty =>
          match fd' with
            | fd _ f0 => f0
          end) fds ->
        nth_error fds' m = Some (fd F Ty cl1 f) ->
        nth_error fds n = Some (fd F Ty cl2 f) -> m = n)
    (WF_fields_map_sub' : forall (gamma : Context) (c : cFJ.CL C)
      (tye tye' : ty_ext)
      (fds fds' : list (State.FD F Ty)),
      WF_fields_map gamma
      (FJ_Ty_Wrap (ty_def C ty_ext tye c))
      (FJ_Ty_Wrap (ty_def C ty_ext tye' c)) ->
      fields Empty (FJ_Ty_Wrap (ty_def C ty_ext tye c)) fds ->
      fields Empty (FJ_Ty_Wrap (ty_def C ty_ext tye' c))
      fds' ->
      List_P2'
      (fun fd' fd'' : cFJ.FD F Ty =>
        match fd' with
          | fd S' _ =>
            match fd'' with
              | fd T' _ => subtype Empty S' T'
            end
        end) fds' fds).
    
    Definition F_eq_dec := eq_nat_dec.

    Definition WF_Config_HFUpdate := LJ_WF_Config_HFUpdate C F M X ty_ext Ty E Context subtype 
      Empty lookup WF_fields_map fields cld_ext md_ext O Config Value SLookup 
      HLookup_Type HLookup_Field HUpdate_Field LJ_Val_Wrap FJ_Ty_Wrap WF_Type 
      Lem_2_8 WF_fields_map_id WF_fields_map_id' CT SLookup_id
      build_te FJ_subtype_Wrap LJ_Val_invert LJ_Val_Wrap_inject 
      Subtype_Weaken HTLookup_id O_eq_dec SLookup_HFUpdate 
      HTLookup_HFUpdate HTLookup_HFUpdate' HFLookup_HFUpdate_eq HFLookup_HFUpdate_o_neq 
      HFLookup_HFUpdate_o_neq' HFLookup_HFUpdate_f_neq' 
      F_eq_dec fds_distinct WF_fields_map_sub'.
          
    Definition S_preservation_H5 := S_preservation_H5 C F M X ty_ext Ty E S LJ_S_Wrap 
      Context mty_ext m_call_ext subtype E_WF S_WF Empty lookup WF_fields_map WF_mtype_ty_0_map 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext fields O Config Exception Value 
      SLookup SUpdate HUpdate_Field Set_Exception NPE_Wrap FJ_E_Wrap LJ_Val_Wrap 
      FJ_Ty_Wrap Check_NPE_Exception WF_Config S_Reduce Base_S_Reduce
      mtype WF_Type FJ_E_WF_invert EWrap_inject Conservative_Extension 
      Conservative_Extension_id LJ_S_Wrap_inject LJ_S_WF_invert WF_Config_HFUpdate.


    Fixpoint preservation e e' (red_e : Reduce e e') : preservation_def _ _ red_e :=
      match red_e with 
        |  FJ_S_Reduce t t' red_t => FJ_pres _ _ _ _ _ _ cFJ _ _ 
          cFJ_E _ _ _ CT _ subtype build_te cFJ_sub WF_Type fields
          mtype mbody_build_te mb_ext build_mb_ext map_mbody E_WF lookup
          WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map
          WF_mtype_ext Empty FJ_E_WF Update trans
          Reduce FJ_S_Reduce FJ_E_WF_invert EWrap_inject
          Fields_eq fds_distinct WF_fields_map_id WF_fields_map_id'
          WF_fields_map_sub Subtype_Weaken WF_mtype_map_sub Term_subst_pres_typ
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
      end.


    Lemma EWrap_inject : forall e e', Base_E e = Base_E e' -> e = e'.
      intros; injection H; intros; assumption.
    Qed.
    
    Lemma FJ_E_WF_invert : forall gamma (e : FJ_E _ _ _ _ _ _ _ ) c0, 
      Exp_WF gamma (Base_E e) c0 -> cFJ.Exp_WF _ _ _ _ _ Ty cFJ _ _ Base_E mty_ext
      Context subtype WF_Type fields mtype
      Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
      WF_mtype_ext Empty gamma (Base_E e) c0.
      intros; inversion H; subst; assumption.
    Qed.

    Definition preservation_def := cFJ.preservation Ty E Context subtype Exp_WF Reduce.
    
    Definition Reduce_List_preservation es es' (red_es : Congruence_List_Reduce es es') :=
      cFJ.Reduce_List_preservation _ _ _ subtype Exp_WF Congruence_List_Reduce es es' red_es.

    Fixpoint preservation e e' (red_e : Reduce e e') : preservation_def _ _ red_e :=
      match red_e with 
        |  FJ_S_Reduce t t' red_t => FJ_pres _ _ _ _ _ _ cFJ _ _ 
          Base_E _ _ _ CT _ subtype build_te cFJ_sub WF_Type fields
          mtype mbody_build_te
          map_e_ext mbody_m_call_map mbody_new_map Exp_WF lookup
          WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map
          WF_mtype_ext Empty FJ_Exp_WF Update trans
          Reduce FJ_S_Reduce FJ_E_WF_invert EWrap_inject
          Fields_eq fds_distinct WF_fields_map_id WF_fields_map_id'
          WF_fields_map_sub Subtype_Weaken' WF_mtype_map_sub Term_subst_pres_typ'
          Lem_2_12' t t' red_t
        | FJ_C_Reduce e e' fj_red_e' => FJ_C_preservation _ _ _ _ ty_ext _ cFJ _ _ Base_E _ _ _ CT
          _ subtype build_te cFJ_sub WF_Type fields mtype Exp_WF lookup WF_fields_map
          WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_Exp_WF 
          Reduce Congruence_List_Reduce FJ_C_Reduce FJ_E_WF_invert EWrap_inject
          Lem_2_8 Lem_2_9' WF_mtype_ty_0_map_tot e e' fj_red_e'
          preservation (fix preservation_list (es es' : list E) (red_es : Congruence_List_Reduce es es') : 
            Reduce_List_preservation _ _ red_es :=
            match red_es return Reduce_List_preservation _ _ red_es with
              FJ_Reduce_List es es' red_es' => FJ_C_List_preservation _ _ _ _ _ _ cFJ _ _ _ 
              CT _ subtype build_te cFJ_sub Exp_WF Empty Reduce
              Congruence_List_Reduce FJ_Reduce_List
              (fun g S T sub_S_T => Subtype_Weaken _ _ _ sub_S_T _ (refl_equal _))
              es es' red_es' preservation preservation_list end)             
      end.

    Inductive subexpression : E -> E -> Prop :=
      FJ_subexpression_Wrap : forall e e', FJ_subexpression _ _ _ _ _ _ _ Base_E subexpression subexpression_list e e' -> subexpression e e'
    with subexpression_list : E -> list E -> Prop :=
      subexpression_list_Wrap : forall e es, FJ_subexpression_list _ subexpression subexpression_list e es ->
        subexpression_list e es.

    Definition progress_1_def := cFJ.progress_1_def _ _ _ _ _ _ cFJ _ _ Base_E _ fields
      Exp_WF Empty subexpression.

    Definition progress_1_list_def := cFJ.progress_1_list_def _ _ _ _ _ _ cFJ _ _ Base_E 
      _ fields Exp_WF Empty subexpression_list.
        
    Lemma subexp_invert : forall (e : E) e',
      subexpression e (Base_E e') ->
      FJ_subexpression nat nat nat nat ty_ext E m_call_ext Base_E subexpression subexpression_list e (Base_E e').
      clear; intros; inversion H; subst; auto.
    Qed.
    
    Lemma subexpression_list_nil : forall e : E, ~ subexpression_list e nil.
      clear; unfold not; intros; inversion H; subst;
        eapply (FJ_subexpression_list_nil E subexpression subexpression_list _ H0).
    Qed.
    
    Lemma subexpression_list_destruct : forall e e' es, subexpression_list e (e' :: es) -> 
      (subexpression e e') \/ (subexpression_list e es).
      clear; intros; inversion H; subst; eapply FJ_subexpression_list_destruct; eassumption.
    Qed.
    
    Fixpoint progress_1 gamma e T (WF_e : Exp_WF gamma e T) :
      progress_1_def gamma e T WF_e :=
      match WF_e with 
        FJ_Exp_WF gamma e ty FJ_case => FJ_progress_1 _ _ _ _ _ _ cFJ _ _ Base_E _ _ subtype
        WF_Type fields mtype Exp_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Empty FJ_Exp_WF FJ_E_WF_invert EWrap_inject
        WF_fields_map_id WF_fields_map_id' subexpression subexpression_list 
        subexp_invert subexpression_list_nil subexpression_list_destruct gamma e ty FJ_case progress_1
      end.
    
    Definition progress_2_def := cFJ.progress_2_def _ _ _ _ _ _ cFJ _ _ Base_E _ _ CT _ 
      mbody_build_te map_e_ext mbody_m_call_map mbody_new_map Exp_WF Empty subexpression.
    
    Definition progress_2_list_def := cFJ.progress_2_list_def _ _ _ _ _ _ cFJ _ _ Base_E _ _ 
      CT _ mbody_build_te map_e_ext mbody_m_call_map mbody_new_map Exp_WF Empty 
      subexpression_list.
    
    Definition WF_mtype_ty_0_map_Empty_refl := FJ_WF_mtype_ty_0_map_Empty_refl _ _ _ cFJ Context.
    
    Definition mtype_mbody_build_te := FJ_mtype_mbody_build_te.
    
    Lemma map_e_ext'_tot : forall (ce : cld_ext) (te0 : FJ_ty_def_ext) (mce : FJ_m_call_ext)
      (me : md_ext) (e : E),
      exists e' : E,
        map_e_ext (mbody_m_call_map ce te0 mce me) (mbody_new_map ce te0 mce me)
        e e'.
      clear; intros; exists _; constructor; constructor.
    Qed.
    
  Fixpoint mtype_implies_mbody gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
    match mtype_m with 
      FJ_mtype gamma' m' ty' mty' fj_mtype_m => FJ_mtype_implies_mbody _ _ _ _ _ _ Base
      _ _ _ _ _ CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye
      FJ_mtype mbody_build_te map_e_ext mbody_m_call_map mbody_new_map
      Empty Base_inject mtype_build_tys_len map_e_ext'_tot
      mtype_mbody_build_te gamma' m' ty' mty' fj_mtype_m mtype_implies_mbody
    end.

  Lemma mtype_implies_mbody' : forall (mce : m_call_ext) (m : nat) (cl : cFJ.CL nat)
    (te : FJ_ty_def_ext) (mtye : mty_ext) (Us : list Ty) (U : Ty),
    mtype Empty m (cFJ (ty_def nat FJ_ty_def_ext te cl))
    (mty Ty mty_ext mtye Us U) ->
    exists xs : list nat,
      exists e : E,
      cFJ.mbody nat nat nat nat FJ_ty_def_ext Ty cFJ E m_call_ext
      md_ext cld_ext CT Context mbody_build_te map_e_ext mbody_m_call_map
      mbody_new_map Empty mce m (cFJ (ty_def nat FJ_ty_def_ext te cl))
      (mb nat E xs e) /\ length xs = length Us.
    intros; eapply mtype_implies_mbody; eauto.
  Qed.

  Fixpoint progress_2 gamma e T (WF_e : Exp_WF gamma e T) :
    progress_2_def gamma e T WF_e :=
    match WF_e with 
      FJ_Exp_WF gamma e ty FJ_case => FJ_progress_2 _ _ _ _ _ _ cFJ _ _ Base_E 
      _ _ _ CT _ subtype WF_Type fields mtype mbody_build_te map_e_ext mbody_m_call_map
      mbody_new_map Exp_WF lookup WF_fields_map WF_mtype_ty_0_map
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_Exp_WF FJ_E_WF_invert
      EWrap_inject WF_mtype_Us_map_len subexpression subexpression_list
      subexp_invert subexpression_list_nil subexpression_list_destruct
      WF_mtype_ty_0_map_Empty_refl mtype_implies_mbody' gamma e ty FJ_case progress_2
      end.

  End Proofs.
