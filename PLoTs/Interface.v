Section Interfaces.

  Require Import Arith.
  Require Import List.
  Require Import FJ_tactics.
  Require Import cFJ.

  Variables (I : Set)
    (ty_ext : Set)
    (Ty : Set).
  
  Inductive I_Ty : Set :=
    ity_def : ty_ext -> I -> I_Ty.

  Variable (I_Ty_Wrap : I_Ty -> Ty).
  Coercion I_Ty_Wrap : I_Ty >-> Ty.

  Variable (mty_ext : Set).
  Definition Mty := cFJ.Mty Ty mty_ext.

  Variables (X M : Set).
  Definition VD := cFJ.VD X Ty.

  Inductive Abs_Mty : Set :=
    abs_mty : mty_ext -> Ty -> M -> list VD -> Abs_Mty.

  Variable (Interface_ext : Set).
  Definition FJ_Interface_ext := unit.

  Inductive Interface : Set :=
    intd : Interface_ext -> I -> list Abs_Mty -> Interface.

  Definition Interface_ie (int : Interface) : Interface_ext := 
    match int with
      intd ie _ _ => ie
    end.

  Variables (Context : Set)
    (IT : I -> option Interface)
    (imtype_build_te : Interface_ext -> ty_ext -> ty_ext -> Prop)
    (imtype_build_tys : Interface_ext -> ty_ext -> Ty -> list VD -> mty_ext -> list Ty -> list Ty -> Prop)
    (imtype_build_mtye : Interface_ext -> ty_ext -> Ty -> list VD -> mty_ext -> mty_ext -> Prop).
  
  Definition I_imtype_build_te : FJ_Interface_ext -> ty_ext -> ty_ext -> Prop :=
    fun ie tye tye' => id_map_1 ie tye tye'.
  Definition I_imtype_build_tys : Interface_ext -> ty_ext -> Ty -> list VD -> FJ_mty_ext -> 
    list Ty -> list Ty -> Prop := id_map_5.
  Definition I_imtype_build_mtye : Interface_ext -> ty_ext -> Ty -> list VD -> mty_ext -> mty_ext -> Prop := 
    id_map_4.

  Inductive I_mtype : Context -> M -> Ty -> Mty -> Prop :=
    Imtype_fnd : forall gamma i ie te abs_mtys mtye ty m vds ty' tys' mtye', 
      IT i = Some (intd ie i abs_mtys) ->
      In (abs_mty mtye ty m vds) abs_mtys -> (*** Found the method ***)
  (*** Modify type extensions on parameter types ***)
      imtype_build_tys ie te ty vds mtye (map (fun vd' => match vd' with vd ty _ => ty end) vds) tys' -> 
  (*** Modify type extensions on return type ***)
      imtype_build_tys ie te ty vds mtye (ty :: nil) (ty' :: nil) -> 
  (*** Build method type extension ***)
      imtype_build_mtye ie te ty vds mtye mtye' -> 
      I_mtype gamma m (ity_def te i) (mty _ _ mtye' tys' ty').
  
  Variables (mtype : Context -> M -> Ty -> Mty -> Prop)
    (mtype_Wrap : forall gamma m ty mty, I_mtype gamma m ty mty -> mtype gamma m ty mty).
  Coercion mtype_Wrap : I_mtype >-> mtype.

  Variables (C F E md_ext cld_ext : Set).

  Definition L := cFJ.L C F M X ty_ext Ty E md_ext cld_ext.
  Definition cld := cFJ.cld C F M X ty_ext Ty E md_ext cld_ext.
  Definition I_cld_ext {cld_def_ext : Set} := (prod (list I_Ty) cld_def_ext).
  Definition FJ_Ty := cFJ.FJ_Ty C ty_ext.

  Definition I_build_te (cld_def_ext : Set) (build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) :
    @I_cld_ext cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop := fun ice te te' te''=> 
      build_te' (snd ice) te te' te''.

  Definition I_fields_build_te 
    (cld_def_ext : Set) (fields_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) :
    @I_cld_ext cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop := 
    fun ice te te' te''=> fields_build_te' (snd ice) te te' te''.

  Variables (CT : C -> option L)
    (isub_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (implements : cld_ext -> list I_Ty)
    (FJ_Ty_Wrap : FJ_Ty -> Ty)
    (ce_build_cte : cld_ext -> ty_ext -> Prop).

  Coercion FJ_Ty_Wrap : FJ_Ty >-> Ty.

  Definition I_isub_build_te (ce : cld_ext) (te te' te'' : ty_ext) := id_map_2 ce te te' te''.

  Definition I_implements {cld_ext : Set} (ie : @I_cld_ext cld_ext) : list I_Ty := fst ie.

  Inductive I_subtype : Context -> Ty -> Ty -> Prop :=
    I_sub_dir : forall gamma ce c d fs k' ms te te' te'' i,
      CT c = Some (cld ce c d fs k' ms) -> isub_build_te ce te te' te''->
      In (ity_def te' i) (implements ce) ->  
      I_subtype gamma (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) (ity_def te'' i).

  Variable (subtype : Context -> Ty -> Ty -> Prop)
    (I_subtype_Wrap : forall gamma ty ty', I_subtype gamma ty ty' -> subtype gamma ty ty').
  Coercion I_subtype_Wrap : I_subtype >-> subtype.

  Variable (ioverride : Context -> M -> FJ_Ty -> Mty -> Prop).

  Definition I_ioverride (gamma : Context)  (m : M) (ty : FJ_Ty) (mty : Mty) := 
    mtype gamma m ty mty.

  Definition I_L_WF_Ext {cld_ext' : Set} (gamma : Context) (ie : @I_cld_ext cld_ext') (c : C)
    (L_WF_cld : Context -> cld_ext' -> C -> Prop) (ce_build_cte : cld_ext -> ty_ext -> Prop) : Prop := 
    (forall Empty ity m mty ce c te, 
      In ity (fst ie) -> mtype Empty m ity mty -> ce_build_cte ce te ->
    ioverride Empty m (ty_def _ _ te (cl _ c)) mty)
    /\ L_WF_cld gamma (snd ie) c.

  Variable (wf_int_ext : Context -> Interface_ext -> ty_ext -> Prop).
  
  Definition I_wf_int_ext : Context -> Interface_ext -> ty_ext -> Prop := fun c i tye => True.
  
  Inductive I_WF_Type : Context -> Ty -> Prop :=
  | WF_Int : forall gamma i Int te, IT i = Some Int -> wf_int_ext gamma (Interface_ie Int) te ->
    I_WF_Type gamma (ity_def te i).
  
  Variables (WF_Type : Context -> Ty -> Prop)
    (I_WF_Type_Wrap : forall {gamma : Context} {ty : Ty}, I_WF_Type gamma ty -> WF_Type gamma ty).
  
  Coercion I_WF_Type_Wrap : I_WF_Type >-> WF_Type.
  
  Variables (Int_build_context : Interface_ext -> Context -> Prop)
    (Int_WF_Ext : Context -> Interface_ext -> I -> Prop)
    (Int_Meth_WF_Ext : Context -> Interface_ext -> mty_ext -> Prop)
    (Int_Meth_build_context : Interface_ext -> mty_ext -> Context -> Context -> Prop)
    (Empty : Context).

  Inductive I_Int_build_context : FJ_Interface_ext -> Context -> Prop :=
    i_int_build_context : forall ie, I_Int_build_context ie Empty.

  Definition FJ_Meth_WF_Ext : Context -> FJ_Interface_ext -> mty_ext -> Prop :=
    fun gamma ie mtye => True.

  Definition I_Int_WF_Ext : Context -> FJ_Interface_ext -> I -> Prop := fun gamma ce c => True.

  Definition I_Int_Meth_build_context : FJ_Interface_ext -> mty_ext -> Context -> Context -> Prop := id_map_2.
    
  Inductive Int_Meth_WF : Context -> I -> Abs_Mty -> Prop :=
    T_Md : forall gamma' gamma ie i amtye ty m vds, 
      Int_Meth_build_context ie amtye gamma' gamma -> 
      WF_Type gamma ty -> (*** Return Type Well-formed ***)
      List_P1 (fun Tx => match Tx with vd ty _ => WF_Type gamma ty end) vds -> (*** Parameter Types Well-formed ***)
      Int_Meth_WF_Ext gamma ie amtye -> (*** Additional premises for extensions ***)
      Int_Meth_WF gamma' i (abs_mty amtye ty m vds).
  
  Inductive I_WF : Interface -> Prop :=
    T_cld : forall i ie amtys gamma, 
      Int_build_context ie gamma -> (*** Build up the typing context ***)
      (forall amty, In amty amtys -> Int_Meth_WF gamma i amty) -> (*** Methods Well Formed ***)
      Int_WF_Ext gamma ie i -> (*** Additional premises for extensions ***)
      I_WF (intd ie i amtys).
  
  Section WF_Type_recursion.
    
    Variable (P : forall gamma ty, WF_Type gamma ty -> Prop)
      (Q : forall gamma int te, wf_int_ext gamma int te -> Prop).
    
    Hypothesis (H1 : forall gamma i Int te IT_i wf_int, Q gamma (Interface_ie Int) te wf_int -> 
      P _ _ (WF_Int gamma i Int te IT_i wf_int))
      (H2 : forall gamma int te wf_int, Q gamma int te wf_int).
    
    Definition I_WF_Type_rect' gamma ty (WF_ty : I_WF_Type gamma ty) : P _ _ WF_ty :=
      match WF_ty return P _ _ WF_ty with 
        WF_Int gamma i Int te IT_i wf_int => 
        H1 gamma i Int te IT_i wf_int (H2 _ _ _ wf_int)
      end.
  
  End WF_Type_recursion.

  Variable (update : Context -> Var X -> Ty -> Context).
  Definition update_list := cFJ.update_list _ _ _ update.
  
  Definition Weaken_WF_Type_update_list_P gamma ty (WF_ty : WF_Type gamma ty) :=
      forall vars gamma', gamma = (update_list Empty vars) -> WF_Type (update_list gamma' vars) ty.

  Definition Weaken_WF_Int_Ext_Q gamma' int te (wf_int : wf_int_ext gamma' int te) :=
    forall gamma vars, gamma' = (update_list Empty vars) ->
      wf_int_ext (update_list gamma vars) int te.

  Lemma I_Weaken_WF_Int_Ext : forall gamma' int te,
    forall (wf_int : I_wf_int_ext gamma' int te) gamma vars, gamma' =  (update_list Empty vars) ->
      I_wf_int_ext (update_list gamma vars) int te.
    unfold I_wf_int_ext; intros; auto.
  Qed.
  
  Lemma I_Weaken_WF_Type_update_list 
    (ext_rect : forall gamma int te wf_int, Weaken_WF_Int_Ext_Q gamma int te wf_int) : 
    forall gamma ty (WF_ty : I_WF_Type gamma ty), 
    Weaken_WF_Type_update_list_P _ _ WF_ty.
    intro.
    eapply I_WF_Type_rect' with (Q := Weaken_WF_Int_Ext_Q) (P := Weaken_WF_Type_update_list_P).
    unfold Weaken_WF_Int_Ext_Q; unfold Weaken_WF_Type_update_list_P; intros; subst.
    eapply I_WF_Type_Wrap; econstructor; eauto.
    assumption.
  Defined.
  
  Definition Weaken_Subtype_update_list_P := 
    cFJ.Weaken_Subtype_update_list_P _ _ _ subtype Empty update.
  
  Lemma I_Weaken_Subtype_update_list : forall gamma S T (sub_S_T : I_subtype gamma S T), 
    Weaken_Subtype_update_list_P _ _ _ sub_S_T.
    cbv beta delta; intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.

  Definition Subtype_Update_list_id'_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall vars, subtype (update_list gamma vars) S T.

  Lemma I_Weaken_Subtype_update_list_id' : forall gamma S T (sub_S_T : I_subtype gamma S T), 
    Subtype_Update_list_id'_P gamma S T sub_S_T.
    cbv beta delta; intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.
  
  Definition Subtype_Update_list_id_P := 
    cFJ.Subtype_Update_list_id_P X Ty Context subtype update.
  
  Lemma I_Subtype_Update_list_id: forall gamma ty ty' (sub_ty_ty' : I_subtype gamma ty ty'), 
    Subtype_Update_list_id_P _ _ _ sub_ty_ty'.
    cbv beta delta; intros; inversion sub_ty_ty'; subst.
    eapply I_subtype_Wrap; econstructor; eauto.
  Qed.

  Variables (wf_object_ext : Context -> ty_ext -> Prop)
    (wf_class_ext : Context -> cld_ext -> ty_ext -> Prop)
    (mtype_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (L_build_context : cld_ext -> Context -> Prop).  
  
  Definition WF_Type_par_Lem_P := WF_Type_par_Lem_P 
    _ _ _ _ ty_ext Ty FJ_Ty_Wrap _ _ _ CT Context 
    wf_object_ext WF_Type mtype_build_te L_build_context.

  Variable (Ty_inject : forall ty ty', FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty')
    (I_Ty_inject : forall ty ty', I_Ty_Wrap ty = I_Ty_Wrap ty' -> ty = ty')
    (Ty_discriminate : forall ty ty', FJ_Ty_Wrap ty <> I_Ty_Wrap ty').

  Lemma I_WF_Type_par_Lem : forall gamma ty (wf_ty : I_WF_Type gamma ty), 
    WF_Type_par_Lem_P _ _ wf_ty.
    intros; inversion wf_ty; subst.
    cbv beta delta; intros; elimtype False; eapply Ty_discriminate; eauto.
  Qed.

   Definition WF_Type_par_Lem_P' := 
     WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty FJ_Ty_Wrap E _ _ CT Context wf_class_ext
     WF_Type mtype_build_te L_build_context.

  Lemma I_WF_Type_par_Lem' : forall gamma ty (wf_ty : I_WF_Type gamma ty),
    WF_Type_par_Lem_P' _ _ wf_ty.
    intros; inversion wf_ty; subst.
    unfold WF_Type_par_Lem_P'; unfold cFJ.WF_Type_par_Lem_P'; intros.
    elimtype False; eapply Ty_discriminate; eauto.
  Qed.

  Lemma WF_Type_par : forall gamma ty (WF_ty : I_WF_Type gamma ty),
    WF_Type_par_P _ _ _ _ ty_ext Ty FJ_Ty_Wrap E _ _ CT _ WF_Type mtype_build_te
    L_build_context gamma ty WF_ty.
    unfold WF_Type_par_P; intros.
    inversion WF_ty; subst; elimtype False; apply (Ty_discriminate _ _ (sym_eq H7)).
  Qed.

  Variable (fields : Context -> Ty -> list (FD F Ty) -> Prop)
    (WF_fields_map : Context -> Ty -> Ty -> Prop).

  Lemma I_fields_build_te_id' (cld_def_ext : Set)
    (build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (fields_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (WF_fields_map' : Context -> Ty -> Ty -> Prop) 
    (H : forall gamma ce c d te te' te'' te3 te4 te5, 
      build_te' ce te te5 te' -> 
      WF_fields_map' gamma (FJ_Ty_Wrap (ty_def _ _ te' d)) (FJ_Ty_Wrap (ty_def _ _ te'' d)) -> 
      WF_fields_map' gamma (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) (FJ_Ty_Wrap (ty_def _ _ te3 (cl _ c))) ->
      fields_build_te' ce te3 te5 te4 -> te'' = te4) : 
    forall gamma ce c d te te' te'' te3 te4 te5, 
      I_build_te cld_def_ext build_te' ce te te5 te' -> 
      WF_fields_map' gamma (FJ_Ty_Wrap (ty_def _ _ te' d)) (FJ_Ty_Wrap (ty_def _ _ te'' d)) -> 
      WF_fields_map' gamma (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) (FJ_Ty_Wrap (ty_def _ _ te3 (cl _ c))) ->
      I_fields_build_te _ fields_build_te' ce te3 te5 te4 -> te'' = te4.
    intros; destruct ce; cbv in H0, H3; eauto.
  Qed.

  Definition Lem_2_8_P := cFJ.Lem_2_8_P _ _ _ subtype fields
    WF_fields_map Empty.

  Variable (Map_Fields_Ity_False : forall (ity : I_Ty) T gamma gamma' fds, 
    WF_fields_map gamma ity T -> ~fields gamma' T fds)
  (Fields_Ity_False : forall gamma (ity : I_Ty) fds, ~fields gamma ity fds)
  (fields_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
  (fields_build_tys : ty_ext -> cld_ext -> list Ty -> list Ty -> Prop).

  Lemma FJ_Fields_Ity_False : forall gamma (ity : I_Ty) fds, 
    ~ FJ_fields _ _ _ _ _ _ FJ_Ty_Wrap E md_ext cld_ext CT Context fields fields_build_te 
    fields_build_tys gamma ity fds.
    unfold not; intros; inversion H; subst; eapply Ty_discriminate; eauto.
  Qed.

  Lemma FJ_Map_Fields_Ity_False : forall (ity : I_Ty) T gamma gamma' fds, 
    FJ_WF_fields_map Ty Context gamma ity T -> ~fields gamma' T fds.
    intros; inversion H; subst; eauto.
  Qed.
    
  Lemma I_Lem_2_8 : forall gamma ty ty' (sub_ty_ty' : I_subtype gamma ty ty'), 
    Lem_2_8_P _ _ _ sub_ty_ty'.
    unfold Lem_2_8_P; unfold cFJ.Lem_2_8_P; 
      intros; inversion sub_ty_ty'; subst.
    elimtype False; eapply Map_Fields_Ity_False; eauto.
  Qed.

  Definition Weaken_mtype_P := Weaken_mtype_P _ _ _ _ mtype Empty.

  Lemma I_Weaken_mtype : forall gamma m ty mty (imtype : I_mtype gamma m ty mty), 
    Weaken_mtype_P _ _ _ _ imtype.
    unfold Weaken_mtype_P; unfold cFJ.Weaken_mtype_P; intros; 
      inversion imtype; subst.
    apply mtype_Wrap; econstructor; eauto.
  Qed.

  Variables (E_WF : Context -> E -> Ty -> Prop)
          (Meth_build_context : cld_ext ->
                                md_ext -> Context -> Context -> Prop)
          (Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop)
          (override : Context ->
                      M ->
                      cFJ.FJ_Ty C ty_ext ->
                      md_ext -> list Ty -> Ty -> Prop)
          (L_WF_Ext : Context -> cld_ext -> C -> Prop).

  Definition L_WF := cFJ.L_WF _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT _
    subtype WF_Type fields E_WF Empty update ce_build_cte 
    Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context.

  Variable (WF_CT : forall c l, CT c = Some l -> L_WF l)
    (imtype_invert : forall gamma m (ity : I_Ty) mty, mtype gamma m ity mty ->
      I_mtype gamma m ity mty)
    (mtype_build_tys : cld_ext -> ty_ext -> Ty -> list (cFJ.VD X Ty) -> md_ext -> list Ty -> list Ty -> Prop)
    (mtype_build_mtye : cld_ext -> ty_ext -> Ty -> list (cFJ.VD X Ty) -> md_ext -> mty_ext -> Prop)
    (Weaken_mtype : forall gamma m ty mty mtype_m, Weaken_mtype_P gamma m ty mty mtype_m).

  Definition FJ_mtype := cFJ.FJ_mtype _ _ _ _ _ Ty FJ_Ty_Wrap _ _ _ _ CT Context mtype mtype_build_te 
    mtype_build_tys mtype_build_mtye.

  Variable (FJ_mtype_Wrap : forall gamma m ty mty, 
    FJ_mtype gamma m ty mty -> mtype gamma m ty mty).

  Lemma I_ioverride_eq : forall gamma m ty mt, I_ioverride gamma m ty mt -> 
    mtype gamma m ty mt.
    unfold I_ioverride; auto.
  Qed.

  Variable (app_context : Context -> Context -> Context).

  Definition Weaken_Subtype_app_P := cFJ.Weaken_Subtype_app_P Ty Context subtype app_context.

  Lemma I_Weaken_Subtype_app : forall gamma ty ty' 
    (sub_ty_ty' : I_subtype gamma ty ty'), 
    Weaken_Subtype_app_P _ _ _ sub_ty_ty'.
    cbv beta delta; intros; inversion sub_ty_ty'; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.

  Lemma I_WF_Ext_ioverride : forall cld_ext'
    (unWrap_ce : cld_ext -> @I_cld_ext cld_ext') L_WF
    (implements_eq : forall ce, implements ce = (fst (unWrap_ce ce)))
    (build_cte_tot : forall ce, exists te, ce_build_cte ce te)
    (i_override_eq : forall gamma m ty mt, ioverride gamma m ty mt -> mtype gamma m ty mt)
    (mytype_build_cte : forall m c te te' mty, mtype Empty m (FJ_Ty_Wrap (ty_def _ _ te c)) mty ->
      mtype Empty m (FJ_Ty_Wrap (ty_def _ _ te' c)) mty)
    gamma ce c d fds k mds i ie m abs_mtys mtye U Us te te' te'',
    CT c = Some (cld ce c d fds k mds) ->
    I_L_WF_Ext gamma (unWrap_ce ce) c L_WF ce_build_cte ->
    I_isub_build_te ce te te' te'' ->
    mtype Empty m (ity_def te'' i) (mty Ty mty_ext mtye Us U) ->
    IT i = Some (intd ie i abs_mtys) ->
    In (ity_def te' i) (implements ce) ->
    mtype Empty m (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))) (mty Ty mty_ext mtye Us U).
    intros; unfold I_L_WF_Ext in H0; subst; rewrite implements_eq in H4.
    inversion H1; subst.
    destruct (build_cte_tot ce) as [te' bld_te'].
    generalize (i_override_eq _ _ _ _ ((proj1 H0) _ _ _ _ _ c _ H4 H2 bld_te')); intros.
    eauto.
  Qed.

  Variable WF_Ext_ioverride : forall gamma ce c d fds k mds i ie m abs_mtys mtye U Us te te' te'', 
    CT c = Some (cld ce c d fds k mds) -> 
    L_WF_Ext gamma ce c -> 
    isub_build_te ce te te' te'' -> 
    mtype Empty m (ity_def te'' i) (mty Ty mty_ext mtye Us U) -> 
    IT i = Some (intd ie i abs_mtys) -> 
    In (ity_def te' i) (implements ce) ->
    mtype Empty m (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))) (mty Ty mty_ext mtye Us U).

  Variables (m_call_ext : Set)
    (mbody_m_call_map : cld_ext -> ty_ext -> m_call_ext -> md_ext -> m_call_ext -> m_call_ext -> Prop)
    (mbody_new_map : cld_ext -> ty_ext -> m_call_ext -> md_ext -> ty_ext -> ty_ext -> Prop)
    (map_e_ext' : (m_call_ext -> m_call_ext -> Prop) -> (ty_ext -> ty_ext -> Prop) -> E -> E -> Prop)
    (mbody_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_ext -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop)
    (WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop).

  Variable WF_mtype_ty_0_map_Ity : forall gamma I I', 
    WF_mtype_ty_0_map gamma (I_Ty_Wrap I) I' -> I_Ty_Wrap I = I'.

  Lemma FJ_WF_mtype_ty_0_map_Ity : forall gamma I I',
    cFJ.FJ_WF_mtype_ty_0_map Ty Context gamma (I_Ty_Wrap I) I' -> I_Ty_Wrap I = I'.
    intros; inversion H; subst; reflexivity.
  Qed.

  Variable WF_mtype_ty_0_map_cl_id'' : forall delta te d S', 
    WF_mtype_ty_0_map delta (FJ_Ty_Wrap (ty_def _ _ te d)) S' -> S' = FJ_Ty_Wrap (ty_def _ _ te d).
  Variable build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop.
  Variable FJ_subtype_Wrap : forall gamma S T,
    cFJ.FJ_subtype _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT Context subtype build_te gamma S T -> subtype gamma S T.
  Variable L_WF_Ext_ioverride : forall gamma ce c ity te m mty, 
    L_WF_Ext gamma ce c -> In ity (implements ce) -> mtype Empty m ity mty -> 
    ce_build_cte ce te -> ioverride Empty m (ty_def _ _ te (cl _ c)) mty.
  Variable ce_build_cte_tot : forall ce, exists te, ce_build_cte ce te.

  Definition Lem_2_9_P := cFJ.Lem_2_9_P _ _ _ _ _ subtype mtype WF_mtype_ty_0_map WF_mtype_Us_map 
      WF_mtype_U_map WF_mtype_ext Empty.

  Lemma I_Lem_2_9 : forall gamma ty ty' (sub_ty_ty' : I_subtype gamma ty ty'), 
    Lem_2_9_P _ _ _ sub_ty_ty'.
    cbv beta delta; intros; inversion sub_ty_ty'; subst.
    apply WF_mtype_ty_0_map_Ity in H; apply WF_mtype_ty_0_map_cl_id'' in H4; subst.
    apply imtype_invert in H0; inversion H0; subst.
    apply I_Ty_inject in H; injection H; intros; subst; clear H sub_ty_ty'.
    generalize (WF_CT _ _ H5); intros WF_c; inversion WF_c; subst.
    exists U; exists Us; exists mtye; split.
    eapply WF_Ext_ioverride; eauto.
    exists U'; repeat split; eauto.
    eapply FJ_subtype_Wrap; constructor.
  Qed.

  Definition Subtype_Weaken_P := cFJ.Subtype_Weaken_P _ _ subtype Empty.

  Lemma I_Subtype_Weaken : forall gamma ty ty' (sub_ty_ty' : I_subtype gamma ty ty'), 
    Subtype_Weaken_P _ _ _ sub_ty_ty'.
    cbv beta delta; intros; inversion sub_ty_ty'; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.
  
  Definition WF_int_ext_Update_Vars_id_Q delta' int te (wf_l : wf_int_ext delta' int te) :=
    forall delta Vars, delta' = (update_list delta Vars) -> wf_int_ext delta int te.
  
  Lemma I_WF_int_ext_Update_Vars_id : forall delta' int te (wf_l : I_wf_int_ext delta' int te)
    delta Vars, delta' = (update_list delta Vars) -> I_wf_int_ext delta int te.
    unfold I_wf_int_ext; auto.
  Qed.
  
  Definition WF_Type_update_list_id_P gamma ty (wf_ty : WF_Type gamma ty) :=
    forall delta Vars, gamma = (update_list delta Vars) -> WF_Type delta ty.
  
  Variable mb_ext : Set.
  Variable build_mb_ext : cld_ext -> ty_ext -> m_call_ext -> md_ext -> mb_ext -> Prop.
  Variable map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop.

  Lemma I_WF_Type_update_list_id 
    (ext_rect : forall gamma int te wf_int, WF_int_ext_Update_Vars_id_Q gamma int te wf_int) : 
    forall gamma ty (WF_ty : I_WF_Type gamma ty), 
    WF_Type_update_list_id_P _ _ WF_ty.
    intro.
    eapply I_WF_Type_rect' with (Q := WF_int_ext_Update_Vars_id_Q) (P := WF_Type_update_list_id_P).
    unfold WF_int_ext_Update_Vars_id_Q; unfold WF_Type_update_list_id_P; intros; subst. 
    apply I_WF_Type_Wrap; econstructor; eauto.
    assumption.
  Defined.
  
  Definition mtype_implies_mbody_P := mtype_implies_mbody_P _ _ _ _ _ _ FJ_Ty_Wrap 
    _ _ _ _ _ CT _ mtype mbody_build_te mb_ext build_mb_ext map_mbody Empty.

  Lemma I_mtype_implies_mbody : forall gamma m ty mty (imtype : I_mtype gamma m ty mty), 
    mtype_implies_mbody_P _ _ _ _ imtype.
    cbv delta beta; intros; subst; inversion imtype; subst.
    elimtype False; eapply Ty_discriminate; eauto. 
  Qed.

  Definition I_Subtype_Update_list_id'_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall vars, subtype (update_list gamma vars) S T.

  Lemma I_Subtype_Update_list_id' :  forall gamma ty ty' (sub_ty_ty' : I_subtype gamma ty ty'), 
    I_Subtype_Update_list_id'_P _ _ _ sub_ty_ty'.
    unfold I_Subtype_Update_list_id'_P; intros; inversion sub_ty_ty'; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed. 

   Lemma FJ_ce_build_cte_tot : forall (ce : cFJ.FJ_cld_ext), exists te, FJ_ce_build_cte ce te.
     intros; exists tt; constructor.
   Qed.

End Interfaces.
