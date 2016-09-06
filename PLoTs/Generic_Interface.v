Require Import FJ_tactics.
Require Import cFJ.
Require Import Interface.
Require Import Generic.

Require Import List.
Require Import Arith.

Section Generic_Interfaces.

  Variables (I C TX Ty ty_ext mty_ext X M Interface_ext N : Set).
  Definition GTy := GTy TX.
  Definition I_Ty := I_Ty I ty_ext.

  Variables (Ty_Wrap : GTy -> Ty)
    (Context : Set)
    (TLookup : Context -> TX -> N -> Prop)
    (WF_Type : Context -> Ty -> Prop)
    (subtype : Context -> Ty -> Ty -> Prop)
    (GJ_WF_Type_Wrap : forall {gamma : Context} {ty : Ty}, GJ_WF_Type TX Ty Ty_Wrap N Context TLookup gamma ty -> 
      WF_Type gamma ty)
    (Ty_trans : Ty -> list TX -> list Ty -> Ty).
  
  Definition Interface := Interface I Ty mty_ext X M Interface_ext.
  
  Variable (wf_int_ext : Context -> Interface_ext -> ty_ext -> Prop).
  
  Definition TyP_List := TyP_List TX N.
  
  Definition GInterface_ext {int_ext : Set} := prod TyP_List int_ext.
  
  Variable N_Wrap : N -> Ty.
  Variable I_N_Wrap : I_Ty -> N.
  Definition I_Ty_Wrap (ity : I_Ty) : Ty := N_Wrap (I_N_Wrap ity).
    
  Coercion N_Wrap : N >-> Ty.
  Coercion Ty_Wrap : GTy >-> Ty.

  Coercion I_Ty_Wrap : I_Ty >-> Ty.
    
  Inductive I_wf_int_ext {int_ext ty_ext : Set} : 
    Context -> @GInterface_ext int_ext -> 
    (@GTy_ext Ty ty_ext) -> Prop :=
    i_wf_int_ext : forall ie delta (typs : TyP_List) tys te, 
      List_P1 (WF_Type delta) tys -> (*** All type are well-formed ***)
      length typs = length tys -> (*** Same number of type arguments and type parameters ***)
      List_P2 tys (*** Each type argument is a subtype of the declared type bound ***)
      (map (fun (typ' : GTy * N) => Ty_trans 
        (snd typ') (Extract_TyVar TX _ typs) tys) typs) (subtype delta) ->
      I_wf_int_ext delta (typs, ie) (tys, te).

  Variable mty_def_ext : Set.
  Variable build_fresh : list Ty -> Ty -> list Ty -> list TX -> TyP_List -> list TX -> Prop.
  Definition VD := cFJ.VD X Ty.

  Inductive imtype_build_tys {int_ext ty_ext : Set}
    (imtype_build_tys' : int_ext -> ty_ext -> Ty -> list VD -> mty_def_ext -> list Ty -> list Ty -> Prop) :
    @GInterface_ext int_ext -> @GTy_ext Ty ty_ext -> Ty -> list VD -> 
    @Generic.mty_ext TX N mty_def_ext -> list Ty -> list Ty -> Prop :=
    I_imtype_build_tys : forall (ie : int_ext) (te : ty_ext) (typs typs' : TyP_List) (ty : Ty) 
      vds (mtye : mty_def_ext) (fresh_tys : list TX) (tys tys' vd_tys : list Ty),
      length typs = length tys -> 
      imtype_build_tys' ie te ty vds mtye vd_tys tys' -> (*** Map the parameter types using the previous definitions ***)
      build_fresh tys ty (map (fun vd' => match vd' with | vd ty _ => ty end) vds)
      (Extract_TyVar _ _ typs) typs' fresh_tys -> (*** Get fresh vars that aren't in tys ***)
      imtype_build_tys imtype_build_tys' (typs, ie) (tys, te) ty vds (typs', mtye)
      vd_tys (Tys_Trans _ _ _ Ty_trans typs tys 
        (Tys_Trans _ _ _ Ty_trans typs' (map (fun Y => Ty_Wrap (TyVar _ Y)) fresh_tys) tys')).
  
  Variable N_Trans : TyP_List -> list Ty -> N -> N.
  
  Inductive imtype_build_mtye {int_ext ty_def_ext : Set}
    (imtype_build_mtye' : int_ext -> ty_def_ext -> Ty -> list VD -> mty_def_ext -> mty_def_ext -> Prop) : 
    @GInterface_ext int_ext -> @GTy_ext Ty ty_def_ext -> Ty -> list VD ->  
    @Generic.mty_ext TX N mty_def_ext -> @Generic.mty_ext TX N mty_def_ext -> Prop :=
    I_imtype_build_mtye : forall (ie : int_ext) (te : ty_def_ext) (mtye mtye'' : mty_def_ext)
      (typs typs' : TyP_List) (ty : Ty) vds (fresh_tys : list TX) (tys vd_tys : list Ty) (ZQs' : TyP_List)
      (eq_ZQs' : zip fresh_tys 
        (map (fun (typ' : GTy * N) => N_Trans typs' 
          (map (fun Y => Ty_Wrap (TyVar _ Y)) fresh_tys) (snd typ')) typs') (*** Patch up Bounds***)
        (fun x => @pair _ _ (TyVar _ x)) = Some ZQs'),
      imtype_build_mtye' ie te ty vds mtye mtye'' -> 
      build_fresh tys ty (map (fun vd' => match vd' with | vd ty _ => ty end) vds)
      (Extract_TyVar _ _ typs) typs' fresh_tys -> (*** Get fresh vars that aren't in tys ***)
      imtype_build_mtye imtype_build_mtye' (typs, ie) (tys, te) ty vds (typs', mtye) 
      ((@Generic.Typs_Trans TX Ty N N_Trans typs tys ZQs'), mtye'').
  
  Variable (TUpdate : Context -> TX -> N -> Context).
    
  Variable (cld_ext : Set) 
    (ce_build_cte : cld_ext -> ty_ext -> Prop)
    (mtype : Context -> M -> Ty -> Mty Ty mty_ext -> Prop)
    (implements : cld_ext -> list (Interface.I_Ty I ty_ext))
    (ioverride : Context -> M -> FJ_Ty C ty_ext -> Mty Ty mty_ext -> Prop)
    (FJ_N_Wrap : FJ_Ty ty_ext C -> N).
        
  Definition FJ_Ty_Wrap ty := N_Wrap (FJ_N_Wrap ty).

  Definition GI_L_WF_Ext (Empty : Context)
    (gamma : Context) (ce : cld_ext) : Prop := 
    (forall ity, In ity (implements ce) -> WF_Type gamma (I_Ty_Wrap ity)).

  Definition update_Tlist := update_Tlist _ _ _ TUpdate.

  Inductive GI_Int_build_context {int_def_ext : Set} (Int_build_context' : int_def_ext -> Context -> Prop)
    : @GInterface_ext int_def_ext -> Context -> Prop :=
    GI_I_build_context : forall ie gamma XNs, 
      Int_build_context' ie gamma ->
      GI_Int_build_context Int_build_context' (XNs, ie) (update_Tlist gamma XNs).
  
  Inductive GI_Int_WF_Ext {int_def_ext : Set} (I_WF_Ext' : Context -> int_def_ext -> I -> Prop ) :
    Context -> @GInterface_ext int_def_ext -> I -> Prop :=
    GI_I_WF_Ext : forall gamma ie typs i, I_WF_Ext' gamma ie i ->
      List_P1 (fun typ => WF_Type gamma (N_Wrap (snd typ))) typs -> (*** All the bounds well-formed? ***)
      GI_Int_WF_Ext I_WF_Ext' gamma (typs, ie) i.

  Definition GI_Int_Meth_WF_Ext {int_def_ext mty_ext : Set} 
    (Int_Meth_WF_Ext' : Context -> int_def_ext -> mty_ext -> Prop)
    (gamma : Context) (ie : @GInterface_ext int_def_ext) (amtye : @Generic.mty_ext TX N mty_ext) : Prop :=
    match ie, amtye with 
      (XNs, ce'), (YOs, mde') => List_P1 (fun xn : (GTy * N) => WF_Type gamma (snd xn)) YOs /\ 
      Int_Meth_WF_Ext' gamma ce' mde'
    end.
  
  Inductive GI_Int_Meth_build_context {int_def_ext mty_def_ext : Set} 
    (build_context' : int_def_ext -> mty_def_ext -> Context -> Context -> Prop) :
    @GInterface_ext int_def_ext -> @Generic.mty_ext TX N mty_def_ext -> Context -> Context -> Prop :=
    build_context : forall ie amtye gamma gamma' XNs YOs, build_context' ie amtye gamma gamma' ->
      GI_Int_Meth_build_context build_context' (XNs, ie) (YOs, amtye) gamma (update_Tlist gamma' (XNs ++ YOs)).

  Section Preservation.

    Variable (Empty : Context)
      (Update : Context -> Var X -> Ty -> Context)
      (int_def_ext ty_def_ext: Set)
      (Weaken_Subtype_update_list : forall delta S T sub_S_T, 
        cFJ.Weaken_Subtype_update_list_P _ _ _ subtype Empty Update delta S T sub_S_T)
      (app_context : Context -> Context -> Context)
      (TLookup_app : forall gamma delta X ty, TLookup gamma X ty -> TLookup (app_context gamma delta) X ty).
    
  Definition update_list := cFJ.update_list X Ty Context Update.

  Definition Weaken_WF_update_list_Q'' delta int te (_ : wf_int_ext delta int te) :=
    forall gamma vars, delta = (update_list Empty vars) -> wf_int_ext (update_list gamma vars) int te.
     
  Definition Weaken_WF_update_list_P1 delta' tys (_ : List_P1 (WF_Type delta') tys) :=
    forall Vars delta, delta' = update_list Empty Vars -> List_P1 (WF_Type (update_list delta Vars)) tys.

  Lemma I_Weaken_WF_update_list_ext : forall (ie : int_def_ext) gamma (typs : TyP_List) tys 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Weaken_WF_update_list_P1 gamma tys P1-> 
    forall delta Vars, gamma = update_list Empty Vars -> 
      I_wf_int_ext (update_list delta Vars) 
      (typs, ie) (tys, te).
    unfold Weaken_WF_Update_list_P1; intros; subst.
    constructor; auto.
    destruct P2 as [In_ty NIn_ty]; split; intros.
    destruct (In_ty _ _ H0) as [b [nth_b sub_a_b]]; exists b; split; auto.
    eapply Weaken_Subtype_update_list; try eassumption; reflexivity.
    auto.
  Defined.

  Variable (GJ_Ty_Wrap : Generic.GTy TX -> Ty)
    (Bound' : Context -> Ty -> Ty -> Prop)
    (N_Bound'_Wrap : forall gamma ty ty', N_Bound Ty N N_Wrap Context gamma ty ty' -> Bound' gamma ty ty').

  Definition Bound_total_def gamma S T (sub_S_T : subtype gamma S T) :=
    forall T', Bound' gamma T T' -> exists S' , Bound' gamma S S'.

  Variables (F E md_ext : Set)
    (CT : C -> option (L ty_ext Ty X M C F E md_ext cld_ext))
    (isub_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (I_subtype_Wrap : forall gamma S T,
      I_subtype I ty_ext Ty I_Ty_Wrap X M Context C F E md_ext cld_ext CT 
      isub_build_te implements FJ_Ty_Wrap gamma S T -> subtype gamma S T).

  Definition I_subtype := I_subtype I ty_ext Ty I_Ty_Wrap _ _ Context _ _ _ _ _ CT 
    isub_build_te implements FJ_Ty_Wrap.

  Lemma I_Bound_total : forall gamma S T 
    (sub_S_T : I_subtype gamma S T), Bound_total_def _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Bound_total_def; intros; inversion sub_S_T; subst.
    exists (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))); apply N_Bound'_Wrap.
    unfold FJ_Ty_Wrap; econstructor.
  Qed.

  Definition WF_Type_update_list_id_P1 := WF_Type_update_list_id_Q'_P1 _ _ WF_Type _ Update.

  Variable (Subtype_Update_list_id : forall gamma S T sub_S_T, 
    cFJ.Subtype_Update_list_id_P X _ _ subtype Update gamma S T sub_S_T).

  Lemma WF_int_ext_update_list_id : forall (ie : int_def_ext) gamma (typs : TyP_List) tys 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    WF_Type_update_list_id_P1 gamma tys P1 -> 
    forall delta Vars, gamma = (update_list delta Vars) -> I_wf_int_ext delta 
      (typs, ie) (tys, te).
    unfold WF_Type_update_list_id_P1; unfold WF_Type_update_list_id_Q'_P1; intros; subst.
    constructor; auto.
    apply (H _ _ (refl_equal _)).
    destruct P2 as [In_ty NIn_ty]; split; intros.
    destruct (In_ty _ _ H0) as [b [nth_b sub_a_b]]; exists b; split; auto.
    eapply Subtype_Update_list_id; try eassumption; reflexivity.
    auto.
  Defined.

  Definition Weakening_2_1_1_P := Generic.Weakening_2_1_1_P _ _ subtype app_context.

  Lemma I_Weakening_2_1_1 : forall delta S T (sub_S_T : I_subtype delta S T),
    Weakening_2_1_1_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Weakening_2_1_1_P; unfold Generic.Weakening_2_1_1_P; intros; apply I_subtype_Wrap;
      inversion sub_S_T; subst; econstructor; eauto.
  Qed.

  Variable (Weakening_2_1_1 : forall gamma S T sub_S_T, Weakening_2_1_1_P gamma S T sub_S_T)
    (IT : I -> option (Interface.Interface I Ty mty_ext X M Interface_ext)).

  Definition Weakening_2_1_2_P := Weakening_2_1_2_P _ _ WF_Type app_context.

  Definition Weakening_2_1_2_P1 := Weakening_2_1_2_P1 _ _ WF_Type app_context.

  Definition Weakening_2_1_2_Q'' delta int te (_ : wf_int_ext delta int te) :=
    forall gamma, wf_int_ext (app_context delta gamma) int te.

  Lemma I_Weakening_2_1_2_ext : forall (ie : int_def_ext) gamma (typs : TyP_List) tys 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Weakening_2_1_2_P1 gamma tys P1-> 
    forall delta,
      I_wf_int_ext (app_context gamma delta) 
      (typs, ie) (tys, te).
    intros; subst.
    constructor; auto.
    destruct P2 as [In_ty NIn_ty]; split; intros.
    destruct (In_ty _ _ H0) as [b [nth_b sub_a_b]]; exists b; split; auto.
    eapply Weakening_2_1_1; try eassumption; reflexivity.
    auto.
  Defined.

  Definition I_WF_Type := I_WF_Type _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext.
  
  Variable (I_WF_Type_Wrap : forall gamma ty, I_WF_Type gamma ty -> WF_Type gamma ty).

  Definition Interface_ie int := Interface_ie I Ty mty_ext X M Interface_ext int.

  Lemma I_Weakening_2_1_2 : forall (gamma : Context) i int te IT_i wf_int,
    Weakening_2_1_2_Q'' gamma (Interface_ie int) te wf_int ->
    Weakening_2_1_2_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold Weakening_2_1_2_Q''; unfold Weakening_2_1_2_P; unfold Generic.Weakening_2_1_2_P; 
      intros; subst.
    eapply I_WF_Type_Wrap; econstructor; eauto.
  Defined.

  Variables (Free_Vars : Ty -> list TX -> Prop)
    (TE_Free_Vars : ty_ext -> list TX -> Prop)
    (TE_trans : ty_ext -> list TX -> list Ty -> ty_ext).

  Definition I_Ty_Trans (ty : I_Ty) txs tys : Ty :=
    match ty with 
      ity_def te i => (I_Ty_Wrap (ity_def _ _ (TE_trans te txs tys) i))
    end.

  Inductive I_Free_Vars : Ty -> list TX -> Prop :=
    I_Ty_def : forall i te txs, TE_Free_Vars te txs ->
      I_Free_Vars (I_Ty_Wrap (ity_def _ _ te i)) txs.

  Definition Ty_trans_nil_P := Ty_trans_nil_P _ _ Ty_trans.
  Definition Ty_trans_nil'_P := Ty_trans_nil'_P _ _ Ty_trans.
  Definition TE_trans_nil_P := TE_trans_nil_P _ _ _ TE_trans.
  Definition TE_trans_nil'_P := TE_trans_nil'_P _ _ _ TE_trans.

  Variables (I_Free_Vars_Wrap : forall ty txs, I_Free_Vars ty txs -> Free_Vars ty txs)
    (I_Free_Vars_invert : forall ty txs, Free_Vars (I_Ty_Wrap ty) txs -> I_Free_Vars (I_Ty_Wrap ty) txs)
    (I_Ty_trans_invert : forall ty txs tys, Ty_trans (I_Ty_Wrap ty) txs tys = I_Ty_Trans ty txs tys)
    (I_Ty_Wrap_inject : forall ty ty', I_Ty_Wrap ty = I_Ty_Wrap ty' -> ty = ty')
    (FJ_Ty_Wrap_inject : forall ty ty',FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty')
    (FJ_Ty_trans_invert : forall ty txs tys, Ty_trans (FJ_Ty_Wrap ty) txs tys =
      FJ_Ty_Trans _ _ _ _ N N_Wrap FJ_N_Wrap TE_trans ty txs tys).

  Lemma I_Ty_trans_nil : forall te i, TE_trans_nil_P te -> Ty_trans_nil_P (I_Ty_Wrap (ity_def _ _ te i)).
    simpl; unfold Ty_trans_nil_P; unfold Generic.Ty_trans_nil_P; intros.
    rewrite I_Ty_trans_invert; simpl.
    congruence.
  Defined.

  Lemma I_Ty_trans_nil' : forall te i, TE_trans_nil'_P te -> Ty_trans_nil'_P (I_Ty_Wrap (ity_def _ _ te i)).
    simpl; unfold Ty_trans_nil'_P; unfold Generic.Ty_trans_nil'_P; intros.
    rewrite I_Ty_trans_invert; simpl.
    congruence.
  Defined.
  
  Variables (Ty_trans_nil : forall ty, Ty_trans_nil_P ty)
    (Ty_trans_nil' : forall ty, Ty_trans_nil'_P ty)
    (TE_trans_nil : forall te, TE_trans_nil_P te)
    (TE_trans_nil' : forall te, TE_trans_nil'_P te).

  Definition Free_Vars_Subst_Q := Free_Vars_Subst_Q _ _ _ TE_Free_Vars TE_trans.
  
  Lemma I_Free_Vars_Subst : forall te i, Free_Vars_Subst_Q te -> 
    forall (Xs Ys : list TX) (Us : list Ty),
    (forall X, In X Xs -> ~ In X Ys) -> Free_Vars (I_Ty_Wrap (ity_def _ _ te i)) Xs -> 
    I_Ty_Trans (ity_def _ _ te i) Ys Us = I_Ty_Wrap (ity_def _ _ te i).
    simpl; intros; erewrite H.
    reflexivity.
    eapply H0.
    apply I_Free_Vars_invert in H1; inversion H1; subst.
    apply I_Ty_Wrap_inject in H2; injection H2; intros; subst; assumption.
  Qed.

  Definition map_Ty_trans_P := map_Ty_trans_P _ _ N Ty_trans Free_Vars.
  
  Definition map_Ty_trans_Q := map_Ty_trans_Q _ _ _ N Ty_trans TE_Free_Vars TE_trans.

  Lemma I_map_Ty_trans : forall te i, map_Ty_trans_Q te -> map_Ty_trans_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold map_Ty_trans_Q; unfold map_Ty_trans_P; unfold Generic.map_Ty_trans_Q; 
      unfold Generic.map_Ty_trans_P; intros.
    repeat (rewrite I_Ty_trans_invert; simpl).
    apply I_Free_Vars_invert in H0; inversion H0; apply I_Ty_Wrap_inject in H2; 
      injection H2; intros; subst; clear H2.
    erewrite H; eauto.
  Qed.
  
  Definition map_Ty_trans_P' := map_Ty_trans_P' _ _ N Ty_trans Free_Vars.

  Definition map_Ty_trans_Q' := map_Ty_trans_Q' _ _ _ N Ty_trans TE_Free_Vars TE_trans.

  Lemma I_map_Ty_trans' : forall te i, map_Ty_trans_Q' te -> map_Ty_trans_P' (I_Ty_Wrap (ity_def _ _ te i)).
    unfold map_Ty_trans_Q'; unfold map_Ty_trans_P'; unfold Generic.map_Ty_trans_Q'; 
      unfold Generic.map_Ty_trans_P'; intros.
    repeat (rewrite I_Ty_trans_invert; simpl).
    apply I_Free_Vars_invert in H0; inversion H0; apply I_Ty_Wrap_inject in H3; 
      injection H3; intros; subst; clear H3.
    erewrite H; eauto.
  Qed.

  Definition wf_free_vars_P := wf_free_vars_P _ _ _ _ Empty WF_Type TUpdate Free_Vars.

  Definition wf_free_vars_Q'' delta int te (_ : wf_int_ext delta int te) :=
    forall XNs Xs, delta = update_Tlist Empty XNs -> TE_Free_Vars te Xs ->
      forall X, In X Xs -> In X (Extract_TyVar _ _ XNs).

  Definition wf_free_vars_P1 := wf_free_vars_Q_P1 _ _ _ _ Empty WF_Type TUpdate Free_Vars.

  Lemma I_wf_free_vars_ext : forall (ie : int_def_ext) 
    gamma (typs : TyP_List) tys (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    wf_free_vars_P1 gamma tys P1-> 
    forall XNs Xs, gamma = update_Tlist Empty XNs -> 
      GJ_TE_Free_Vars _ _ _ Free_Vars (tys, te) Xs ->
      forall X, In X Xs -> In X (Extract_TyVar _ _ XNs).
    unfold wf_free_vars_P1; unfold wf_free_vars_Q_P1; intros; subst.
    inversion H1; subst.
    unfold update_Tlist in H.
    apply (H _ _ (refl_equal _) H5 X0 H2).
  Defined.

  Lemma I_wf_free_vars : forall (gamma : Context) i int te IT_i wf_int,
    wf_free_vars_Q'' gamma (Interface_ie int) te wf_int ->
    wf_free_vars_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold wf_free_vars_P; unfold Generic.wf_free_vars_P; intros.
    eapply H; eauto.
    apply I_Free_Vars_invert in H1; inversion H1; subst; apply I_Ty_Wrap_inject in H3;
      injection H3; intros; subst; assumption.
  Qed.

  Definition exists_Free_Vars_P := exists_Free_Vars_P _ _ Free_Vars.

  Definition exists_Free_Vars_Q := exists_Free_Vars_Q _ _ TE_Free_Vars.

  Lemma I_exists_Free_Vars : forall te i, exists_Free_Vars_Q te -> 
    exists_Free_Vars_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold exists_Free_Vars_P; unfold Generic.exists_Free_Vars_P;
      unfold exists_Free_Vars_Q; unfold Generic.exists_Free_Vars_Q; intros.
    destruct H as [Xs FV_Xs]; exists Xs; apply I_Free_Vars_Wrap; constructor; auto.
  Qed.

  Variables
    (fields : Context -> Ty -> list (cFJ.FD F Ty) -> Prop)
    (E_WF : Context -> E -> Ty -> Prop)
    (N_trans : N -> list TX -> list Ty -> N)
    (Ty_rename : Ty -> TX -> Ty)
    (TE_rename : ty_ext -> TX -> ty_ext)
    (NTy_rename : N -> TX -> N)
    (Ty_rename_eq_NTy_rename : forall n X, Ty_rename (N_Wrap n) X = NTy_rename n X)
    (subst_context : Context -> list TX -> list Ty -> Context)
    (subst_context_Empty : forall Xs Us, subst_context Empty Xs Us = Empty)
    (app_context_Empty : forall gamma, app_context gamma Empty = gamma)
    (Finite_Context : forall gamma, exists n, forall X ty ty' Ys, TLookup gamma X ty ->
      Free_Vars (Ty_rename ty' n) Ys -> ~ In X Ys)
    (cld_def_ext : Set)
    (L_build_context : cld_ext -> Context -> Prop)
    (override : Context -> M -> cFJ.FJ_Ty C ty_ext -> md_ext -> list Ty -> Ty -> Prop)
    (L_WF_Ext : Context -> cld_ext -> C -> Prop)
    (Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop)
    (Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop).

  Definition L_WF :=
    cFJ.L_WF _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT _ subtype
    WF_Type fields E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext
    override L_WF_Ext L_build_context.

  Definition Type_Subst_Sub_2_5_P := 
    Type_Subst_Sub_2_5_P _ Ty N N_Wrap Context TLookup
    subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.

  Definition Type_Subst_Sub_2_5_TE_P 
    (isub_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) ce te te' te'' :=
    isub_build_te ce te te' te'' ->
    forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
      (Us : list Ty) (XNs : TyP_List) int, 
      (L_build_context ce gamma') ->
      wf_int_ext gamma' int te' ->
      length Xs = length Us ->
      zip Xs Ns (fun x : TX => pair (TyVar _ x)) = Some XNs ->
      List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (N_trans N Xs Us)) ->
      List_P1 (WF_Type delta_1) Us ->
      isub_build_te ce (TE_trans te Xs Us) te' (TE_trans te'' Xs Us).

  Variable (Type_Subst_Sub_2_5_TE : forall ce te te' te'', 
    Type_Subst_Sub_2_5_TE_P isub_build_te ce te te' te'')
  (WF_CT : forall (c : C) cld, CT c = Some cld -> L_WF cld)
  (I_WF_Type_invert : forall gamma ity, WF_Type gamma (I_Ty_Wrap ity) -> 
    I_WF_Type gamma ity)
  (L_build_context' : cld_def_ext -> Context -> Prop)
  (exists_Free_Vars : forall ty, exists_Free_Vars_P ty)
  (map_Ty_trans' : forall ty, map_Ty_trans_P' ty)
  (map_Ty_trans : forall ty, map_Ty_trans_P ty)
  (wf_free_vars : forall gamma ty wf_ty, wf_free_vars_P gamma ty wf_ty)
  (L_build_context'_Empty_1 : forall ce gamma XNs T, L_build_context' ce gamma -> 
    WF_Type (update_Tlist gamma XNs) T -> WF_Type (update_Tlist Empty XNs) T)
  (L_build_context'_Empty_2 : forall ce gamma XNs S T, L_build_context' ce gamma -> 
    subtype (update_Tlist gamma XNs) S T -> subtype (update_Tlist Empty XNs) S T)
  (L_WF_GI_L_WF_Ext : forall gamma ce c ty fs k' ms, 
    L_build_context ce gamma -> 
    L_WF (cld ty_ext Ty X M C F E md_ext cld_ext ce c ty fs k' ms) ->
    GI_L_WF_Ext Empty gamma ce).
    
  Lemma GJ_L_WF_WF_Int :
    forall gamma ce c ty fs k' ms ity, 
      L_build_context ce gamma -> 
      L_WF (cld ty_ext Ty X M C F E md_ext cld_ext ce c ty fs k' ms) ->
      In ity (implements ce) -> WF_Type gamma (I_Ty_Wrap ity).
    intros; generalize (L_WF_GI_L_WF_Ext _ _ _ _ _ _ _ H H0); intros H3;
    apply H3; eauto.
  Qed.

  Definition GJ_TE_trans := GJ_TE_Trans _ _ Ty_trans ty_def_ext.

  Lemma GJ_Type_Subst_Sub_2_5_TE {build_te'} :
    forall ce te te' te'',
      @GJ_build_te _ _ _ Ty_trans cld_def_ext ty_def_ext build_te' ce te te' te'' ->
      forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
        (Us : list Ty) (XNs : TyP_List) ce',
        (Generic.L_build_context _ _ _ TUpdate L_build_context' ce gamma') ->
        @I_wf_int_ext int_def_ext ty_def_ext gamma' ce' te' ->
        length Xs = length Us ->
        zip Xs Ns (fun x : TX => pair (TyVar _ x)) = Some XNs ->
        List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (N_trans N Xs Us)) ->
        List_P1 (WF_Type delta_1) Us ->
        @GJ_build_te _ _ _ Ty_trans cld_def_ext ty_def_ext build_te' 
        ce (GJ_TE_trans te Xs Us) te' (GJ_TE_trans te'' Xs Us).
    intros; inversion H; subst.
    unfold GJ_TE_trans; simpl.
    unfold Tys_Trans.
    assert (map (fun ty : Ty => Ty_trans ty Xs Us)
      (map (fun ty' : Ty => Ty_trans ty' (Extract_TyVar _ _ typs) tys) tys') =
      map (fun ty : Ty => Ty_trans ty (Extract_TyVar _ _ typs)
      (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys)) tys').
    inversion H1; subst; rename H10 into WF_tys; clear H13 H14 H1 H.
    induction tys'; simpl; auto.
    inversion WF_tys; subst.
    destruct (exists_Free_Vars a).
    inversion H0; subst.
    erewrite (map_Ty_trans'); eauto.
    rewrite IHtys'; auto.
    eapply wf_free_vars.
    eapply L_build_context'_Empty_1; eauto.
    reflexivity.
    assumption.
    unfold GJ_TE_Trans; simpl; rewrite H8.
    econstructor; auto.
    generalize typs H7; clear; induction tys; simpl; intros; auto;
      destruct typs; simpl in H7; first [discriminate | injection H7; intros; subst];
        simpl; rewrite IHtys; auto.
  Qed.

  Lemma I_Type_Subst_Sub_2_5 : forall delta S T (sub_S_T : I_subtype delta S T),
    Type_Subst_Sub_2_5_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Type_Subst_Sub_2_5_P; unfold Generic.Type_Subst_Sub_2_5_P; intros.
    inversion sub_S_T; subst.
    generalize (WF_CT _ _ H5); intros; inversion H1; subst.
    generalize (I_WF_Type_invert _ _ (GJ_L_WF_WF_Int _ _ _ _ _ _ _ _ H14 H1 H7)); intros WF_Ity.
    inversion WF_Ity; subst.
    apply I_Ty_Wrap_inject in H8; injection H8; intros; subst.
    rewrite I_Ty_trans_invert; rewrite FJ_Ty_trans_invert; simpl.
    apply I_subtype_Wrap; econstructor; try eassumption.
    eapply Type_Subst_Sub_2_5_TE; try eassumption.
  Qed.

  Variable (Type_Subst_Sub_2_5 : forall delta S T sub_S_T, Type_Subst_Sub_2_5_P delta S T sub_S_T).

  Lemma Type_Subst_Sub_2_5_P2 : forall gamma Ss Ts (sub_S_Ts : List_P2' (subtype gamma) Ss Ts) 
    (delta_1 delta_2 : Context) (Xs : list _)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us -> 
    zip Xs Ns (fun x => @pair _ _ (TyVar _ x)) = Some XNs ->
    gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (N_trans N Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
      ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
    List_P2' (subtype (app_context delta_1 (subst_context delta_2 Xs Us)))
    (map (fun S => Ty_trans S Xs Us) Ss) (map (fun T => Ty_trans T Xs Us) Ts).
    induction Ss; intros; inversion sub_S_Ts; subst; simpl; constructor.
    eapply Type_Subst_Sub_2_5; try eassumption.
    reflexivity.
    eapply IHSs; eauto.
  Qed.

  Definition Ty_trans_trans_subst_P := Ty_trans_trans_subst_P _ _ Ty_trans Free_Vars.
  Definition Ty_trans_trans_subst_Q := Ty_trans_trans_subst_Q _ _ _ Ty_trans TE_Free_Vars TE_trans.

  Lemma I_Ty_trans_trans_subst : forall te i, Ty_trans_trans_subst_Q te -> Ty_trans_trans_subst_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_trans_trans_subst_Q; unfold Ty_trans_trans_subst_P; unfold Generic.Ty_trans_trans_subst_Q; 
      unfold Generic.Ty_trans_trans_subst_P; intros.
    repeat (rewrite I_Ty_trans_invert; simpl).
    apply I_Free_Vars_invert in H1; inversion H1. 
    apply I_Ty_Wrap_inject in H3; injection H3; intros; subst; clear H3.
    erewrite H; eauto.
  Qed.

 Definition Type_Subst_WF_2_6_P := Generic.Type_Subst_WF_2_6_P _ _ _ N_Wrap
    _ TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.

  Definition Type_Subst_WF_2_6_P1 := Type_Subst_WF_2_6_P1 _ _ _  N_Wrap _ 
    TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.
  
  Variable (int_typs : Interface_ext -> TyP_List)
    (Ty_trans_trans_subst : forall ty, Ty_trans_trans_subst_P ty)
    (wf_class_ext : Context -> cld_ext -> ty_ext -> Prop)
    (wf_object_ext : Context -> ty_ext -> Prop).
  
  Definition Type_Subst_WF_2_6_Q'' gamma int te (_ : wf_int_ext gamma int te) :=
    forall (delta_1 delta_2 : Context) (Xs : list TX)
      (Ns : list N) (Us : list Ty) (XNs : TyP_List) Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (int_typs int) Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ (int_typs int))),
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar _ x)) = Some XNs ->
      gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
      List_P2 Us Ns (fun U N => subtype delta_1 U (N_trans N Xs Us)) -> 
      List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
        ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
      wf_int_ext (app_context delta_1 (subst_context delta_2 Xs Us)) int
      (TE_trans te Xs Us).

  Lemma I_Type_Subst_WF_2_6_ext : forall (ie : int_def_ext) gamma (typs : TyP_List) tys 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Type_Subst_WF_2_6_P1 gamma tys P1-> 
    forall (delta_1 delta_2 : Context) (Xs : list TX)
      (Ns : list N) (Us : list Ty) (XNs : TyP_List) Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (typs) Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ typs)),
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar _ x)) = Some XNs ->
      gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
      List_P2 Us Ns (fun U N => subtype delta_1 U (N_trans N Xs Us)) -> 
      List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
        ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
      I_wf_int_ext (app_context delta_1 (subst_context delta_2 Xs Us)) (typs, ie)
      (GJ_TE_trans (tys, te) Xs Us).
    intros; subst.
    constructor; auto.
    eapply H; eauto.
    rewrite len_map; simpl; assumption.
    simpl; apply P2'_if_P2.
    apply P2_if_P2' in P2; generalize (Type_Subst_Sub_2_5_P2 _ _ _ P2
      _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5) as H'.
    generalize Ty_trans_trans_subst FV_typs Bound_Ys len; clear.
    intros Ty_trans_trans_subst; assert (forall typs' tys Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ N typs')),
      length (Extract_TyVar _ N typs') = length tys ->
      map (fun T : Ty => Ty_trans T Xs Us)
      (map
        (fun typ' : GTy * N =>
          Ty_trans (snd typ') (Extract_TyVar _ N typs') tys) typs) = 
      map
      (fun typ' : GTy * N =>
        Ty_trans (snd typ') (Extract_TyVar _ N typs')
        (map (fun ty : Ty => Ty_trans ty Xs Us) tys)) typs).
    generalize Ty_trans_trans_subst; clear; induction typs; simpl; intros; auto.
    destruct a; simpl.
    inversion FV_typs; subst; erewrite IHtyps; eauto.
    assert (forall Y : TX, In Y b -> In Y (Extract_TyVar _ _ typs')).
    intros; apply Bound_Ys; simpl; apply in_or_app; left; assumption.
    erewrite Ty_trans_trans_subst; eauto.
    intros; eapply Bound_Ys; apply in_or_app; right; assumption.
    intros; erewrite H in H'; eauto.
    generalize tys len; clear; induction typs; simpl; intros; auto.
    destruct tys; try discriminate; simpl in *|-*; injection len; intros.
    erewrite IHtyps; eauto.
  Defined.    
    
  Definition I_Ty_rename ty (Y : TX) : Ty :=
    match ty with 
      |  ity_def te c => I_Ty_Wrap (ity_def _ _ (TE_rename te Y) c)
    end.

  Definition FJ_Ty_rename := FJ_Ty_rename _ _ _ _ N N_Wrap FJ_N_Wrap TE_rename.

  Definition FJ_WF_Type := cFJ.FJ_WF_Type _ _ _ _ _ _ FJ_Ty_Wrap _ _ _
    CT Context wf_class_ext wf_object_ext.

  Variables (rename_X : TX -> TX -> TX)
    (rename_X_inject : forall X Y n, rename_X X n = rename_X Y n -> X = Y)          
    (rename_context : Context -> TX -> Context)
    (TLookup_rename_context : forall gamma x ty Y, 
      TLookup gamma x ty -> TLookup (rename_context gamma Y) (rename_X x Y) (NTy_rename ty Y))
    (TLookup_rename_context' : forall gamma x ty n, 
      TLookup (rename_context gamma n) x ty -> exists x', exists ty', x = rename_X x' n /\ 
        ty = NTy_rename ty' n /\ TLookup gamma x' ty')
    (rename_X_eq : forall Y Y' X', rename_X Y X' = rename_X Y' X' -> Y = Y')
    (I_Ty_rename_invert : forall (ty : _) Y, Ty_rename (I_Ty_Wrap ty) Y = I_Ty_rename ty Y)
    (FJ_Ty_rename_invert : forall (ty : _) Y, Ty_rename (FJ_Ty_Wrap ty) Y = FJ_Ty_rename ty Y)
    (FJ_WF_Type_Wrap_invert : forall delta S, WF_Type delta (FJ_Ty_Wrap S) -> 
      FJ_WF_Type delta (FJ_Ty_Wrap S)).

  Definition Ty_rename_Ty_trans_P := Ty_rename_Ty_trans_P _ _ Ty_trans rename_X Ty_rename.
  Definition Ty_rename_Ty_trans_Q := Ty_rename_Ty_trans_Q _ _ _ TE_trans rename_X Ty_rename TE_rename.

  Lemma I_Ty_rename_Ty_trans : forall te i, Ty_rename_Ty_trans_Q te -> 
    Ty_rename_Ty_trans_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_Ty_trans_Q; unfold Ty_rename_Ty_trans_P; unfold Generic.Ty_rename_Ty_trans_Q; 
      unfold Generic.Ty_rename_Ty_trans_P; intros.
    repeat (rewrite I_Ty_trans_invert; rewrite I_Ty_rename_invert; simpl).
    erewrite H; eauto.
  Qed.
  
  Definition FV_subst_tot_P := FV_subst_tot_P _ _ Ty_trans Free_Vars.
  Definition FV_subst_tot_Q := FV_subst_tot_Q _ _ _ Free_Vars TE_Free_Vars TE_trans.

  Lemma I_FV_subst_tot : forall te i, FV_subst_tot_Q te -> 
    FV_subst_tot_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold FV_subst_tot_Q; unfold FV_subst_tot_P; unfold Generic.FV_subst_tot_P; 
      unfold Generic.FV_subst_tot_Q; intros.
    apply I_Free_Vars_invert in H2; inversion H2; subst;
      apply I_Ty_Wrap_inject in H4; injection H4; intros; subst; clear H4.
    destruct (H _ _ _ _ H0 H1 H5 H3) as [Ys' [FV_te Bound_Ys']].
    exists Ys'; split; auto.
    repeat (rewrite I_Ty_trans_invert; simpl).
    apply I_Free_Vars_Wrap; constructor; auto.
  Qed.

  Definition Ty_rename_eq_Ty_trans_P := Ty_rename_eq_Ty_trans_P _ _ Ty_Wrap Ty_trans Free_Vars rename_X Ty_rename.
  Definition Ty_rename_eq_Ty_trans_Q := 
    Ty_rename_eq_Ty_trans_Q _ _ _ Ty_Wrap TE_Free_Vars TE_trans rename_X TE_rename.

  Lemma I_Ty_rename_eq_Ty_trans : forall te i, Ty_rename_eq_Ty_trans_Q te -> 
    Ty_rename_eq_Ty_trans_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_eq_Ty_trans_Q; unfold Ty_rename_eq_Ty_trans_P; unfold Generic.Ty_rename_eq_Ty_trans_P; 
      unfold Generic.Ty_rename_eq_Ty_trans_Q; intros.
    repeat (rewrite I_Ty_trans_invert; rewrite I_Ty_rename_invert; simpl).
    apply I_Free_Vars_invert in H0; inversion H0; subst;
      apply I_Ty_Wrap_inject in H2; injection H2; intros; subst; clear H2.
    rewrite (H _ _ _ H3 H1); reflexivity.
  Qed.

  Definition Ty_rename_subtype_P := Ty_rename_subtype_P _ _ _ subtype Ty_rename rename_context.

  Variables (Int_build_context : Interface_ext -> Context -> Prop)
    (Int_WF_Ext : Context -> Interface_ext -> I -> Prop)
    (Int_Meth_WF_Ext : Context -> Interface_ext -> mty_ext -> Prop)
    (Int_Meth_build_context : Interface_ext -> mty_ext -> Context -> Context -> Prop).

  Definition I_WF := I_WF I Ty mty_ext X M _ _ WF_Type Int_build_context
    Int_WF_Ext Int_Meth_WF_Ext Int_Meth_build_context.

  Variable (rename_isub_build_te : 
    forall gamma ce ie c te te'' te' n, 
      L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
      wf_int_ext gamma ie te' ->
      isub_build_te ce te te' te'' ->
      isub_build_te ce (TE_rename te n) te' (TE_rename te'' n))
  (Ty_rename_eq_Ty_trans : forall ty, Ty_rename_eq_Ty_trans_P ty)
  (FV_subst_tot : forall ty, FV_subst_tot_P ty)
  (cld_typs : cld_ext -> Generic.TyP_List TX N)
  (Free_Vars_id : forall ty Us Us', Free_Vars ty Us -> Free_Vars ty Us' -> Us = Us')
  (Ty_rename_subtype : forall delta S T sub_S_T, Ty_rename_subtype_P delta S T sub_S_T)
  (WF_IT : forall i int, IT i = Some int -> I_WF int).
  
  Definition exists_Free_Vars_P2 := exists_Free_Vars_P2 _ _ Free_Vars exists_Free_Vars.

  Definition GJ_L_WF_bound := GJ_L_WF_bound _ _ C _ N_Wrap _ Empty WF_Type TUpdate _
    Free_Vars exists_Free_Vars wf_free_vars L_build_context' L_build_context'_Empty_1.

  Lemma I_rename_isub_build_te {build_te' L_WF_Ext'} :
    forall gamma ce ie (c : C) te te'' te' n, 
      Generic.L_build_context _ _ _ TUpdate L_build_context' ce gamma ->
      Generic.L_WF_Ext _ _ _ N N_Wrap _ WF_Type L_WF_Ext' gamma ce c ->
      @I_wf_int_ext int_def_ext ty_def_ext gamma ie te' ->
      @GJ_build_te _ _ _ Ty_trans cld_def_ext ty_def_ext build_te' ce te te' te'' ->
      @GJ_build_te _ _ _ Ty_trans cld_def_ext ty_def_ext build_te' ce 
      (GJ_TE_rename _ _ _ Ty_rename te n) te' (GJ_TE_rename _ _ _ Ty_rename te'' n).
    intros; inversion H2; subst.
    unfold GJ_TE_rename.
    destruct (exists_Free_Vars_P2 tys') as [Vs FV_tys'].
    destruct (GJ_L_WF_bound L_WF_Ext' _ _ _ H H0) as [Ys' [FV_tys In_Ys_tys]].
    erewrite Ty_rename_Ty_trans_tot; eauto.
    econstructor; auto.
    rewrite len_map; assumption.
    intros; inversion H1; subst.
    simpl in FV_tys.
    assert (exists n', exists Vs', nth_error Vs n' = Some Vs' /\ In V Vs').
    generalize Vs H5; clear; induction Vs; simpl; intros; try contradiction.
    apply in_app_or in H5; destruct H5; subst.
    exists 0; exists a; simpl; split; auto.
    destruct (IHVs H) as [n' [Vs' [nth_Vs' In_V]]]; exists (S n'); exists Vs'; split; auto.
    destruct H6 as [n' [Vs' [nth_Vs' In_V]]].
    apply P2'_if_P2 in FV_tys'; destruct FV_tys'.
    caseEq (nth_error tys' n').
    destruct (H6 _ _ H9) as [Vs'' [nth_Vs'' FV_t]].
    rewrite nth_Vs'' in nth_Vs'; injection nth_Vs'; intros; subst.
    assert (WF_Type gamma t).
    generalize tys' H8 H9; clear; induction n'; destruct tys'; simpl; intros;
      try discriminate.
    injection H9; intros; subst.
    inversion H8; auto.
    inversion H8; eauto.
    inversion H; subst.
    apply (L_build_context'_Empty_1 _ _ _ _ H16) in H10.
    generalize (wf_free_vars _ _ H10 _ _ (refl_equal _) FV_t).
    intros.
    apply H13.
    assumption.
    rewrite (H7 _ H9) in nth_Vs'; discriminate.
  Qed.    

  Lemma I_Ty_rename_subtype : forall delta S T (sub_S_T : I_subtype delta S T),
    Ty_rename_subtype_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Ty_rename_subtype_P; unfold Generic.Ty_rename_subtype_P; intros.
    inversion sub_S_T; subst.
    rewrite I_Ty_rename_invert; rewrite FJ_Ty_rename_invert; simpl; apply I_subtype_Wrap;
      econstructor; eauto.
    apply WF_CT in H; inversion H; subst.
    generalize (GJ_L_WF_WF_Int _ _ _ _ _ _ _ _ H8 H H1); intros WF_i.
    apply I_WF_Type_invert in WF_i; inversion WF_i; subst;
      apply I_Ty_Wrap_inject in H2; injection H2; intros; subst.
    eapply rename_isub_build_te; eauto.
  Qed.

  Definition Free_Vars_id_P := Free_Vars_id_P _ _ Free_Vars.
  Definition Free_Vars_id_Q := Free_Vars_id_Q _ _ TE_Free_Vars.

  Lemma I_Free_Vars_id : forall te i, Free_Vars_id_Q te -> Free_Vars_id_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Free_Vars_id_Q; unfold Free_Vars_id_P; unfold Generic.Free_Vars_id_Q; 
      unfold Generic.Free_Vars_id_P; intros.
    apply I_Free_Vars_invert in H0; apply I_Free_Vars_invert in H1; 
      inversion H0; inversion H1; subst; apply I_Ty_Wrap_inject in H2;
        apply I_Ty_Wrap_inject in H5; injection H2; injection H5; intros; subst; eauto.
  Qed.

  Definition Ty_rename_WF_Type_P := Ty_rename_WF_Type_P _ _ _ WF_Type Ty_rename rename_context.
  Definition Ty_rename_WF_Type_P1 :=  Ty_rename_WF_Type_P1 _ _ _ WF_Type Ty_rename rename_context.

  Definition Ty_rename_WF_Type_Q'' gamma int te (WF_te : wf_int_ext gamma int te) :=
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (int_typs int) Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ (int_typs int)))
    n, wf_int_ext (rename_context gamma n) int (TE_rename te n).

  Definition Ty_rename_Ty_trans_tot' := Ty_rename_Ty_trans_tot' _ _ Ty_Wrap Ty_trans
    Free_Vars exists_Free_Vars Ty_trans_trans_subst rename_X
    Ty_rename Ty_rename_eq_Ty_trans FV_subst_tot.

  Variable (Int_WF_bound : forall int, I_WF int -> exists Ys,
      List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (int_typs (Interface_ie int)) Ys /\
      forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ (int_typs (Interface_ie int)))).

  Lemma I_Ty_rename_WF_Type_ext : forall (ie : int_def_ext) 
    gamma (typs : TyP_List) tys (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Ty_rename_WF_Type_P1 gamma tys P1-> 
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ typs))
    n, I_wf_int_ext (rename_context gamma n) (typs, ie) (GJ_TE_rename _ _ _ Ty_rename (tys, te) n).
    intros; constructor.
    eapply H.
    rewrite len_map; assumption.
    destruct P2; split; intros.
    caseEq (nth_error tys n0).
    generalize (nth_error_map _ _ (fun ty : Ty => Ty_rename ty n) _ _ _ H3); intros H3';
      rewrite H3' in H2; injection H2; intros; subst; clear H2.
    destruct (H0 _ _ H3) as [ty' [nth_ty' sub_t_ty']].
    caseEq (nth_error typs n0).
    generalize (nth_error_map _ _ (fun typ' : Generic.GTy TX * N =>
      Ty_trans (snd typ') (Extract_TyVar _ _ typs) tys) _ _ _ H2); intros nth_ty'';
    rewrite nth_ty'' in nth_ty'; injection nth_ty'; intros; subst; clear nth_ty'.
    exists (Ty_rename (Ty_trans (snd p) (Extract_TyVar _ _ typs) tys) n); split.
    rewrite (nth_error_map _ _ (fun typ' : GTy * N =>
      Ty_trans (snd typ') (Extract_TyVar _ _ typs)
      (map (fun ty : Ty => Ty_rename ty n) tys)) _ _ _ H2).
    destruct (exists_Free_Vars (snd p)) as [Vs FV_p].
    erewrite Ty_rename_Ty_trans_tot'; eauto.
    generalize tys len; clear; induction typs; destruct tys; simpl; intros; 
      try discriminate; auto.
    intros; eapply Bound_Ys.
    apply P2'_if_P2 in FV_typs; destruct FV_typs.
    destruct (H5 _ _ H2) as [B [nth_Ys FV_B]].
    rewrite <- (Free_Vars_id _ _ _ FV_p FV_B) in nth_Ys.
    generalize Vs Ys H4 nth_Ys; clear; induction n0; destruct Ys; simpl; intros;
      try discriminate.
    injection nth_Ys; intros; subst; apply in_or_app; left; auto.
    simpl; apply in_or_app; right; eauto.
    eapply Ty_rename_subtype; assumption.
    elimtype False; generalize tys typs len H3 H2; clear; induction n0; 
      destruct tys; destruct typs; simpl; intros; try discriminate.
    injection len; intros; eauto.
    rewrite (nth_error_map' _ _ _ _ _ H3) in H2; discriminate.
    caseEq (nth_error tys n0).
    rewrite (nth_error_map _ _  (fun ty : Ty => Ty_rename ty n) _ _ _ H3) in H2; discriminate.
    generalize (H1 _ H3); clear; intros.
    caseEq (nth_error typs n0).
    rewrite (nth_error_map _ _  _ _ _ _ H0) in H; discriminate.
    rewrite (nth_error_map' _ _ _ _ _ H0); reflexivity.
  Qed.

  Variables (I_WF_Ext' : Context -> int_def_ext -> I -> Prop)
    (Int_build_context' : int_def_ext -> Context -> Prop)
    (Int_build_context'_Empty_1 : forall ce gamma XNs T, Int_build_context' ce gamma -> 
      WF_Type (update_Tlist gamma XNs) T -> WF_Type (update_Tlist Empty XNs) T)
    (Int_build_context'_Empty_2 : forall ce gamma XNs S T, Int_build_context' ce gamma -> 
      subtype (update_Tlist gamma XNs) S T -> subtype (update_Tlist Empty XNs) S T).

  Lemma GI_I_WF_bound 
    : forall (ie : @GInterface_ext int_def_ext) gamma c,
    GI_Int_build_context Int_build_context' ie gamma -> 
    GI_Int_WF_Ext I_WF_Ext' gamma ie c -> 
    exists Ys,
      List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (fst ie) Ys /\
      forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ (fst ie)).
    intros; inversion H; inversion H0; subst; injection H7; intros; subst.
    assert (List_P1  (fun typ : GTy * N => WF_Type (update_Tlist Empty XNs) (snd typ)) XNs) as H5' by
      (assert (exists XNs', XNs' = XNs) as eq_XNs' by (eexists _; reflexivity);
        destruct eq_XNs' as [XNs' eq_XNs'];
          revert H5; rewrite <- eq_XNs' at 1; rewrite <- eq_XNs' at 1;
            generalize XNs (fun T => Int_build_context'_Empty_1 _ _ XNs T H1); clear;
              induction XNs'; intros; inversion H0; subst; constructor; eauto); clear H5.
    assert (forall XN, In XN XNs -> 
      forall Xs, Free_Vars (snd XN) Xs -> 
        forall X, In X Xs -> In X (Extract_TyVar _ _ XNs)) as wf_free_vars' by
    (intros;
      assert (forall gamma, In XN XNs -> List_P1 (fun typ : GTy * N => WF_Type gamma (snd typ)) XNs
        -> WF_Type gamma (snd XN)) by (clear; induction XNs; simpl; intros; try contradiction;
          inversion H0; destruct H; subst; auto);
        intros; eapply wf_free_vars; try apply (H6 _ H2 H5'); eauto).
    simpl.
    assert (exists Ys : list (list TX),
     List_P2' (fun typ : GTy * N => Free_Vars (snd typ)) XNs Ys) as ex_Ys by
    (generalize exists_Free_Vars; clear; induction XNs; intros;
      first [exists nil; constructor | 
        destruct a; destruct (exists_Free_Vars n); destruct (IHXNs exists_Free_Vars);
          eexists (_ :: _); constructor; simpl; eauto]); destruct ex_Ys as [Ys FV_Ys];
    exists Ys; split; auto.
    assert (List_P2 Ys XNs (fun Y typ => Free_Vars (snd typ) Y)).
    apply P2'_if_P2 in FV_Ys; generalize FV_Ys; clear; intros; destruct FV_Ys; split;
      intros; caseEq (nth_error XNs n).
    destruct (H _ _ H2) as [b' [nth' FV_b]].
    exists p; split; try congruence. 
    rewrite H1 in nth'; injection nth'; intros; subst; assumption.
    rewrite (H0 _ H2) in H1; discriminate.
    destruct (H _ _ H2) as [b' [nth' FV_b]]; rewrite nth' in H1; discriminate.
    reflexivity.
    destruct H2.
    intros.
    assert (exists Ys', In Ys' Ys /\ In Y Ys') as ex_Ys' by 
      (generalize H5; clear; induction Ys; simpl; intros; try contradiction;
        apply in_app_or in H5; destruct H5; try (exists a; split; tauto);
          destruct (IHYs H) as [Ys' [InYs' InY]]; exists Ys'; tauto).
    destruct ex_Ys' as [Ys' [In_Ys' In_Y]].
    destruct (nth_error_in' _ _ _ In_Ys') as [n nth_Ys].
    destruct (H2 _ _ nth_Ys) as [b [nth_b FV_b]].
    eapply wf_free_vars'.
    eapply nth_error_in; eauto.
    eapply FV_b.
    assumption.
  Qed.

  Lemma I_Ty_rename_WF_Type : forall (gamma : Context) i int te IT_i wf_int,
    Ty_rename_WF_Type_Q'' gamma (Interface_ie int) te wf_int ->
    Ty_rename_WF_Type_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold Ty_rename_WF_Type_Q''; unfold Ty_rename_WF_Type_P; unfold Generic.Ty_rename_WF_Type_P;
      intros.
    rewrite I_Ty_rename_invert; simpl; apply I_WF_Type_Wrap; econstructor; try eassumption.
    generalize (WF_IT _ _ IT_i); intros H2; inversion H2; subst.
    destruct (Int_WF_bound _ H2) as [Ys [FV_Ys Bound_Ys]].
    eapply (H Ys); eauto.
  Qed.

  Definition subtype_context_shuffle_P := subtype_context_shuffle_P _ _ _ _ TLookup subtype app_context.

  Lemma I_subtype_context_shuffle : forall delta S T (sub_S_T : I_subtype delta S T),
    subtype_context_shuffle_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold subtype_context_shuffle_P; unfold Generic.subtype_context_shuffle_P; intros.
    inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; try eassumption.
  Qed.

  Definition WF_context_shuffle_P := WF_context_shuffle_P _ _ _ _ TLookup WF_Type app_context.
  Definition WF_context_shuffle_P1 := WF_context_shuffle_P1 _ _ _ _ TLookup WF_Type app_context.

  Definition WF_context_shuffle_Q'' gamma int te (WF_te : wf_int_ext gamma int te) :=
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      wf_int_ext (app_context delta_2 delta_1) int te.

  Variable (subtype_context_shuffle : forall delta S T sub_S_T, subtype_context_shuffle_P delta S T sub_S_T).

  Lemma I_WF_context_shuffle_ext : forall (ie : int_def_ext) 
    gamma (typs : TyP_List) tys (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    WF_context_shuffle_P1 gamma tys P1-> 
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      I_wf_int_ext (app_context delta_2 delta_1) (typs, ie) (tys, te).
    unfold WF_context_shuffle_P1; unfold Generic.WF_context_shuffle_P1; intros; subst.
    econstructor; eauto.
    destruct P2; split; intros.
    destruct (H0 _ _ H3) as [b [nth_b sub_a_b]].
    exists b; split; eauto.
    eapply subtype_context_shuffle; try eapply sub_a_b; eauto.
    apply (H2 _ H3).
  Qed.
  
  Lemma I_WF_context_shuffle : forall (gamma : Context) i int te IT_i wf_int,
    WF_context_shuffle_Q'' gamma (Interface_ie int) te wf_int ->
    WF_context_shuffle_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold WF_context_shuffle_P; unfold Generic.WF_context_shuffle_P; intros; subst.
    apply I_WF_Type_Wrap; econstructor; try eassumption.
    eapply H; eauto.
  Qed.

  Lemma I_Type_Subst_WF_2_6 : forall (gamma : Context) i int te IT_i wf_int,
    Type_Subst_WF_2_6_Q'' gamma (Interface_ie int) te wf_int ->
    Type_Subst_WF_2_6_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold Type_Subst_WF_2_6_P; unfold Generic.Type_Subst_WF_2_6_P; intros.
    apply I_WF_Type_Wrap; rewrite I_Ty_trans_invert; simpl;
      econstructor; eauto.
    generalize (WF_IT _ _ IT_i); intros H2'; inversion H2'; subst.
    destruct (Int_WF_bound _ H2') as [Ys [FV_Ys Bound_Ys]].
    eapply H; eauto.
  Qed.

  Definition Ty_rename_FJ_Ty_Wrap_eq_P := Ty_rename_FJ_Ty_Wrap_eq_P _ _ _ _ _ N_Wrap FJ_N_Wrap Ty_rename TE_rename.

  Variables (Ty_Wrap_discriminate : forall ty ty', Ty_Wrap ty <> I_Ty_Wrap ty')
    (Ty_Wrap_discriminate' : forall ty ty', FJ_Ty_Wrap ty <> I_Ty_Wrap ty').

  Lemma I_Ty_rename_FJ_Ty_Wrap_eq : forall te i, Ty_rename_FJ_Ty_Wrap_eq_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_FJ_Ty_Wrap_eq_P; unfold Generic.Ty_rename_FJ_Ty_Wrap_eq_P; intros.
    rewrite I_Ty_rename_invert in H; cbv in H.
    destruct (Ty_Wrap_discriminate' _ _ H).
  Qed.

  Definition Ty_rename_GJ_Ty_Wrap_eq_P := Ty_rename_GJ_Ty_Wrap_eq_P _ _ Ty_Wrap Ty_rename.

  Lemma I_Ty_rename_GJ_Ty_Wrap_eq : forall te i, Ty_rename_GJ_Ty_Wrap_eq_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_GJ_Ty_Wrap_eq_P; unfold Generic.Ty_rename_GJ_Ty_Wrap_eq_P; intros.
    rewrite I_Ty_rename_invert in H; cbv in H.
    destruct (Ty_Wrap_discriminate _ _ H).
  Qed.

  Definition Ty_rename_inject_P := Ty_rename_inject_P _ _ Ty_rename.
  Definition Ty_rename_inject_Q := Ty_rename_inject_Q _ _ TE_rename.

  Definition Ty_rename_I_Ty_Wrap_eq_P T' := forall T n,
    I_Ty_Wrap T = Ty_rename T' n -> 
    exists te, exists i, T' = I_Ty_Wrap (ity_def _ _ te i).

  Lemma I_Ty_rename_I_Ty_Wrap_eq : forall te i, Ty_rename_I_Ty_Wrap_eq_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_I_Ty_Wrap_eq_P; intros; rewrite I_Ty_rename_invert in H; simpl in H.
    eexists _; eexists _; reflexivity.
  Qed.

  Variable (Ty_rename_I_Ty_Wrap_eq : forall ty, Ty_rename_I_Ty_Wrap_eq_P ty)
    (Ty_rename_GJ_Ty_Wrap_eq : forall ty', Ty_rename_GJ_Ty_Wrap_eq_P ty')
    (Ty_rename_FJ_Ty_Wrap_eq : forall ty', Ty_rename_FJ_Ty_Wrap_eq_P ty')
    (GJ_Ty_rename_invert : forall (ty : GTy) Y, Ty_rename ty Y = GJ_Ty_rename _ _ Ty_Wrap rename_X ty Y).

  Lemma FJ_Ty_rename_I_Ty_Wrap_eq : forall ty, Ty_rename_I_Ty_Wrap_eq_P (FJ_Ty_Wrap ty).
    unfold Ty_rename_I_Ty_Wrap_eq_P; intros. 
    rewrite FJ_Ty_rename_invert in H; destruct ty; cbv in H.
    destruct (Ty_Wrap_discriminate' _ _ (sym_eq H)).
  Qed.

  Lemma GJ_Ty_rename_I_Ty_Wrap_eq : forall ty, Ty_rename_I_Ty_Wrap_eq_P (Ty_Wrap ty).
    unfold Ty_rename_I_Ty_Wrap_eq_P; intros. 
    rewrite GJ_Ty_rename_invert in H; destruct ty; cbv in H.
    destruct (Ty_Wrap_discriminate _ _ (sym_eq H)).
  Qed.

  Lemma I_Ty_rename_inject : forall te i, Ty_rename_inject_Q te -> 
    Ty_rename_inject_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Ty_rename_inject_Q; unfold Ty_rename_inject_P; unfold Generic.Ty_rename_inject_Q; 
      unfold Generic.Ty_rename_inject_P; intros.
    rewrite I_Ty_rename_invert in H0; simpl in H0.
    destruct (Ty_rename_I_Ty_Wrap_eq _ _ _ H0) as [te' [i' ty'_eq]]; subst.
    rewrite I_Ty_rename_invert in H0; simpl in H0; apply I_Ty_Wrap_inject in H0.
    injection H0; intros; subst; rewrite (H te' n); auto.
  Qed.

  Definition ex_Ty_rename_subtype_P := ex_Ty_rename_subtype_P_r _ _ _ subtype Ty_rename rename_context.

  Variable (TE_rename_isub_build_te : 
      forall gamma ce c te te' te'' n int,
        L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
        wf_int_ext gamma int te' -> 
        isub_build_te ce (TE_rename te n) te' te'' -> 
        exists te3, te'' = TE_rename te3 n)
  (TE_rename_isub_build_te' : 
    forall gamma ce c te te' te'' n int,
      L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
      wf_int_ext gamma int te' -> 
      isub_build_te ce (TE_rename te n) te' (TE_rename te'' n) -> 
      isub_build_te ce te te' te'')
  (Ty_rename_eq_inject : forall ty ty' n, Ty_rename ty n = Ty_rename ty' n -> ty = ty').

  Lemma I_TE_rename_build_te {build_te' L_WF_Ext'} :
    forall gamma ce ie (c : C) te te'' te' n, 
      Generic.L_build_context _ _ _ TUpdate L_build_context' ce gamma ->
      Generic.L_WF_Ext _ _ _ N N_Wrap _ WF_Type L_WF_Ext' gamma ce c ->
      @I_wf_int_ext int_def_ext ty_def_ext gamma ie te' ->
      @GJ_build_te _ _ N Ty_trans cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename _ _ _ Ty_rename te n) te' te'' ->
      exists te3, te'' = GJ_TE_rename _ _ _ Ty_rename te3 n.
    intros; inversion H2; subst.
    unfold GJ_TE_rename.
    destruct (exists_Free_Vars_P2 tys') as [Vs FV_tys'].
    destruct (GJ_L_WF_bound _ _ _ _ H H0) as [Ys' [FV_tys In_Ys_tys]].
    destruct te; unfold GJ_TE_rename in H3; injection H3; intros; subst.
    eexists (Tys_Trans _ _ _ _ typs l tys', _); 
      erewrite Ty_rename_Ty_trans_tot; eauto.
    rewrite len_map in H6; assumption.
    inversion H; subst.
    intros; inversion H1; subst.
    simpl in FV_tys.
    assert (exists n', exists Vs', nth_error Vs n' = Some Vs' /\ In V Vs').
    generalize Vs H5; clear; induction Vs; simpl; intros; try contradiction.
    apply in_app_or in H5; destruct H5; subst.
    exists 0; exists a; simpl; split; auto.
    destruct (IHVs H) as [n' [Vs' [nth_Vs' In_V]]]; exists (S n'); exists Vs'; split; auto.
    destruct H7 as [n' [Vs' [nth_Vs' In_V]]].
    apply P2'_if_P2 in FV_tys'; destruct FV_tys'.
    caseEq (nth_error tys' n').
    destruct (H7 _ _ H11) as [Vs'' [nth_Vs'' FV_t]].
    rewrite nth_Vs'' in nth_Vs'; injection nth_Vs'; intros; subst.
    assert (WF_Type (update_Tlist gamma0 typs) t0).
    generalize tys' H10 H11; clear; induction n'; destruct tys'; simpl; intros;
      try discriminate.
    injection H11; intros; subst.
    inversion H10; auto.
    inversion H10; eauto.
    apply (L_build_context'_Empty_1 _ _ _ _ H9) in H12.
    generalize (wf_free_vars _ _ H12 _ _ (refl_equal _) FV_t).
    intros; apply H15; assumption.
    rewrite (H8 _ H11) in nth_Vs'; discriminate.
  Qed.

  Lemma I_TE_rename_build_te' {build_te' L_WF_Ext'} :
    forall gamma ce ie (c : C) te te'' te' n, 
      Generic.L_build_context _ _ _ TUpdate L_build_context' ce gamma ->
      Generic.L_WF_Ext _ _ _ N N_Wrap _ WF_Type L_WF_Ext' gamma ce c ->
      @I_wf_int_ext int_def_ext ty_def_ext gamma ie te' ->
      @GJ_build_te _ _ N Ty_trans cld_def_ext ty_def_ext build_te' 
      ce (GJ_TE_rename _ _ _ Ty_rename te n) te' (GJ_TE_rename _ _ _ Ty_rename te'' n) ->
      @GJ_build_te _ _ N Ty_trans cld_def_ext ty_def_ext build_te' ce te te' te''.
    intros; inversion H2; subst.
    unfold GJ_TE_rename in H2.
    destruct (exists_Free_Vars_P2 tys') as [Vs FV_tys'].
    destruct (GJ_L_WF_bound _ _ _ _ H H0) as [Ys' [FV_tys In_Ys_tys]].
    destruct te; unfold GJ_TE_rename in H3; injection H3; intros; subst.
    destruct te''; unfold GJ_TE_rename in H4. 
    erewrite <- Ty_rename_Ty_trans_tot in H4; injection H4; intros; subst.
    assert (forall tys tys', map (fun ty : Ty => Ty_rename ty n) tys = 
      map (fun ty : Ty => Ty_rename ty n) tys' -> tys = tys').
    generalize Ty_rename_eq_inject; clear; induction tys; simpl; destruct tys';
      simpl; intros; try discriminate; auto; injection H; intros; subst.
    rewrite (Ty_rename_eq_inject _ _ _ H1); rewrite (IHtys _ H0); reflexivity.
    rewrite <- (H5 _ _ H7).
    constructor; auto.
    rewrite len_map in H8; assumption.
    apply exists_Free_Vars.
    apply Ty_trans_trans_subst.
    apply Ty_rename_eq_Ty_trans.
    apply FV_subst_tot.
    apply FV_tys'.
    rewrite len_map in H8; assumption.
    simpl in FV_tys.
    assert (exists n', exists Vs', nth_error Vs n' = Some Vs' /\ In V Vs').
    generalize Vs H9; clear; induction Vs; simpl; intros; try contradiction.
    apply in_app_or in H9; destruct H9; subst.
    exists 0; exists a; simpl; split; auto.
    destruct (IHVs H) as [n' [Vs' [nth_Vs' In_V]]]; exists (S n'); exists Vs'; split; auto.
    destruct H5 as [n' [Vs' [nth_Vs' In_V]]].
    apply P2'_if_P2 in FV_tys'; destruct FV_tys'.
    caseEq (nth_error tys' n').
    destruct (H5 _ _ H11) as [Vs'' [nth_Vs'' FV_t]].
    rewrite nth_Vs'' in nth_Vs'; injection nth_Vs'; intros; subst.
    inversion H1; subst.
    inversion H; subst.
    assert (WF_Type (update_Tlist gamma0 typs) t1).
    generalize tys' H11 H14; clear; induction n'; destruct tys'; simpl; intros;
      try discriminate.
    injection H11; intros; subst.
    inversion H14; auto.
    inversion H14; eauto.
    apply (L_build_context'_Empty_1 _ _ _ _ H16) in H12.
    apply (wf_free_vars _ _ H12 _ _ (refl_equal _) FV_t); assumption.
    rewrite (H10 _ H11) in nth_Vs'; discriminate.
  Qed.

  Lemma I_ex_Ty_rename_subtype : forall delta S T (sub_S_T : I_subtype delta S T),
    ex_Ty_rename_subtype_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold ex_Ty_rename_subtype_P; unfold Generic.ex_Ty_rename_subtype_P_r; intros.
    inversion sub_S_T; subst.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H5) as [te3 [te_eq S'_eq]]; subst.
    apply WF_CT in H1; inversion H1; subst.
    generalize (GJ_L_WF_WF_Int _ _ _ _ _ _ _ _ H9 H1 H3); intros H;
      apply I_WF_Type_invert in H; inversion H; subst.
    apply I_Ty_Wrap_inject in H0; injection H0; intros; subst.
    destruct (TE_rename_isub_build_te _ _ _ _ _ _ _ _ H9 H17 H7 H2) as [te4 te5_eq].
    exists (I_Ty_Wrap (ity_def _ _ te4 i)); rewrite I_Ty_rename_invert;
      simpl; congruence.
  Qed.

  Definition Ty_rename_subtype_P' := Ty_rename_subtype_P' _ _ _ subtype Ty_rename rename_context.

  Lemma I_Ty_rename_subtype' : forall delta S T (sub_S_T : I_subtype delta S T),
    Ty_rename_subtype_P' _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Ty_rename_subtype_P'; unfold Generic.Ty_rename_subtype_P'; intros.
    inversion sub_S_T; subst.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H6) as [te3 [te_eq S'_eq]]; subst.
    destruct (Ty_rename_I_Ty_Wrap_eq _ _ _ H7) as [te4 [eq_te4 eq_T']].
    generalize (WF_CT _ _ H2) as WF_c; intros; inversion WF_c; subst.
    generalize (GJ_L_WF_WF_Int _ _ _ _ _ _ _ _ H10 WF_c H4); intros H1;
      apply I_WF_Type_invert in H1; inversion H1; subst.
    apply I_Ty_Wrap_inject in H; injection H; intros; subst.
    destruct (TE_rename_isub_build_te _ _ _ _ _ _ _ _ H10 H18 H8 H3) as [te5 te5_eq]; subst.
    rewrite I_Ty_rename_invert in H7; simpl in H7; apply I_Ty_Wrap_inject in H7;
      injection H7; intros; subst.
    apply I_subtype_Wrap; econstructor; eauto.
    eapply TE_rename_isub_build_te'; try eassumption.
    rewrite H9 in H3; apply H3.
  Qed.

  Definition Ty_rename_WF_Type'_P := Ty_rename_WF_Type'_P _ _ _ WF_Type Ty_rename rename_context.

  Definition Ty_rename_WF_Type'_Q'' gamma int te (WF_te : wf_int_ext gamma int te) :=
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (int_typs int) Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ (int_typs int)))
    gamma' te' n, gamma = rename_context gamma' n -> te = TE_rename te' n ->
    wf_int_ext gamma' int te'.

  Definition Ty_rename_WF_Type'_P1 := Ty_rename_WF_Type'_P1 _ _ _ WF_Type Ty_rename rename_context.

  Variable (Ty_rename_subtype' : forall delta S T sub_S_T, Ty_rename_subtype_P' delta S T sub_S_T).

  Lemma I_Ty_rename_WF_Type_ext' : forall (ie : int_def_ext) 
    gamma (typs : TyP_List) tys (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Ty_rename_WF_Type'_P1 gamma tys P1-> 
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar _ _ typs))
    gamma' te' n, gamma = rename_context gamma' n -> (tys, te) = (GJ_TE_rename _ _ _ Ty_rename te' n) ->
    I_wf_int_ext gamma' (typs, ie) te'.
    unfold Ty_rename_WF_Type'_P1; intros; destruct te' as [tys' te']; simpl in H1; 
      injection H1; intros; subst.
    constructor.
    eapply H; auto.
    rewrite len_map in len; assumption.
    destruct P2; split; intros.
    generalize (nth_error_map _ _ (fun ty : Ty => Ty_rename ty n) _ _ _ H3); intros H3'.
    destruct (H0 _ _ H3') as [ty' [nth_ty' sub_t_ty']].
    caseEq (nth_error typs n0).
    generalize (nth_error_map _ _ (fun typ' : Generic.GTy TX * N =>
                  Ty_trans (snd typ') (Extract_TyVar _ _ typs)
                    (map (fun ty : Ty => Ty_rename ty n) tys')) _ _ _ H4); intros nth_ty'';
      rewrite nth_ty'' in nth_ty'; injection nth_ty'; intros; subst; clear nth_ty'.
    exists (Ty_trans (snd p) (Extract_TyVar _ _ typs) tys'); split.
    rewrite (nth_error_map _ _ (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar _ _ typs) tys') _ _ _ H4).
    reflexivity.
    destruct (exists_Free_Vars (snd p)) as [Vs FV_p].
    erewrite <- Ty_rename_Ty_trans_tot' in sub_t_ty'; eauto.
    eapply (Ty_rename_subtype' _ _ _ sub_t_ty'); reflexivity.
    generalize tys' len; clear; induction typs; destruct tys'; simpl; intros; 
      try discriminate; auto.
    intros; eapply Bound_Ys.
    apply P2'_if_P2 in FV_typs; destruct FV_typs.
    destruct (H6 _ _ H4) as [B [nth_Ys FV_B]].
    rewrite <- (Free_Vars_id _ _ _ FV_p FV_B) in nth_Ys.
    generalize Vs Ys H5 nth_Ys; clear; induction n0; destruct Ys; simpl; intros;
      try discriminate.
    injection nth_Ys; intros; subst; apply in_or_app; left; auto.
    simpl; apply in_or_app; right; eauto.
    rewrite (nth_error_map' _ _ _ _ _ H4) in nth_ty'; discriminate.
    generalize (H2 _ (nth_error_map' _ _ _ _ _ H3)); intros; rewrite nth_error_map'.
    reflexivity.
    caseEq (nth_error typs n0).
    rewrite (nth_error_map _ _ _ _ _ _ H5) in H4; discriminate.
    assumption.
  Qed.

  Lemma I_Ty_rename_WF_Type' : forall (gamma : Context) i int te IT_i wf_int,
    Ty_rename_WF_Type'_Q'' gamma (Interface_ie int) te wf_int ->
    Ty_rename_WF_Type'_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold Ty_rename_WF_Type'_Q''; unfold Ty_rename_WF_Type'_P; unfold Generic.Ty_rename_WF_Type'_P;
      intros.
    destruct (Ty_rename_I_Ty_Wrap_eq _ _ _ H1) as [te' [eq_te' eq_T']]; subst;
      rewrite I_Ty_rename_invert in H1; simpl in H1; apply I_Ty_Wrap_inject in H1;
        injection H1; intros; subst.
    apply I_WF_Type_Wrap; econstructor; try eassumption.
    generalize (WF_IT _ _ IT_i); intros H2; inversion H2; subst.
    destruct (Int_WF_bound _ H2) as [Ys [FV_Ys Bound_Ys]].
    eapply (H Ys); eauto.
  Qed.

  Definition Type_Subst_Sub_2_5_P' := Type_Subst_Sub_2_5_P' _ _ N N_Wrap _ Empty subtype Ty_trans
    WF_Type TUpdate app_context subst_context.

  Variable (Ty_trans_eq_NTy_trans : forall N Xs Us, N_Wrap (N_trans N Xs Us) = Ty_trans N Xs Us).

  Lemma I_Type_Subst_Sub_2_5' : forall delta S T (sub_S_T : I_subtype delta S T),
    Type_Subst_Sub_2_5_P' _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Type_Subst_Sub_2_5_P'; unfold Generic.Type_Subst_Sub_2_5_P'; intros.
    inversion sub_S_T; subst.
    generalize (WF_CT _ _ H5); intros; inversion H1; subst.
    generalize (I_WF_Type_invert _ _ (GJ_L_WF_WF_Int _ _ _ _ _ _ _ _ H14 H1 H7)); intros WF_Ity.
    inversion WF_Ity; subst.
    apply I_Ty_Wrap_inject in H8; injection H8; intros; subst.
    rewrite I_Ty_trans_invert; rewrite FJ_Ty_trans_invert; simpl.
    apply I_subtype_Wrap; econstructor; try eassumption.
    eapply Type_Subst_Sub_2_5_TE; try eassumption.
    destruct H2 as [In_n NIn_n]; split; intros.
    destruct (In_n _ _ H2) as [b [nth_b sub_a_b]].
    exists b; rewrite Ty_trans_eq_NTy_trans; split; auto.
    eauto.
  Qed.

  Definition Free_Vars_Ty_Rename_P := Free_Vars_Ty_Rename_P _ _ Free_Vars rename_X Ty_rename.
  Definition Free_Vars_TE_Rename_P := Free_Vars_TE_Rename_P _ _ TE_Free_Vars rename_X TE_rename.

  Lemma I_Free_Vars_Ty_Rename : forall te i, Free_Vars_TE_Rename_P te -> 
    Free_Vars_Ty_Rename_P (I_Ty_Wrap (ity_def _ _ te i)).
    unfold Free_Vars_Ty_Rename_P; unfold Generic.Free_Vars_Ty_Rename_P; intros.
    rewrite I_Ty_rename_invert in H0; apply I_Free_Vars_invert in H0;
      inversion H0; subst; apply I_Ty_Wrap_inject in H2; injection H2; intros; subst.
    apply (H _ _ _ H3 H1).
  Qed.
  
  Definition N_Bound := N_Bound _ _ N_Wrap Context.

  Variable (mtype_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (N_Bound'_invert : forall delta n ty, Bound' delta (N_Wrap n) ty -> N_Bound delta n ty).

  Definition WF_Type_par_Lem_P' := 
    cFJ.WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty  FJ_Ty_Wrap E _ _ CT Context wf_class_ext
    WF_Type mtype_build_te L_build_context.

  Lemma I_WF_Type_par_Lem' : 
    forall gamma ty wf_ty, WF_Type_par_Lem_P' gamma ty (I_WF_Type_Wrap _ _ wf_ty).
    unfold WF_Type_par_Lem_P'; unfold cFJ.WF_Type_par_Lem_P'; intros; subst.
    inversion wf_ty; subst.
    apply sym_eq in H; apply Ty_Wrap_discriminate' in H; contradiction.
  Qed.

  Lemma FJ_Fields_Ity_False fields_build_te fields_build_tys : forall gamma (ity : I_Ty) fds, 
    ~ cFJ.FJ_fields _ _ _ _ _ _ FJ_Ty_Wrap E md_ext cld_ext CT Context fields fields_build_te 
    fields_build_tys gamma ity fds.
    unfold not; intros; inversion H; subst; eapply Ty_Wrap_discriminate'; eauto.
  Qed.

  Definition Lem_2_8_P := cFJ.Lem_2_8_P _ _ _ subtype fields Bound'.

  Variable (Fields_Ity_False : forall gamma (ity : I_Ty) fds, ~fields gamma ity fds).

  Lemma FJ_Map_Fields_Ity_False : forall (ity : I_Ty) T gamma gamma' fds, 
    Bound' gamma ity T -> ~fields gamma' T fds.
    intros; apply N_Bound'_invert in H; inversion H; subst.
    rewrite H2; apply Fields_Ity_False.
  Qed.

  Definition Subtype_Weaken_P := Subtype_Weaken_P Ty Context subtype Empty.

  Lemma I_Subtype_Weaken: forall delta S T (sub_S_T : I_subtype delta S T),
    Subtype_Weaken_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Subtype_Weaken_P; unfold Interface.Subtype_Weaken_P; unfold cFJ.Subtype_Weaken_P;
      intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.

  Definition Weaken_subtype_Update_list_P := Weaken_subtype_Update_list_P _ _ subtype _ Update.

  Lemma I_Weaken_subtype_Update_list: forall delta S T (sub_S_T : I_subtype delta S T),
    Weaken_subtype_Update_list_P _ _ _ (I_subtype_Wrap _ _ _ sub_S_T).
    unfold Weaken_subtype_Update_list_P; unfold Generic.Weaken_subtype_Update_list_P; intros;
      inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eauto.
  Qed.

  Definition Weaken_WF_Update_list_P := Weaken_WF_Update_list_P _ _ WF_Type _ Update.
  Definition Weaken_WF_Update_list_P1 := Weaken_WF_Update_list_P1 _ _ WF_Type _ Update.
  
  Definition Weaken_WF_Update_list_Q'' delta' int te (_ : wf_int_ext delta' int te) :=
    forall delta Vars, delta' = update_list delta Vars -> wf_int_ext delta int te.
  
  Variable (Weaken_subtype_Update_list : forall delta S T sub_S_T, Weaken_subtype_Update_list_P delta S T sub_S_T).

  Lemma I_Weaken_WF_Update_list_ext : forall (ie : int_def_ext) gamma (typs : TyP_List) tys 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype gamma)),
    Weaken_WF_Update_list_P1 gamma tys P1-> 
    forall delta Vars, gamma = update_list delta Vars -> 
      I_wf_int_ext delta (typs, ie) (tys, te).
    unfold Weaken_WF_Update_list_P1; unfold Generic.Weaken_WF_Update_list_P1; intros.
    constructor; auto.
    eapply H; eassumption.
    destruct P2 as [In_ty NIn_ty]; split; intros.
    destruct (In_ty _ _ H1) as [b [nth_b sub_a_b]]; exists b; split; auto.
    eapply Weaken_subtype_Update_list; try eassumption; reflexivity.
    auto.
  Defined.

  Lemma I_Weaken_WF_Update_list : forall (gamma : Context) i int te IT_i wf_int,
    Weaken_WF_Update_list_Q'' gamma (Interface_ie int) te wf_int ->
    Weaken_WF_Update_list_P _ _ (I_WF_Type_Wrap _ _ 
      (WF_Int _ _ _ I_Ty_Wrap _ _ _ _ _ IT wf_int_ext gamma i int te IT_i wf_int)).
    unfold Weaken_WF_Update_list_P; unfold Generic.Weaken_WF_Update_list_P; intros.
    apply I_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma Bound_id' : forall (I : I_Ty), Generic.Bound'_id_P _ _ Bound' I.
    unfold Bound'_id_P; intros.
    apply N_Bound'_invert in H; apply N_Bound'_invert in H0; inversion H; inversion H0; subst.
    rewrite H3; rewrite H6; reflexivity.
  Qed.

  Lemma I_Weaken_subtype_app_TList : forall delta S T sub_S_T, 
    Generic.Weaken_subtype_app_TList_P _ _ _ _ Empty subtype TUpdate _ _ _ (I_subtype_Wrap delta S T sub_S_T).
    unfold Weaken_subtype_app_TList_P; intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eassumption.
  Qed.

  Variable Weaken_subtype_app_TList : forall delta S T sub_S_T, 
    Generic.Weaken_subtype_app_TList_P _ _ _ _ Empty subtype TUpdate delta S T sub_S_T.
    
  Definition Weaken_WF_Type_app_TList_Q'' delta int te 
    (wf_int : wf_int_ext delta int te) :=
    forall XNs YOs, delta = update_Tlist Empty XNs -> wf_int_ext (update_Tlist Empty (XNs ++ YOs)) int te.

  Lemma Weaken_WF_Type_app_TList_int_ext : forall (ie : int_def_ext) (delta : Context)
    (typs : TyP_List) (tys : list Ty) (te : ty_def_ext) (P1 : List_P1 (WF_Type delta) tys)
    (len : length typs = length tys)
    (P2 : List_P2 tys (map (fun typ'  =>
      Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys) typs) (subtype delta)),
    Weaken_WF_Type_app_TList_P1 _ Ty N Context Empty WF_Type TUpdate delta tys P1 ->
    forall XNs YOs, delta = update_Tlist Empty XNs -> 
      I_wf_int_ext (update_Tlist Empty (XNs ++ YOs)) (typs, ie) (tys, te).
    intros; subst; constructor; auto.
    destruct P2; split; intros.
    destruct (H0 _ _ H2) as [b [nth_typs sub_a_b]].
    exists b; split; auto.
    eapply Weaken_subtype_app_TList; try eassumption; reflexivity.
    eauto.
  Qed.
  
  Lemma I_Weaken_WF_Type_app_TList_int : (forall (gamma : Context) i Int
    (te : ty_ext) (IT_i : IT i = Some Int) wf_int,
    Weaken_WF_Type_app_TList_Q'' gamma (Interface.Interface_ie _ Ty mty_ext _ _ Interface_ext Int) te wf_int ->
    Weaken_WF_Type_app_TList_P _ Ty N Context Empty WF_Type TUpdate
    gamma (I_Ty_Wrap (ity_def _ _ te i))
    (I_WF_Type_Wrap gamma (I_Ty_Wrap (ity_def _ _ te i))
      (WF_Int _ _ Ty I_Ty_Wrap mty_ext _ _ Interface_ext
        Context IT wf_int_ext gamma i Int te IT_i wf_int))).
    unfold Weaken_WF_Type_app_TList_Q''; unfold Weaken_WF_Type_app_TList_P; intros.
    apply I_WF_Type_Wrap; econstructor; try eassumption.
    eapply H; eassumption.
  Defined.
  
  Lemma I_ex_WF_Bound' : forall I, ex_WF_Bound'_P Ty N N_Wrap Context WF_Type Bound' (N_Wrap (I_N_Wrap I)).
    unfold ex_WF_Bound'_P; intros; eexists _; apply N_Bound'_Wrap; constructor.
  Qed.

  Lemma I_sub_Bound : forall delta S T sub_S_T, sub_Bound'_P _ _ subtype Bound' _ _ _ 
    (I_subtype_Wrap delta S T sub_S_T).
    unfold sub_Bound'_P; intros; inversion sub_S_T; subst.
    apply N_Bound'_invert in H; apply N_Bound'_invert in H0; inversion H; inversion H0; subst.
    rewrite H6; rewrite H9; apply I_subtype_Wrap; fold (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))); 
      fold (I_Ty_Wrap (ity_def _ _ te'' i)); econstructor; try eassumption.
  Qed.
    
  Variable N_Wrap_inject : forall n n', N_Wrap n = N_Wrap n' -> n = n'.
  Variable build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop.

  Definition FJ_subtype := cFJ.FJ_subtype C F M X ty_ext Ty FJ_Ty_Wrap
    E md_ext cld_ext CT Context subtype build_te.

  Variable FJ_subtype_Wrap : forall gamma ty ty', FJ_subtype gamma ty ty' -> subtype gamma ty ty'.

  Lemma I_Lem_2_7 : forall i, Generic.Lem_2_7_P _ _ _ N_Wrap
      _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound' (N_Wrap (I_N_Wrap i)).
    unfold Generic.Lem_2_7_P; intros; apply N_Bound'_invert in H5; inversion H5; subst.
    apply N_Wrap_inject in H8; subst.
    destruct i; eexists _; fold (I_Ty_Wrap (ity_def _ _ t i)); rewrite I_Ty_trans_invert; simpl;
      split.
    apply N_Bound'_Wrap; unfold I_Ty_Wrap; econstructor.
    apply FJ_subtype_Wrap; econstructor.
  Qed.

  Lemma I_Bound'_sub : forall i, Bound'_sub_P _ _ subtype Bound' (N_Wrap (I_N_Wrap i)).
    unfold Bound'_sub_P; intros; apply N_Bound'_invert in H; inversion H; subst.
    apply FJ_subtype_Wrap; econstructor.
  Qed.

  Lemma I_Trans_Bound' : forall i, Trans_Bound'_P _ _ _ Ty_trans Bound' (N_Wrap (I_N_Wrap i)).
    unfold Trans_Bound'_P; intros; apply N_Bound'_invert in H; inversion H; subst.
    rewrite <- Ty_trans_eq_NTy_trans; apply N_Bound'_Wrap; econstructor.
  Qed.

  Lemma I_Bound_total' : forall gamma S T sub_S_T,
    Bound_total_P _ _ subtype Bound' _ _ _ (I_subtype_Wrap gamma S T sub_S_T).
    unfold Bound_total_P; intros; inversion sub_S_T; subst; apply N_Bound'_invert in H; inversion H; subst.
    unfold FJ_Ty_Wrap; intros; eexists _; apply N_Bound'_Wrap; econstructor.
  Qed.

  Lemma I_Lem_2_7'' : forall i, 
    Lem_2_7''_P _ _ _ N_Wrap _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound' (N_Wrap (I_N_Wrap i)).
    unfold Lem_2_7''_P; intros; subst; apply N_Bound'_invert in H5; inversion H5; subst.
    rewrite H7; rewrite <- Ty_trans_eq_NTy_trans; eexists _; split.
    eapply N_Bound'_Wrap; econstructor.
    apply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma I_subtype_update_list_id' : forall delta S T sub_S_T,
    subtype_update_list_id'_P _ _ subtype _ Update _ _ _ (I_subtype_Wrap delta S T sub_S_T).
    unfold subtype_update_list_id'_P; intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eassumption.
  Qed.

  Variable subtype_update_list_id' : forall delta S T sub_S_T, 
    subtype_update_list_id'_P _ _ subtype _ Update delta S T sub_S_T.

  Definition WF_Type_update_list_id'_Q'' delta int te 
    (wf_int : wf_int_ext delta int te) := forall Vars, wf_int_ext (update_list delta Vars) int te.

  Lemma WF_Type_update_list_id'_int_ext : forall (ie : int_def_ext) (delta : Context)
    (typs : TyP_List) (tys : list Ty)
    (te : FJ_ty_ext) (P1 : List_P1 (WF_Type delta) tys)
    (len : length typs = length tys)
    (P2 : List_P2 tys
            (map
               (fun typ' =>
                Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ _ typs) tys)
               typs) (subtype delta)),
  WF_Type_update_list_id'_P1 Ty Context WF_Type _ Update delta tys P1 ->
  forall Vars, I_wf_int_ext (update_list delta Vars) (typs, ie) (tys, te).
    unfold WF_Type_update_list_id'_P1; intros; econstructor; try eassumption.
    eapply H.
    destruct P2; split; intros.
    destruct (H0 _ _ H2) as [b [nth_typs sub_a_b]].
    exists b; split; auto.
    eapply subtype_update_list_id'; try eassumption; reflexivity.
    eauto.
  Qed.
  
  Lemma I_WF_Type_update_list_id' : (forall (gamma : Context) (i : _)
    (Int : Interface.Interface _ Ty mty_ext _ _ Interface_ext)
    (te : ty_ext) (IT_i : IT i = Some Int) wf_int,
    WF_Type_update_list_id'_Q'' gamma _ te wf_int ->
    WF_Type_update_list_id'_P Ty Context WF_Type _ Update gamma
          (I_Ty_Wrap (ity_def _ ty_ext te i))
          (I_WF_Type_Wrap gamma (I_Ty_Wrap (ity_def _ ty_ext te i))
             (WF_Int _ ty_ext Ty I_Ty_Wrap mty_ext _ _ Interface_ext
                Context IT wf_int_ext gamma i Int te IT_i wf_int))).
    unfold WF_Type_update_list_id'_P; unfold WF_Type_update_list_id'_Q''; intros.
    apply I_WF_Type_Wrap; econstructor; try eauto.
  Qed.

  Lemma I_Strengthen_Bound'' : forall i, Strengthen_Bound''_P _ _ _ Update Bound' (N_Wrap (I_N_Wrap i)).
    unfold Strengthen_Bound''_P; intros.
    eapply N_Bound'_invert in H; inversion H; subst.
    apply N_Bound'_Wrap; econstructor.
  Qed.

  Lemma I_Strengthen_Bound' : forall i, Strengthen_Bound'_P _ _ _ Update Bound' (N_Wrap (I_N_Wrap i)).
    unfold Strengthen_Bound'_P; intros.
    eapply N_Bound'_invert in H; inversion H; subst.
    apply N_Bound'_Wrap; econstructor.
  Qed.

  Lemma I_subtype_update_Tupdate : forall delta S T sub_S_T,
    subtype_update_Tupdate_P _ _ _ _ subtype _ TUpdate Update _ _ _ (I_subtype_Wrap delta S T sub_S_T).
    unfold subtype_update_Tupdate_P; intros; inversion sub_S_T; subst.
    apply I_subtype_Wrap; econstructor; eassumption.
  Qed.
    
  Variable subtype_update_Tupdate : forall delta S T sub_S_T,
    subtype_update_Tupdate_P _ _ _ _ subtype _ TUpdate Update delta S T sub_S_T.

  Definition WF_Type_update_Tupdate_Q'' delta int te (wf_int : wf_int_ext delta int te) :=
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      wf_int_ext (update_list (update_Tlist gamma XNs) Vars) int te.

  Lemma WF_Type_update_Tupdate_int_ext : forall (ie : int_def_ext) (delta : Context)
    (typs : TyP_List ) (tys : list Ty)
    (te : FJ_ty_ext) (P1 : List_P1 (WF_Type delta) tys)
    (len : length typs = length tys)
    (P2 : List_P2 tys
            (map
               (fun typ' =>
                Ty_trans (N_Wrap (snd typ')) (Extract_TyVar _ N typs) tys)
               typs) (subtype delta)),
  WF_Type_update_Tupdate_P1 _ Ty N Context WF_Type _ TUpdate Update delta
    tys P1 ->
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      I_wf_int_ext (update_list (update_Tlist gamma XNs) Vars) (typs, ie) (tys, te).
    intros; subst; econstructor; eauto.
    destruct P2; split; intros.
    destruct (H0 _ _ H2) as [b [nth_typs sub_a_b]].
    exists b; split; auto.
    eapply subtype_update_Tupdate; try eassumption; reflexivity.
    eauto.
  Qed.

    Lemma I_WF_Type_update_Tupdate : (forall (gamma : Context) (i : _)
          (Int : Interface.Interface _ Ty mty_ext _ _ Interface_ext)
          (te : ty_ext) (IT_i : IT i = Some Int) wf_int,
        WF_Type_update_Tupdate_Q'' gamma (Interface.Interface_ie _ Ty mty_ext _ _ Interface_ext Int)  te wf_int ->
        WF_Type_update_Tupdate_P _ Ty N Context WF_Type _ TUpdate Update
          gamma (I_Ty_Wrap (ity_def _ ty_ext te i))
          (I_WF_Type_Wrap gamma (I_Ty_Wrap (ity_def _ ty_ext te i))
             (WF_Int _ ty_ext Ty I_Ty_Wrap mty_ext _ _ Interface_ext
                Context IT wf_int_ext gamma i Int te IT_i wf_int))).
      unfold WF_Type_update_Tupdate_Q''; unfold WF_Type_update_Tupdate_P; intros; subst.
      apply I_WF_Type_Wrap; econstructor; eauto.
    Qed.

  Lemma I_Ty_trans_app : forall (te : ty_ext) (cl : _),
    TE_trans_app_Q _ Ty _ TE_Free_Vars TE_trans te ->
    Ty_trans_app_P _ Ty Ty_trans Free_Vars (I_Ty_Wrap (ity_def _ ty_ext te cl)).
    unfold TE_trans_app_Q; unfold Ty_trans_app_P; intros; subst.
    apply I_Free_Vars_invert in H1; inversion H1; subst; apply I_Ty_Wrap_inject in H3;
      injection H3; intros; subst; repeat rewrite I_Ty_trans_invert; simpl; erewrite H; eauto.
  Qed.
    
  Lemma I_Strengthen_subtype_update_TList : forall delta S T sub_S_T,
    Strengthen_subtype_update_TList_P _ _ subtype _ Update _ _ _ (I_subtype_Wrap delta S T sub_S_T).
    unfold Strengthen_subtype_update_TList_P; intros; inversion sub_S_T; subst;
      apply I_subtype_Wrap; econstructor; try eassumption.
  Qed.

  Variable Strengthen_subtype_update_TList : forall delta S T sub_S_T,
    Strengthen_subtype_update_TList_P _ _ subtype _ Update delta S T sub_S_T.

  Definition Strengthen_WF_Type_update_TList_Q'' delta int te (_ : wf_int_ext delta int te) :=
    forall gamma Vars, delta = update_list gamma Vars -> wf_int_ext gamma int te.

  Lemma Strengthen_WF_Type_update_TList_int_ext : forall (ie : int_def_ext) (delta : Context)
    (typs : TyP_List) (tys : list Ty)
    (te : FJ_ty_ext) (P1 : List_P1 (WF_Type delta) tys)
    (len : length typs = length tys)
    (P2 : List_P2 tys (map (fun typ' => Ty_trans (N_Wrap (snd typ')) 
      (Extract_TyVar _ N typs) tys) typs) (subtype delta)),
    Strengthen_WF_Type_update_TList_P1 Ty Context WF_Type _ Update delta tys P1 ->
    forall gamma Vars, delta = update_list gamma Vars -> I_wf_int_ext gamma (typs, ie) (tys, te).
    intros; subst; econstructor; eauto.
    destruct P2; split; intros.
    destruct (H0 _ _ H2) as [b [nth_typs sub_a_b]].
    exists b; split; auto.
    eapply Strengthen_subtype_update_TList; try eassumption; reflexivity.
    eauto.
  Qed.

  Lemma I_Strengthen_WF_Type_update_TList : (forall (gamma : Context) (i : _)
    (Int : Interface.Interface _ Ty mty_ext _ _ Interface_ext)
    (te : ty_ext) (IT_i : IT i = Some Int) wf_int,
    Strengthen_WF_Type_update_TList_Q'' gamma (Interface.Interface_ie _ Ty mty_ext _ _ Interface_ext Int) 
    te wf_int ->
    Strengthen_WF_Type_update_TList_P Ty Context WF_Type _ Update gamma (I_Ty_Wrap (ity_def _ ty_ext te i))
    (I_WF_Type_Wrap gamma (I_Ty_Wrap (ity_def _ ty_ext te i))
      (WF_Int _ ty_ext Ty I_Ty_Wrap mty_ext _ _ Interface_ext
        Context IT wf_int_ext gamma i Int te IT_i wf_int))).
    unfold Strengthen_WF_Type_update_TList_P; unfold Strengthen_WF_Type_update_TList_Q''; intros; subst.
    apply I_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma I_Ty_trans_no_op : forall (te : ty_ext) (cl : _),
    Ty_trans_no_op_Q _ Ty _ TE_Free_Vars TE_trans te ->
    Ty_trans_no_op_P _  _ Ty_trans Free_Vars (I_Ty_Wrap (ity_def _ ty_ext te cl)).
    unfold Ty_trans_no_op_Q; unfold Ty_trans_no_op_P; intros.
    apply I_Free_Vars_invert in H0; inversion H0; subst.
    apply I_Ty_Wrap_inject in H2; injection H2; intros; subst;
      rewrite I_Ty_trans_invert; simpl; erewrite H; auto.
    assumption.
  Defined.

  Lemma I_Ty_trans_fresh_vars : forall (te : ty_ext) (cl : _),
    Ty_trans_fresh_vars_Q TX Ty _ GJ_Ty_Wrap Free_Vars TE_Free_Vars TE_trans te ->
    Ty_trans_fresh_vars_P TX Ty GJ_Ty_Wrap Ty_trans Free_Vars(I_Ty_Wrap (ity_def _ ty_ext te cl)).
    unfold Ty_trans_fresh_vars_Q; unfold Ty_trans_fresh_vars_P; intros.
    apply I_Free_Vars_invert in H1; inversion H1; subst.
    apply I_Ty_Wrap_inject in H5; injection H5; intros; subst;
      repeat (rewrite I_Ty_trans_invert; simpl); erewrite H; try eassumption; auto.
  Defined.
    
End Preservation.

End Generic_Interfaces.

