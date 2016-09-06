Require Import Omega.
Require Import FJ_tactics.
Require Import cFJ.
Require Import Cast.
Require Import Interface.
Require Import Generic.
Require Import Generic_Interface.
Require Import Generic_Cast.

Require Import List.
Require Import Arith.

Definition CL := cFJ.CL nat.

Inductive Ty : Set :=
| N_Wrap : N -> Ty 
| Gty : GTy nat -> Ty
  with 
    N : Set :=
| cFJ_N : cFJ.FJ_Ty nat (@GTy_ext Ty FJ_ty_ext) -> N
| I_N_Wrap : I_Ty nat (@GTy_ext Ty unit) -> N.

Definition ty_ext := @GTy_ext Ty FJ_ty_ext.
Definition md_ext := @MD_ext nat N FJ_md_ext.
Definition mty_ext := @mty_ext nat N FJ_mty_ext.
Definition cld_ext := @Generic.cld_ext nat N (@I_cld_ext nat ty_ext unit).
Definition m_call_ext := @MCall_ext Ty FJ_m_call_ext.
Definition I_cld_ext := @I_cld_ext nat ty_ext unit.

Definition TyP_List := Generic.TyP_List nat N.

Inductive E : Set :=
| cFJ_E : FJ_E nat nat nat nat ty_ext E m_call_ext -> E
| Cast_E : Cast.Cast_E nat ty_ext E -> E.

Definition FD := cFJ.FD nat Ty.
Definition MD := cFJ.MD nat nat Ty E md_ext.
Definition MTy := cFJ.Mty Ty mty_ext.
Definition mb_ext := FJ_mb_ext.
Definition MB := cFJ.MB nat E mb_ext.

Definition L := cFJ.L nat nat nat nat ty_ext Ty E md_ext cld_ext.

Definition Abs_Mty := Interface.Abs_Mty Ty mty_ext nat nat.

Definition Interface_ext := @GInterface_ext nat N unit.
Definition Interface := Interface.Interface nat Ty mty_ext nat nat Interface_ext.

Variable (CT : nat -> option L)
  (IT : nat -> option Interface).

Definition I_Ty_Wrap I := N_Wrap (I_N_Wrap I).
Definition FJ_Ty_Wrap := Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N.

Fixpoint Ty_trans (ty : Ty) (txs : list nat) (tys : list Ty) : Ty :=
  match ty with 
    | N_Wrap (cFJ_N ty) => FJ_Ty_Trans _ _ _ _ N N_Wrap cFJ_N (GJ_TE_Trans _ _ Ty_trans _) ty txs tys
    | N_Wrap (I_N_Wrap ty) => I_Ty_Trans _ _ _ _ _ N_Wrap I_N_Wrap (GJ_TE_Trans _ _ Ty_trans _) ty txs tys
    | Gty gty => GTy_trans _ (eq_nat_dec) _ Gty gty txs tys 
  end.

Definition N_trans (n : N) (txs : list nat) (tys : list Ty) : N :=
  match n with 
    | cFJ_N (ty_def te c)  => cFJ_N (ty_def _ _ ((GJ_TE_Trans _ _ Ty_trans _) te txs tys) c)
    | I_N_Wrap (ity_def te i) => I_N_Wrap (ity_def _ _ ((GJ_TE_Trans _ _ Ty_trans _) te txs tys) i)
  end.

Variable (Context : Set)
  (TLookup : Context -> nat -> N -> Prop)
  (Empty : Context).

Definition implements (ce : cld_ext) := @I_implements nat ty_ext FJ_cld_ext (@snd _ _ ce).

Definition build_te := @GJ_build_te _ _ N Ty_trans _ _ (fun (ice : I_cld_ext) te te' te''=>
  FJ_build_te (snd ice) te te' te'').

Definition isub_build_te := build_te.

Inductive subtype : Context -> Ty -> Ty -> Prop :=
| cFJ_sub : forall gamma ty ty', 
  cFJ.FJ_subtype nat nat nat nat _ Ty FJ_Ty_Wrap 
  E md_ext cld_ext CT Context subtype build_te gamma ty ty' -> subtype gamma ty ty'
| GJ_sub : forall gamma ty ty', Generic.GJ_subtype _ _ Gty N N_Wrap _
  TLookup gamma ty ty' -> subtype gamma ty ty'
| I_subtype_Wrap : forall gamma ty ty', Interface.I_subtype nat ty_ext Ty I_Ty_Wrap _ _ _ _ _ _ _ _ CT 
  isub_build_te implements FJ_Ty_Wrap gamma ty ty' -> subtype gamma ty ty'.

Variables (Update : Context -> Var nat -> Ty -> Context)
  (TUpdate : Context -> nat -> N -> Context)
  (lookup : Context -> Var nat -> Ty -> Prop)
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


  Definition update_list := cFJ.update_list nat Ty Context Update.
  Definition update_Tlist := Generic.update_Tlist nat N Context TUpdate.

  Variables 
    (TLookup_unique : forall gamma X ty ty', TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty')
    (TLookup_dec : forall gamma X, (exists ty, TLookup gamma X ty) \/ (forall ty, ~TLookup gamma X ty))
    (TLookup_app : forall gamma delta X ty, TLookup gamma X ty -> TLookup (app_context gamma delta) X ty)
    (TLookup_app' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') -> TLookup delta X ty -> 
      TLookup (app_context gamma delta) X ty)
    (TLookup_app'' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') ->  
      TLookup (app_context gamma delta) X ty -> TLookup delta X ty)
    (TLookup_Empty : forall X ty, ~ TLookup Empty X ty)
    (subst_context : Context -> list nat -> list Ty -> Context)
    (subst_context_nil : forall delta Us, subst_context delta nil Us = delta)
    (subst_context_nil' : forall delta Xs, subst_context delta Xs nil = delta)
    (TLookup_subst : forall gamma X ty Xs Us, TLookup gamma X ty -> 
      TLookup (subst_context gamma Xs Us) X (N_trans ty Xs Us))
    (TLookup_update_eq : forall gamma X ty, TLookup (TUpdate gamma X ty) X ty) 
    (TLookup_update_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty) 
    (TLookup_update_neq' : forall gamma Y X ty ty', X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty -> TLookup gamma X ty).

Definition wf_object_ext := @GJ_wf_object_ext Ty Context unit.

Definition wf_class_ext' WF_Type := @GJ_wf_class_ext nat Ty _ N_Wrap Context subtype Ty_trans 
  WF_Type I_cld_ext FJ_ty_ext.

Definition wf_int_ext' WF_Type := 
  @Generic_Interface.I_wf_int_ext nat Ty N Context 
  WF_Type subtype Ty_trans N_Wrap unit FJ_ty_ext.

Inductive WF_Type : Context -> Ty -> Prop :=
  cFJ_WF_Type : forall gamma ty, cFJ.FJ_WF_Type _ _ _ _ _ _ FJ_Ty_Wrap
    _ _ _ CT Context (wf_class_ext' WF_Type) wf_object_ext gamma ty -> WF_Type gamma ty
| GJ_WF_Type : forall gamma ty, GJ_WF_Type _ _ Gty _ _ TLookup gamma ty -> WF_Type gamma ty
| I_WF_Type_Wrap : forall gamma ty, Interface.I_WF_Type nat ty_ext Ty
   I_Ty_Wrap mty_ext nat nat Interface_ext Context IT (wf_int_ext' WF_Type) gamma ty ->
  WF_Type gamma ty.

Definition wf_class_ext := wf_class_ext' WF_Type.
Definition wf_int_ext := wf_int_ext' WF_Type.

Definition fields_build_te (ce : cld_ext) (te te' te'' : ty_ext) := 
  Generic.fields_build_te nat Ty _ Ty_trans (fun ice => FJ_fields_build_te (snd ice)) ce te te' te''.

Definition fields_build_tys (te : ty_ext) (ce : cld_ext) (tys tys' : list Ty) :=
  Generic.fields_build_tys nat Ty _ Ty_trans 
  (fun te ice tys tys' => FJ_fields_build_tys Ty te (snd ice) tys tys') te ce tys tys'.

Inductive fields : Context -> Ty -> list FD -> Prop :=
  FJ_fields : forall gamma ty fds, cFJ.FJ_fields _ _ _ _ _ Ty FJ_Ty_Wrap _ _ _
    CT Context fields fields_build_te fields_build_tys gamma ty fds -> fields gamma ty fds.

Definition mtype_build_te (ce : cld_ext) (te te' te'' : ty_ext) :=
  Generic.mtype_build_te nat Ty _ Ty_trans 
  (fun (ice : I_cld_ext) te te' te'' => FJ_mtype_build_te (snd ice) te te' te'') ce te te' te''.

Variable build_fresh : list Ty -> Ty -> list Ty -> list nat -> TyP_List -> list nat -> Prop.

Definition mtype_build_tys (ce : cld_ext) (te : ty_ext) (ty : Ty) vds (mce : md_ext) (tys tys' : list Ty) :=
  Generic.mtype_build_tys _ _ Gty _ Ty_trans _ build_fresh 
  (fun ice te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys') 
  ce te ty vds mce tys tys'.

Definition N_Trans typs Us ty : N := N_trans ty (Extract_TyVar nat N typs) Us.

Definition mtype_build_mtye (ce : cld_ext) (te : ty_ext) (ty : Ty) vds (me : md_ext) (mtye : mty_ext) :=
  Generic.mtype_build_mtye nat Ty Gty N nat build_fresh N_Trans (fun ce te me ty vds (mtye : unit) => True) 
  ce te ty vds me mtye.

Definition imtype_build_tys := imtype_build_tys nat Ty nat N Gty Ty_trans FJ_mty_ext build_fresh
  (Interface.I_imtype_build_tys FJ_ty_ext Ty nat FJ_Interface_ext).

Definition imtype_build_mtye := imtype_build_mtye nat Ty _ N Gty FJ_mty_ext build_fresh
  N_Trans (Interface.I_imtype_build_mtye FJ_ty_ext Ty FJ_mty_ext nat FJ_Interface_ext).

Inductive mtype : Context -> nat -> Ty -> MTy -> Prop :=
| FJ_mtype : forall gamma m ty mty, cFJ.FJ_mtype _ _ _ _ _ Ty FJ_Ty_Wrap
    _ _ _ _ CT Context mtype mtype_build_te 
    mtype_build_tys mtype_build_mtye gamma m ty mty -> mtype gamma m ty mty
| I_mtype_Wrap : forall gamma m ty mty, Interface.I_mtype nat ty_ext Ty I_Ty_Wrap 
  mty_ext nat nat Interface_ext Context IT imtype_build_tys imtype_build_mtye gamma m ty mty ->
  mtype gamma m ty mty.

Definition mbody_build_te (ce : cld_ext) (te te' te'' : ty_ext) :=
  Generic.mbody_build_te _ Ty _ Ty_trans (fun ice te te' te'' => FJ_mbody_build_te (snd ice) te te' te'') 
  ce te te' te''.

Definition VD := VD Ty nat.

Definition mbody_m_call_map (XNs : TyP_List) (Us : list Ty) (mce mce': m_call_ext) :=
  Generic.GJ_mbody_m_call_map nat Ty N Ty_trans _ XNs Us mce mce'.

Definition mbody_new_map (XNs : TyP_List) (Us : list Ty) (mce mce': m_call_ext) :=
  Generic.GJ_mbody_new_map nat Ty N Ty_trans _ XNs Us mce mce'. 

Inductive E_Ty_Trans : TyP_List -> list Ty -> E -> E -> Prop :=
| Base_E_Ty_Trans : forall XNs Us e e', Generic.E_Ty_Trans _ _ _ _ _ _ _ _ _ _ cFJ_E mbody_m_call_map
  mbody_new_map E_Ty_Trans XNs Us e e' -> E_Ty_Trans XNs Us e e'
| Cast_E_Ty_Trans : forall XNs Us e e', 
  Generic_Cast.E_Ty_Trans _ _ Ty ty_ext E _ Cast_E (GJ_TE_Trans _ _ Ty_trans _) E_Ty_Trans XNs Us e e' ->
  E_Ty_Trans XNs Us e e'.

Definition map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop :=
  Generic.map_mbody _ _ _ _ _ _ _ _ E_Ty_Trans.

Definition build_mb_ext (ce : cld_ext) (te : ty_ext) (mce : m_call_ext) (mde : md_ext) := 
  Generic.build_mb_ext _ _ _ _ _ _ _ _ (fun ce te mce mde => FJ_build_mb_ext (snd ce) te mce mde)
  ce te mce mde.

Inductive mbody : Context -> m_call_ext -> nat -> Ty -> MB -> Prop :=
  FJ_mbody : forall gamma Vs m ct mb, cFJ.mbody _ _ _ _ _ Ty 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ _ _ CT _ mbody_build_te 
    mb_ext (fun ce te mce mde mbe => True) map_mbody gamma Vs m ct mb -> mbody gamma Vs m ct mb.

Inductive Bound : Context -> Ty -> Ty -> Prop :=
| GJ_Bound : forall gamma ty ty', Generic.GJ_Bound nat _ Gty N _ TLookup gamma ty ty' ->
    Bound gamma ty (N_Wrap ty')
| N_Bound : forall gamma ty ty', Generic.N_Bound _ _ N_Wrap _ gamma ty ty' -> Bound gamma ty ty'.

Definition WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop := 
  GJ_WF_mtype_Us_map _ _ _ _ Ty_trans _ _ (FJ_WF_mtype_Us_map Ty Context).

Definition WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop :=
  GJ_WF_mtype_U_map _ _ _ _ Ty_trans _ _ (FJ_WF_mtype_U_map Ty Context).

Definition WF_mtype_ext (gamma : Context) (mce : m_call_ext) (mtye : mty_ext) :=
  GJ_WF_mtype_ext _ _ _ N_Wrap _ subtype Ty_trans WF_Type _ _ 
  (FJ_WF_mtype_ext _) gamma mce mtye.

Inductive E_WF : Context -> E -> Ty -> Prop :=
  FJ_E_WF : forall gamma e ty, cFJ.FJ_E_WF _ _ _ _ _ Ty FJ_Ty_Wrap _ _ cFJ_E mty_ext Context subtype WF_Type
    fields mtype E_WF lookup Bound Bound WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty gamma e ty -> E_WF gamma e ty
| Cast_E_WF : forall gamma e ty, 
  Cast.Cast_E_WF _ _ _ 
  (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ Cast_E E_WF Bound subtype gamma e ty ->
  E_WF gamma e ty.

Definition ce_build_cte : cld_ext -> ty_ext -> Prop :=
  Generic.GJ_ce_build_cte _ Ty Gty _ (fun ce te => True).

Definition Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop :=
  Generic.GJ_build_context _ N Context TUpdate (fun 
    (ice : I_cld_ext) mde gamma gamma' => FJ_Meth_build_context _ (snd ice) mde gamma gamma').

Definition Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop :=
  Generic.GJ_Meth_WF_Ext _ _ N N_Wrap Context WF_Type 
  (fun gamma (fcld : _) => cFJ.FJ_Meth_WF_Ext Context gamma (snd fcld)).

Inductive L_build_context' (fcld : (@Interface.I_cld_ext nat ty_ext FJ_cld_ext)) : Context -> Prop :=
  L_bld' : L_build_context' fcld Empty.

Definition L_build_context (fcld : cld_ext) := 
  Generic.L_build_context nat N _ TUpdate L_build_context' fcld.

Definition override := @Generic.override nat Ty Gty nat N N_Wrap Context Empty 
  subtype Ty_trans WF_Type nat nat build_fresh N_Trans TUpdate Update
  (@Interface.I_cld_ext nat ty_ext FJ_cld_ext) Bound unit unit unit unit 
  (fun fcld te te' te'' => FJ_build_te (snd fcld) te te' te'') (FJ_WF_mtype_Us_map Ty Context) (FJ_WF_mtype_U_map Ty Context)
  (FJ_WF_mtype_ext Context) (fun ce te me ty vds (mtye : unit) => True) L_build_context' 
  (fun ice te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys')
  (fun (ice : I_cld_ext) mde gamma gamma' => FJ_Meth_build_context _ (snd ice) mde gamma gamma')
  (fun gamma ce mde => True) (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) mtype.

Inductive Meth_WF : nat -> MD -> Prop :=
  FJ_Meth_WF : forall c md, cFJ.Meth_WF _ _ _ _ _ _ FJ_Ty_Wrap E _ _ CT Context subtype WF_Type 
    E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override c md -> Meth_WF c md.

Definition ioverride := @I_ioverride _ Ty _ _ _ mtype _ FJ_Ty_Wrap.

Definition L_WF_Ext (gamma : Context) (ce : cld_ext) c := 
  Generic.L_WF_Ext nat Ty nat N N_Wrap _ WF_Type 
  (fun gamma (ie : I_cld_ext) c => FJ_L_WF_Ext _ _ gamma (@snd _ _ ie) c ) gamma ce c /\
  GI_L_WF_Ext _ Ty ty_ext N _ WF_Type N_Wrap I_N_Wrap _ implements Empty gamma ce /\
  I_L_WF_Ext _ _ _ I_Ty_Wrap _ _ _ mtype nat _ ioverride gamma (snd ce) c 
  (FJ_L_WF_Ext _ _) ce_build_cte.

Definition L_WF : L -> Prop :=
  cFJ.L_WF _ _ _ _ _ _  FJ_Ty_Wrap _ _ _ CT _ subtype WF_Type 
  fields E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override
  L_WF_Ext L_build_context.

Definition Int_Meth_WF_Ext := GI_Int_Meth_WF_Ext nat _ _ _ WF_Type N_Wrap 
  (FJ_Meth_WF_Ext unit _).

Definition Int_Meth_build_context := GI_Int_Meth_build_context _ _ _ TUpdate
  (I_Int_Meth_build_context unit _).

Definition Int_WF_Ext := GI_Int_WF_Ext _ nat _ _ _ WF_Type N_Wrap (I_Int_WF_Ext nat _).

Definition Int_build_context := GI_Int_build_context _ _ _ TUpdate (I_Int_build_context Context Empty).

Definition I_WF : Interface -> Prop :=
  Interface.I_WF nat Ty mty_ext nat nat Interface_ext _ WF_Type Int_build_context Int_WF_Ext Int_Meth_WF_Ext
  Int_Meth_build_context.

Fixpoint trans (e : E) (Vars : list (Var nat)) (Es : list E) : E :=
  match e with 
    | cFJ_E fj_e => cFJ.FJ_E_trans _ _ _ _ _ _ _ cFJ_E trans eq_nat_dec fj_e Vars Es
    | Cast_E cast_e => Cast_E (Cast.Cast_E_trans _ _ _ _ trans cast_e Vars Es)
  end.

Inductive Reduce : E -> E -> Prop :=
| FJ_S_Reduce : forall e e', FJ_Reduce _ _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _
  cFJ_E _ _ CT _ fields mbody_build_te mb_ext (fun ce te mce mde mbe => True) map_mbody
  Empty trans e e' -> Reduce e e'
| FJ_C_Reduce : forall e e', FJ_Congruence_Reduce _ _ _ _ ty_ext E _ cFJ_E Reduce 
  Congruence_List_Reduce e e' -> Reduce e e'
| Cast_Reduce : forall e e', 
  Cast.Cast_Reduce _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) 
  _ _ Cast_E subtype nat nat nat m_call_ext cFJ_E Empty e e' ->
  Reduce e e'
| Cast_C_Reduce : forall e e', Cast_C_Reduce _ _ _ Cast_E Reduce e e' -> Reduce e e'
with Congruence_List_Reduce : list E -> list E -> Prop :=
| FJ_Reduce_List : forall es es', Reduce_List _ Reduce Congruence_List_Reduce es es' -> Congruence_List_Reduce es es'.

Section Preservation.

  Variables (app_context : Context -> Context -> Context)
    (TLookup_unique : forall gamma X ty ty', TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty')
    (TLookup_dec : forall gamma X, (exists ty, TLookup gamma X ty) \/ (forall ty, ~TLookup gamma X ty))
    (TLookup_app : forall gamma delta X ty, TLookup gamma X ty -> TLookup (app_context gamma delta) X ty)
    (TLookup_app' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') -> TLookup delta X ty -> 
      TLookup (app_context gamma delta) X ty)
    (TLookup_app'' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') ->  
      TLookup (app_context gamma delta) X ty -> TLookup delta X ty)
    (TLookup_Empty : forall X ty, ~ TLookup Empty X ty)
    (subst_context : Context -> list nat -> list Ty -> Context)
    (subst_context_nil : forall delta Us, subst_context delta nil Us = delta)
    (subst_context_nil' : forall delta Xs, subst_context delta Xs nil = delta)
    (TLookup_subst : forall gamma X ty Xs Us, TLookup gamma X ty -> 
      TLookup (subst_context gamma Xs Us) X (N_trans ty Xs Us))
    (TLookup_update_eq : forall gamma X ty, TLookup (TUpdate gamma X ty) X ty) 
    (TLookup_update_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty) 
    (TLookup_update_neq' : forall gamma Y X ty ty', X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty -> TLookup gamma X ty) 
    (TLookup_Update : forall gamma Y X ty ty',  
      TLookup (Update gamma Y ty') X ty -> TLookup gamma X ty) 
    (TLookup_Update' : forall gamma Y X ty ty',  
      TLookup gamma X ty -> TLookup (Update gamma Y ty') X ty) 
    (Lookup_dec : forall gamma x ty, lookup gamma x ty \/ ~ lookup gamma x ty)
    (Lookup_app : forall gamma delta x ty, lookup gamma x ty -> lookup (app_context gamma delta) x ty)
    (Lookup_app' : forall gamma delta x ty, (forall ty', ~ lookup gamma x ty') -> lookup delta x ty -> 
      lookup (app_context gamma delta) x ty)
    (WF_CT : forall (c : nat) l,
      CT c = Some l -> L_WF l)
    (WF_IT : forall i int, IT i = Some int -> I_WF int).

  Definition Fields_eq_def gamma ty fds (fields_fds : fields gamma ty fds) := 
    forall gamma' fds', fields gamma' ty fds' -> fds = fds'.
  
  Lemma cFJ_inject : forall ty ty', FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.
  
  Lemma fields_invert : forall (gamma : Context) ty (fds : list (cFJ.FD nat Ty)),
    fields gamma (FJ_Ty_Wrap ty) fds ->
    cFJ.FJ_fields nat nat nat nat ty_ext Ty FJ_Ty_Wrap E md_ext
    cld_ext CT Context fields fields_build_te fields_build_tys gamma
    (FJ_Ty_Wrap ty) fds.
    intros gamma ty fds fields_fds; inversion fields_fds; subst; assumption.
  Qed.

  Definition fields_build_te_id := 
    Generic.fields_build_te_id nat Ty N Ty_trans _ 
    (fun ice : I_cld_ext => FJ_fields_build_te_id (snd ice)).

  Definition fields_build_tys_id := Generic.fields_build_tys_id nat Ty N Ty_trans _ 
    (fun te (ice : I_cld_ext) => FJ_fields_build_tys_id Ty te (snd ice)).

  Fixpoint Fields_eq gamma ty fds (fields_fds : fields gamma ty fds) : Fields_eq_def _ _ _ fields_fds :=
    match fields_fds return Fields_eq_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_Fields_eq _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert
      fields_build_te_id fields_build_tys_id _ _ _ FJ_case Fields_eq
    end.

  Definition fds_distinct_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall cl1 cl2 f m n fds',
      map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
      nth_error fds' m = Some (fd nat Ty cl1 f) -> nth_error fds n = Some (fd nat Ty cl2 f) -> m = n.

  Definition Fields_Build_tys_len := Generic.Fields_Build_tys_len nat Ty N Ty_trans _ 
    (fun te (ice : I_cld_ext) => FJ_Fields_Build_tys_len Ty te (snd ice)).

  Lemma Ty_Wrap_discriminate : forall ty ty', FJ_Ty_Wrap ty <> Gty ty'.
    unfold FJ_Ty_Wrap; unfold Generic.FJ_Ty_Wrap; congruence.
  Qed.

  Definition WF_fields_map_id'  gamma ty ty' (bound : Bound gamma ty ty') :
    forall (tye : GTy_ext Ty) (c : cFJ.CL nat),
      ty = (FJ_Ty_Wrap (ty_def nat (GTy_ext Ty) tye c)) ->
      exists tye' : GTy_ext Ty, ty' =  FJ_Ty_Wrap (ty_def nat (GTy_ext Ty) tye' c) :=
        match bound in Bound gamma ty ty' return (forall (tye : GTy_ext Ty) (c : cFJ.CL nat),
          ty = (FJ_Ty_Wrap (ty_def nat (GTy_ext Ty) tye c)) ->
          exists tye' : GTy_ext Ty, ty' =  FJ_Ty_Wrap (ty_def nat (GTy_ext Ty) tye' c)) with 
          | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_WF_fields_map_id' nat Ty _ Gty _ _ N_Wrap
            cFJ_N _ TLookup Ty_Wrap_discriminate gamma' ty'' ty''' GJ_bound'
          | N_Bound gamma' ty'' ty''' FJ_bound' => N_WF_fields_map_id' _ _ _ _ N_Wrap cFJ_N _ 
            gamma' ty'' ty''' FJ_bound'
        end.

  Definition WF_fields_map_id_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall tye c tye' fds' fds'', cl' = FJ_Ty_Wrap (ty_def nat ty_ext tye c) -> fds'' = fds -> 
      fields gamma (FJ_Ty_Wrap (ty_def nat ty_ext tye' c)) fds' -> 
      map (fun fd' => match fd' with fd _ f => f end) fds' = 
      map (fun fd' => match fd' with fd _ f => f end) fds.
  
  Fixpoint WF_fields_map_id gamma ty fds (fields_fds : fields gamma ty fds) :
    WF_fields_map_id_def _ _ _ fields_fds :=
    match fields_fds return WF_fields_map_id_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fields_map_id _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert
      Fields_Build_tys_len  _ _ _ FJ_case WF_fields_map_id
    end.

  Definition parent_fields_names_eq_P := 
    cFJ.parent_fields_names_eq_P _ nat _ _ FJ_Ty_Wrap Context fields.

  Fixpoint parent_fields_names_eq gamma ty fds (fields_fds : fields gamma ty fds) : 
    parent_fields_names_eq_P _ _ _ fields_fds :=
    match fields_fds return parent_fields_names_eq_P _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_parent_fields_names_eq _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields cFJ_inject fields_invert 
      Fields_Build_tys_len _ _ _ FJ_case parent_fields_names_eq
    end.

  Fixpoint fds_distinct gamma ty fds (fields_fds : fields gamma ty fds) : fds_distinct_def _ _ _ fields_fds :=
    match fields_fds return fds_distinct_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fds_distinct _ _ _ _ _ Ty FJ_Ty_Wrap _ _ _ CT Context
      subtype WF_Type fields fields_build_te fields_build_tys FJ_fields E_WF Empty Update
      ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
      WF_CT parent_fields_names_eq Fields_Build_tys_len _ _ _ FJ_case fds_distinct
    end.

  Definition Weakening_def e ty gamma (WF_e : E_WF gamma e ty) :=
    forall gamma' vars, gamma = (update_list Empty vars) -> E_WF (update_list gamma' vars) e ty.

  Fixpoint Weaken_Subtype_update_list gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T return cFJ.Weaken_Subtype_update_list_P nat _ _ subtype Empty Update _ _ _ sub_S_T with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_Weaken_Subtype_update_list _ _ _ _ _ _ 
        _ _ _ _ CT _ subtype build_te cFJ_sub Empty Update _ _ _ sub_S_T' Weaken_Subtype_update_list
      | GJ_sub gamma S' T' sub_S_T' => GJ_Weaken_Subtype_update_list _ _ Gty N _ _ Empty TLookup
        subtype GJ_sub nat Update TLookup_Update TLookup_Empty _ _ _ sub_S_T'
      | I_subtype_Wrap gamma S' T' sub_S_T' => I_Weaken_Subtype_update_list _ _ _ I_Ty_Wrap _ _ _ _ _ _ _ _ 
        CT isub_build_te implements FJ_Ty_Wrap subtype I_subtype_Wrap Empty Update 
        gamma S' T' sub_S_T'
    end.

  Definition Weaken_WF_Object_Ext := Generic.Weaken_WF_Object_Ext _ _ Empty _ Update unit.
  
  Section wf_class_ext_recursion.
    
    Definition map_List_P1 := fun (A : Type) (P Q : A -> Prop) (Map_P : forall a, P a -> Q a) => 
      fix map (As : list A) (PAs : List_P1 P As) : List_P1 Q As :=
      match PAs in (List_P1 _ As'') return List_P1 Q As'' with
        Nil => Nil Q
        | Cons_a a As' Pa PAs' => Cons_a Q a As' (Map_P a Pa) (map As' PAs')
      end.

    Variables (P : forall gamma ty, WF_Type gamma ty -> Prop)
      (Q' : forall gamma cld ty,
        @GJ_wf_class_ext nat Ty N N_Wrap Context subtype
        Ty_trans WF_Type I_cld_ext unit gamma cld ty -> Prop)
      (Q'_P1 : forall gamma tys, List_P1 (WF_Type gamma) tys -> Prop)
      (Q'' : forall (gamma : Context) (int : _) (ty : ty_ext), 
        wf_int_ext gamma int ty -> Prop).
    
    Hypothesis (H1 : forall gamma ce tys typs te P1 len P2, 
      Q'_P1 gamma tys P1 -> 
      Q' _ _ _ (@Generic.wf_class_ext nat Ty N _ Context subtype
        Ty_trans WF_Type _ unit ce gamma typs tys te
        P1 len P2))
    (H2 : forall gamma, Q'_P1 gamma _ (Nil (WF_Type gamma)))
    (H3 : forall gamma ty tys P_ty P_tys, P _ _ P_ty -> Q'_P1 _ tys P_tys -> 
      Q'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys))
    (H4 : forall ie delta typs tys te P1 len P2, 
      Q'_P1 delta tys P1 -> 
      (Q'' _ _ _ (i_wf_int_ext _ _ _ _ _ _ _ _ ie delta typs tys te P1 len P2))).
    
    Definition wf_class_ext_rect (WF_type_rect : forall gamma ty wf_ty, P gamma ty wf_ty) 
      gamma cld te (wf_te : wf_class_ext gamma cld te) : Q' _ _ _ wf_te :=
      match wf_te return  Q' _ _ _ wf_te with
        Generic.wf_class_ext ce gamma typs tys te P1 len P2 => 
        H1 gamma ce tys typs te P1 len P2 
        ((fix map (As : list Ty) (PAs : List_P1 (WF_Type gamma) As) : Q'_P1 _ _ PAs :=
          match PAs return Q'_P1 _ _ PAs with
            Nil => H2 gamma
            | Cons_a a As' Pa PAs' => H3 gamma a As' Pa PAs'
              (WF_type_rect _ a Pa) (map As' PAs')
          end) tys P1)
      end.

    Definition wf_int_ext_rect (WF_type_rect : forall gamma ty wf_ty, P gamma ty wf_ty) 
      gamma int te (wf_te : wf_int_ext gamma int te) : Q'' _ _ _ wf_te :=
      match wf_te return  Q'' _ _ _ wf_te with
        i_wf_int_ext ie delta typs tys te P1 len P2 => 
        H4 ie delta typs tys te P1 len P2 
        ((fix map (As : list Ty) (PAs : List_P1 (WF_Type delta) As) : Q'_P1 _ _ PAs :=
          match PAs return Q'_P1 _ _ PAs with
            Nil => H2 delta
            | Cons_a a As' Pa PAs' => H3 delta a As' Pa PAs'
              (WF_type_rect _ a Pa) (map As' PAs')
          end) tys P1)
      end.

    Variable (H5 : forall gamma ty (wf_ty : (Generic.GJ_WF_Type nat Ty Gty N Context TLookup gamma ty)), 
      P gamma ty (GJ_WF_Type _ _ wf_ty)).

    Fixpoint WF_Type_rect' H1 H2 H3 gamma ty wf_ty : P gamma ty wf_ty := 
      match wf_ty return P _ _ wf_ty with 
        | cFJ_WF_Type gamma' ty' wf_ty' => 
          FJ_WF_Type_rect' nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
          wf_class_ext wf_object_ext WF_Type cFJ_WF_Type P Q' H1 H2
          (wf_class_ext_rect (WF_Type_rect' H1 H2 H3)) gamma' ty' wf_ty' 
        | GJ_WF_Type gamma ty wf_ty => H5 _ _ wf_ty
        | I_WF_Type_Wrap gamma ty wf_ty => I_WF_Type_rect' nat ty_ext Ty  
          I_Ty_Wrap mty_ext nat nat _ Context IT (wf_int_ext' WF_Type) WF_Type 
          I_WF_Type_Wrap P Q'' H3 (wf_int_ext_rect (WF_Type_rect' H1 H2 H3)) gamma ty wf_ty
      end.

  End wf_class_ext_recursion.

  Fixpoint Weaken_WF_Type_update_list gamma ty (WF_ty : WF_Type gamma ty) :
    FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty :=
    match WF_ty in WF_Type gamma ty return FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty with 
      | cFJ_WF_Type gamma' ty' wf_ty' => 
        FJ_Weaken_WF_Type_update_list nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type cFJ_WF_Type Empty Update Weaken_WF_Object_Ext
        (Weaken_WF_Type_update_list_ext nat Ty N _ _ Empty subtype Ty_trans WF_Type
          _ _ _ _ Weaken_Subtype_update_list Weaken_WF_Type_update_list) gamma' ty' wf_ty'
      | GJ_WF_Type gamma' ty' wf_ty' => 
        GJ_Weaken_WF_Type_update_list _ _ _ _ _ _ _ _ GJ_WF_Type nat Update
        TLookup_Update TLookup_Update' TLookup_Empty _ _ wf_ty'
      | I_WF_Type_Wrap gamma' ty' wf_ty' => I_Weaken_WF_Type_update_list _ _ _ I_Ty_Wrap
        _ _ _ _ _ IT _ WF_Type I_WF_Type_Wrap Empty Update
        (wf_int_ext_rect _ _ (Weaken_WF_Int_Ext_Q _ _ _ _ _ _ _ _) 
          (Weaken_WF_Type_update_list_H2 _ _ _ _ _ _)
          (Weaken_WF_Type_update_list_H3 _ _ _ _ _ _)
          (I_Weaken_WF_update_list_ext _ _ _ _ _ _ _ _ _ _ _ _ _ Weaken_Subtype_update_list) 
        Weaken_WF_Type_update_list)
        _ _ wf_ty'
    end.
  
  Variables 
    (lookup_update_eq : forall gamma X ty, lookup (Update gamma X ty) X ty) 
    (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
      lookup (Update gamma Y ty') X ty)
    (lookup_update_neq' : forall gamma Y X ty ty', lookup (Update gamma Y ty') X ty -> X <> Y -> 
      lookup gamma X ty)
    (lookup_Empty : forall X ty, ~ lookup Empty X ty)
    (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty').

  Definition WF_mtype_ty_0_map := Bound.
  Definition WF_fields_map := Bound.

  Definition Weaken_WF_fields_map gamma ty ty' (bound : Bound gamma ty ty') :=
    match bound in Bound gamma ty ty' return (forall (gamma' : Context) (vars : list (Var nat * Ty)),
      gamma = Generic.update_list Ty Context nat Update Empty vars ->
      Bound (Generic.update_list Ty Context nat Update gamma' vars) ty ty')
      with 
      | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_Weaken_WF_fields_map nat Ty Gty _ N_Wrap
        _ Empty TLookup _ Update TLookup_Update TLookup_Update' TLookup_Empty Bound GJ_Bound
        gamma' ty'' ty''' GJ_bound'
      | N_Bound gamma' ty'' ty''' FJ_bound' => FJ_Weaken_WF_fields_map Ty _ N_Wrap _ Empty _ 
        Update Bound N_Bound gamma' ty'' ty''' FJ_bound'
    end.

  Definition Weaken_WF_fields_map' gamma vars ty ty' bnd :=
    Weaken_WF_fields_map _ ty ty' bnd gamma vars (refl_equal _).

  Definition Weaken_WF_mtype_Us_map := 
    Generic.Weaken_WF_mtype_Us_map _ _ N _ Empty Ty_trans _ Update _ _
    (FJ_WF_mtype_Us_map Ty Context) 
    (fun mce mtye tys tys' vars gamma => FJ_Weaken_WF_mtype_Us_map _ _ _ Empty Update gamma vars mce tys tys' mtye).
  
  Definition Weaken_WF_mtype_U_map := 
    Generic.Weaken_WF_mtype_U_map _ _ N _ Empty Ty_trans _ Update _ _
    (FJ_WF_mtype_U_map Ty Context) 
    (fun gamma vars mce U U' mtye => FJ_Weaken_WF_mtype_U_map _ _ _ Empty Update gamma vars mce U U' mtye).
  
  Definition Weaken_WF_mtype_ext := 
    Generic.Weaken_WF_mtype_ext nat Ty N N_Wrap _ Empty subtype Ty_trans
    WF_Type _ Update Weaken_Subtype_update_list Weaken_WF_Type_update_list unit unit
    (FJ_WF_mtype_ext Context) (FJ_Weaken_WF_mtype_ext _ _ _ Empty Update).

  Variable Ty_eq_dec : forall (S T : Ty), {S = T} + {S <> T}.
  Variable subtype_dec : forall gamma S T, subtype gamma S T \/ ~ subtype gamma S T.
  
  Fixpoint Weakening gamma e ty (WF_e : E_WF gamma e ty) : Weakening_def _ _ _ WF_e :=
    match WF_e return Weakening_def _ _ _ WF_e with
      | FJ_E_WF gamma e ty FJ_case => FJ_Weakening _ _ _ _ _ _ _ _ _ cFJ_E _ _
        subtype WF_Type fields mtype
        E_WF lookup Bound Bound WF_mtype_Us_map WF_mtype_U_map
        WF_mtype_ext Empty FJ_E_WF Update eq_nat_dec lookup_update_eq
        lookup_update_neq lookup_update_neq' lookup_Empty lookup_id Weaken_WF_fields_map'
        Weaken_WF_fields_map' Weaken_WF_mtype_Us_map Weaken_WF_mtype_U_map
        Weaken_Subtype_update_list Weaken_WF_mtype_ext Weaken_WF_Type_update_list _ _ _ 
        FJ_case Weakening
      | Cast_E_WF gamma e ty Cast_case => 
        Cast_Weakening _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ Cast_E
        E_WF Bound subtype Cast_E_WF _ _ _ _ _ CT build_te Empty Update cFJ_sub
        Weaken_Subtype_update_list subtype_dec Ty_eq_dec Weaken_WF_fields_map' gamma e ty Cast_case Weakening
    end.

  Lemma E_trans_Wrap : forall e vars es', 
    trans (cFJ_E e) vars es' = cFJ.FJ_E_trans _ _ _ _ _ _ _ cFJ_E trans eq_nat_dec e vars es'.
    simpl; reflexivity.
  Qed.
  
  Definition WF_mtype_ty_0_map_Weaken_update_list delta T T' (Bnd : Bound delta T T') :=
    match Bnd in (Bound delta T T') return (forall delta' vars, delta = update_list delta' vars -> 
      Bound delta' T T') with
      | GJ_Bound delta T T' GJ_Bound' => Generic.GJ_Bound_Weaken_update_list _ _ Gty _ N_Wrap _ TLookup _ Update
        TLookup_Update Bound GJ_Bound delta T T' GJ_Bound'
      | N_Bound delta T T' N_Boun' => Generic.N_Bound_Weaken_update_list _ _ N_Wrap _ _ Update Bound N_Bound
        delta T T' N_Boun'
    end.
  
  Definition WF_mtype_U_map_Weaken_update_list := 
    GJ_WF_mtype_U_map_Weaken_update_list _ _ N _ Ty_trans _ Update _ _
    id_map_3 (fun gamma vars mce U U' mtye => 
      FJ_WF_mtype_U_map_Weaken_update_list _ _ _ Update gamma vars mce mtye U U').
  
  Definition WF_mtype_Us_map_Weaken_update_list := 
    GJ_WF_mtype_Us_map_Weaken_update_list _ _ N _ Ty_trans _ Update _ _
    id_map_3 (fun mce mtye tys tys' vars gamma => 
      FJ_WF_mtype_Us_map_Weaken_update_list _ _ _ Update gamma vars mce mtye tys tys').
  
  Definition Bound_total_def gamma S T (sub_S_T : subtype gamma S T) :=
    forall T', Bound gamma T T' -> exists S' , Bound gamma S S'.

  Fixpoint WF_mtype_ty_0_map_total gamma S T (sub_S_T : subtype gamma S T) := 
    match sub_S_T in subtype gamma S T return Bound_total_def gamma S T sub_S_T with
      | cFJ_sub gamma' S' T' sub_S_T' => 
        FJ_Bound_total _ _ _ _ _ _ _ subtype _ _ _ _ Bound N_Bound _ _ CT 
        build_te cFJ_sub WF_mtype_ty_0_map_total gamma' S' T' sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Bound_total _ _ _ _ _ _ TLookup subtype GJ_sub Bound GJ_Bound gamma' S' T' sub_S_T'
      | I_subtype_Wrap gamma' S' T' sub_S_T' => 
        I_Bound_total _ _ _ _ _ _ _ _ subtype N_Wrap I_N_Wrap _ _ cFJ_N Bound N_Bound _ _ _ CT _
        I_subtype_Wrap gamma' S' T' sub_S_T'  
    end.
  
  Fixpoint Subtype_Update_list_id gamma S T (sub_S_T : subtype gamma S T) := 
    match sub_S_T with
      | cFJ_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Update_list_id _ _ _ _ _ _ _ _ _ _ CT _ subtype build_te
        cFJ_sub Update gamma' S' T' sub_S_T' Subtype_Update_list_id
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Subtype_Update_list_id _ _ Gty N _ _ TLookup _ GJ_sub _ Update
        TLookup_Update gamma' S' T' sub_S_T'
      | I_subtype_Wrap gamma S' T' sub_S_T' => 
        I_Subtype_Update_list_id _ _ _ I_Ty_Wrap _ _ _ _ _ _ _ _ CT isub_build_te
        implements _ subtype I_subtype_Wrap Update gamma S' T' sub_S_T'
    end.
  
  Definition WF_Object_ext_Update_Vars_id := 
    GJ_WF_Object_ext_Update_Vars_id _ _ _ Update unit.

  Fixpoint WF_Type_update_list_id gamma ty (WF_ty : WF_Type gamma ty) :
    cFJ.WF_Type_update_list_id_P _ _ _ WF_Type Update gamma ty WF_ty :=
    match WF_ty in WF_Type gamma ty return cFJ.WF_Type_update_list_id_P _ _ _ WF_Type Update gamma ty WF_ty with 
      | cFJ_WF_Type gamma' ty' wf_ty' => 
        FJ_WF_Type_update_list_id nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type cFJ_WF_Type Update WF_Object_ext_Update_Vars_id
        (WF_Type_update_list_id_ext nat Ty N _ _ subtype Ty_trans WF_Type
          nat Update _ _  Subtype_Update_list_id WF_Type_update_list_id) gamma' ty' wf_ty'
      | GJ_WF_Type gamma' ty' wf_ty' => 
        GJ_WF_Type_update_list_id _ _ Gty N _ TLookup WF_Type GJ_WF_Type _ Update 
        TLookup_Update _ _ wf_ty'
      | I_WF_Type_Wrap _ _ wf_ty' => I_WF_Type_update_list_id _ _ _ _ _ _ _ _ _ IT
        wf_int_ext _ I_WF_Type_Wrap Update 
        (wf_int_ext_rect _ _ (WF_int_ext_Update_Vars_id_Q _ _ _ _ _ _ _)
          (WF_Type_update_list_id_H2 _ _ _ _ _)
          (WF_Type_update_list_id_H3 _ _ _ _ _)
          (WF_int_ext_update_list_id _ _ _ _ _ WF_Type subtype
            Ty_trans N_Wrap Update _ _ Subtype_Update_list_id) WF_Type_update_list_id) _ _ wf_ty'
   end.
  
  Definition WF_fields_map_tot := FJ_WF_fields_map_tot _ _ _ FJ_Ty_Wrap Context.
  
  Fixpoint fields_id gamma ty fds (ty_fields : fields gamma ty fds) := 
    match ty_fields with 
      | FJ_fields gamma' ty' fds' FJ_ty'_fields =>
        FJ_fields_id _ _ _ _ _ _ _ _ _ _ CT Context fields fields_build_te 
        fields_build_tys FJ_fields cFJ_inject fields_invert  
        fields_build_te_id fields_build_tys_id  gamma' ty' fds' FJ_ty'_fields fields_id
    end.
  
  Definition WF_mtype_ext_update_list_id := FJ_WF_mtype_ext_update_list_id _ _ _ Update.
  
  Definition WF_mtype_ty_0_map_tot := FJ_WF_mtype_ty_0_map_tot Ty Context.
  
  Definition WF_mtype_ty_0_map_cl_id := 
    FJ_WF_mtype_ty_0_map_cl_id _ _ _ _ Context cFJ_inject.
  
  Definition WF_mtype_ty_0_map_cl_id' := 
    FJ_WF_mtype_ty_0_map_cl_id' _ _ _ FJ_Ty_Wrap Context. 
  
  Definition m_eq_dec := eq_nat_dec.
    
  Definition WF_mtype_Us_map_len := FJ_WF_mtype_Us_map_len Ty Context.
  
  Definition mtype_build_tys_len (ce : I_cld_ext) := FJ_mtype_build_tys_len nat Ty (snd ce).
  
  Definition methods_build_te_id := FJ_methods_build_te_id.
  
  Definition WF_Type_par_Lem_P := cFJ.WF_Type_par_Lem_P
    _ _ _ _ ty_ext Ty FJ_Ty_Wrap _ _ _ CT Context 
    wf_object_ext WF_Type mtype_build_te L_build_context.
  
   Lemma Ty_discriminate : forall ty ty', FJ_Ty_Wrap ty <> I_Ty_Wrap ty'.
     unfold FJ_Ty_Wrap; unfold Generic.FJ_Ty_Wrap; unfold I_Ty_Wrap; intros.
     congruence.
   Qed.

  Fixpoint WF_Type_par_Lem gamma ty (WF_ty : WF_Type gamma ty) :=
    match WF_ty return WF_Type_par_Lem_P _ _ WF_ty with 
      | cFJ_WF_Type gamma ty WF_base => 
        FJ_WF_Type_par_Lem _ _ _ _ _ _ _ _ _ _ CT Context wf_class_ext
        wf_object_ext WF_Type cFJ_WF_Type mtype_build_te
        L_build_context cFJ_inject 
        (fun g g0 te0 te' te'' ce _ _ _ _ _ mty wf_obj _ _ => 
          WF_Obj_ext_Lem _ Ty N _ Ty_trans I_cld_ext _ 
          (fun ice te te' te'' => FJ_mtype_build_te (snd ice) te te' te'')
            g g0 te0 te' te'' ce wf_obj mty) gamma ty WF_base
      | GJ_WF_Type gamma ty WF_ty => (fun g te0 te' te'' ce _ _ _ _ _ _ mty wf_obj _ => 
        WF_Obj_ext_Lem _ Ty N _ Ty_trans I_cld_ext _ 
        (fun ice te te' te'' => FJ_mtype_build_te (snd ice) te te' te'')
        gamma g te0 te' te'' ce wf_obj mty)
      | I_WF_Type_Wrap gamma ty WF_int => 
        I_WF_Type_par_Lem _ _ _ I_Ty_Wrap _ _ _ _ _ IT _ _ _ _ _ CT
        FJ_Ty_Wrap wf_int_ext WF_Type I_WF_Type_Wrap wf_object_ext 
        mtype_build_te L_build_context Ty_discriminate gamma ty WF_int
    end.
  
  Definition WF_Type_par_Lem_P' := 
    cFJ.WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty  FJ_Ty_Wrap E _ _ CT Context wf_class_ext
    WF_Type mtype_build_te L_build_context.

  Fixpoint Weakening_2_1_1 delta S T (sub_S_T : subtype delta S T) : 
    (Weakening_2_1_1_P _ _ subtype app_context _ _ _ sub_S_T) :=
    match sub_S_T return (Weakening_2_1_1_P _ _ subtype app_context _ _ _ sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => 
        Weakening_2_1_1_FJ Ty ty_ext nat N N_Wrap cFJ_N _ subtype _ _ _ app_context
        E _ _ CT build_te cFJ_sub Weakening_2_1_1 delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => Weakening_2_1_1_GJ _ _ Gty _ _ _ TLookup
        subtype GJ_sub app_context TLookup_app delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => 
        I_Weakening_2_1_1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CT _ I_subtype_Wrap _ _ _ sub_S_T'
    end.


  Definition Weakening_2_1_2 :=
    WF_Type_rect' (Weakening_2_1_2_P _ _ WF_Type app_context) 
    (Weakening_2_1_2_Q _ _ _ _ _ subtype Ty_trans WF_Type
      app_context _ _)
    (Weakening_2_1_2_P1 _ _ WF_Type app_context)
    (Weakening_2_1_2_Q'' _ _ _ wf_int_ext app_context)
    (Weakening_2_1_2_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type app_context _ _ Weakening_2_1_1)
    (Weakening_2_1_2_ext_H2 _ _ WF_Type app_context)
    (Weakening_2_1_2_ext_H3 _ _ WF_Type app_context)
    (I_Weakening_2_1_2_ext _ _ _ _ WF_Type subtype _ _ _ _ _ Weakening_2_1_1)
    (GJ_Weakening_2_1_2 _ _ Gty _ _ TLookup WF_Type GJ_WF_Type app_context TLookup_app)
    (FJ_Weakening_2_1_2_H1 _ _ _ _ _ _ _ WF_Type nat nat nat app_context E _ _ CT
      wf_class_ext wf_object_ext (Weakening_2_1_2_obj_ext _ _ app_context _) cFJ_WF_Type)
    (FJ_Weakening_2_1_2_H2 _ _ _ _ _ _ _ WF_Type _ _ _ app_context E _ _ CT wf_class_ext
      wf_object_ext cFJ_WF_Type)
    (I_Weakening_2_1_2 _ _ _ _ _ _ _ _ _ WF_Type _ N_Wrap I_N_Wrap _ _ I_WF_Type_Wrap).

  Definition WF_Bound_app_Weaken := GJ_WF_Bound_app_Weaken _ _ Gty _
    _ TLookup app_context TLookup_app.
  
  Definition WF_mtype_Us_map_app_Weaken := 
    GJ_WF_mtype_Us_map_app_Weaken _ _ N Context Ty_trans _ app_context _ _
    (FJ_WF_mtype_Us_map_app_Weaken _ _ app_context).
  
  Definition WF_mtype_U_map_app_Weaken := 
    GJ_WF_mtype_U_map_app_Weaken _ _ N Context Ty_trans _ app_context _ _
    (FJ_WF_mtype_U_map_app_Weaken _ _ app_context).
  
  Definition WF_mtype_ext_app_Weaken := 
    Generic.GJ_WF_mtype_ext_app_Weaken _ _ _ N_Wrap _ 
    subtype Ty_trans WF_Type _ app_context
    Weakening_2_1_1 Weakening_2_1_2 _ _ (FJ_WF_mtype_ext_app_Weaken _ app_context).

  Definition WF_Bound_app_Weaken' (gamma : Context) (ty ty' : Ty) (Bnd : Bound gamma ty ty') :=
    match Bnd in (Bound gamma ty ty') return (forall gamma', Bound (app_context gamma gamma') ty ty') with
      | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_WF_Bound_app_Weaken' _ _ Gty _ N_Wrap _ TLookup
        app_context TLookup_app Bound GJ_Bound gamma' ty'' ty''' GJ_bound'
      | N_Bound gamma' ty'' ty''' FJ_bound' => N_WF_Bound_app_Weaken' _ _ N_Wrap _ app_context
        Bound N_Bound gamma' ty'' ty''' FJ_bound'
    end.
  
  Fixpoint Weakening_2_1_3_1 delta e T (WF_e : E_WF delta e T) :
    Generic.Weakening_2_1_3_1_P Ty Context app_context E E_WF delta e T WF_e :=
    match WF_e in E_WF delta e T return Generic.Weakening_2_1_3_1_P _ _ app_context _ E_WF delta e T WF_e with 
      | FJ_E_WF gamma e ty FJ_case => Generic.Weakening_2_1_3_1 _ _ _ N N_Wrap _ _ Empty subtype
        WF_Type _ fields _ _ _ mtype app_context _ Weakening_2_1_1
        Weakening_2_1_2 _ cFJ_E E_WF lookup Bound WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Bound Lookup_app FJ_E_WF 
        (fun g g' ty ty' bnd => WF_Bound_app_Weaken' g ty ty' bnd g')
        (fun g g' ty ty' bnd => WF_Bound_app_Weaken' g ty ty' bnd g') WF_mtype_Us_map_app_Weaken
        WF_mtype_U_map_app_Weaken WF_mtype_ext_app_Weaken Weakening_2_1_3_1 gamma e ty FJ_case
      | Cast_E_WF gamma e ty Cast_case => Generic_Cast.Weakening_2_1_3_1 _ _ _ _ _ _ _ _ _ _ Cast_E _ app_context
        E_WF Bound subtype Cast_E_WF WF_Bound_app_Weaken' Weakening_2_1_1 subtype_dec Ty_eq_dec _ _ CT
        build_te cFJ_sub gamma e ty Cast_case Weakening_2_1_3_1
    end.
  
  Inductive Free_Vars : Ty -> list nat -> Prop :=
  | GJ_Free_Vars' : forall ty txs, GJ_Free_Vars _ _ Gty ty txs -> Free_Vars ty txs
  | FJ_Free_Vars' : forall ty txs, FJ_Free_Vars _ _ _ nat N N_Wrap cFJ_N
    (GJ_TE_Free_Vars _ _ _ Free_Vars) ty txs -> Free_Vars ty txs
  | I_Free_Vars' : forall ty txs, I_Free_Vars _ _ _ _ _ N_Wrap I_N_Wrap
    (GJ_TE_Free_Vars _ _ _ Free_Vars) ty txs -> Free_Vars ty txs.
  
  Definition TE_Free_Vars := (GJ_TE_Free_Vars _ _ unit Free_Vars).
  
  Lemma GJ_Free_Vars_invert : forall ty txs, Free_Vars (Gty ty) txs -> GJ_Free_Vars _ _ Gty (Gty ty) txs.
    intros; inversion H; subst; first [apply H0 | inversion H0].
  Qed.
  
  Lemma FJ_Free_Vars_invert : forall ty txs, Free_Vars (FJ_Ty_Wrap ty) txs -> 
    FJ_Free_Vars _ _ _ nat N N_Wrap cFJ_N (GJ_TE_Free_Vars _ _ _ Free_Vars) (FJ_Ty_Wrap ty) txs.
    intros; inversion H; subst; first [apply H0 | inversion H0].
  Qed.
  
  Lemma GJ_Ty_Wrap_inject : forall ty ty', Gty ty = Gty ty' -> ty = ty'.
    intros; congruence.
  Qed.
  
  Lemma FJ_Ty_Wrap_inject : forall ty ty', FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty'.
    unfold FJ_Ty_Wrap; unfold Generic.FJ_Ty_Wrap; congruence.
  Qed.
  
  Lemma GTy_ext_Wrap_inject : forall (te te' : ty_ext) , id te = id te' -> te = te'.
    unfold id; auto.
  Qed.
  
  Definition TE_trans := (GJ_TE_Trans _ _ Ty_trans unit).
      
  Section Ty_recursion.

    Variables
      (P : Ty -> Type)
      (Q : ty_ext -> Type).

    Hypotheses
      (H1 : forall X, P (Gty (TyVar _ X)))
      (H2 : forall te cl, Q te -> P (FJ_Ty_Wrap (ty_def _ _ te cl)))
      (H3 : forall te cl, Q te -> P (I_Ty_Wrap (ity_def _ _ te cl)))
      (H4 : forall te, Q (nil, te))
      (H5 : forall ty tys te, Q (tys, te) -> P ty -> Q (ty :: tys, te)).

    Fixpoint ty_rect (ty : Ty) : P ty :=
      match ty with
        | Gty (TyVar X) => H1 X
        | N_Wrap (cFJ_N (ty_def (tys, te) c)) => H2 (tys, te) c 
          ((fix tys_rect tys : Q (tys, te) :=
            match tys return Q (tys, te) with
              | nil => H4 te
              | ty :: tys' => H5 ty tys' te (tys_rect tys') (ty_rect ty)
            end) tys)
        | N_Wrap (I_N_Wrap (ity_def (tys, te) i)) => H3 (tys, te) i 
          ((fix tys_rect tys : Q (tys, te) :=
            match tys return Q (tys, te) with
              | nil => H4 te
              | ty :: tys' => H5 ty tys' te (tys_rect tys') (ty_rect ty)
            end) tys)
      end.

  End Ty_recursion.

  Lemma FJ_Ty_trans_invert : forall ty txs tys,
    Ty_trans (FJ_Ty_Wrap ty) txs tys = FJ_Ty_Trans _ _ _ _ _ FJ_Ty_Wrap id TE_trans ty txs tys.
    reflexivity.
  Qed.

  Lemma GJ_Ty_trans_invert : 
    forall ty Xs Us, Ty_trans (Gty ty) Xs Us = GTy_trans nat eq_nat_dec Ty Gty ty Xs Us.
    reflexivity.
  Qed.

  Lemma I_Ty_trans_invert : 
    forall ty txs tys, Ty_trans (I_Ty_Wrap ty) txs tys = I_Ty_Trans _ _ _ _ _ N_Wrap I_N_Wrap TE_trans ty txs tys.
    reflexivity.
  Qed.

  Lemma GJ_TE_Trans_invert : forall (te : GTy_ext Ty) (Ys : list nat)
    (Us : list Ty), TE_trans (id te) Ys Us = id (GJ_TE_Trans nat Ty Ty_trans _ te Ys Us).
    reflexivity.
  Qed.

  Definition Ty_trans_nil :=
    ty_rect (Ty_trans_nil_P _ _ Ty_trans)
    (TE_trans_nil_P _ _ _ TE_trans)
    (GJ_Ty_trans_nil _ eq_nat_dec _ Gty _ GJ_Ty_trans_invert)
    (FJ_Ty_trans_nil _ _ _ _ N N_Wrap cFJ_N Ty_trans TE_trans 
      FJ_Ty_trans_invert)
    (I_Ty_trans_nil _ _ _ _ _ _ _ _ _ I_Ty_trans_invert)
    (TE_trans_nil_H1 _ _ _ _ _ id _ GJ_TE_Trans_invert)
    (TE_trans_nil_H2 _ _ _ _ _ id _ (fun _ _ => id) GJ_TE_Trans_invert).

  Definition Ty_trans_nil' :=
    ty_rect (Ty_trans_nil'_P _ _ Ty_trans)
    (TE_trans_nil'_P _ _ _ TE_trans)
    (GJ_Ty_trans_nil' _ eq_nat_dec _ Gty _ GJ_Ty_trans_invert)
    (FJ_Ty_trans_nil' _ _ _ _ N N_Wrap cFJ_N Ty_trans TE_trans 
      FJ_Ty_trans_invert)
    (I_Ty_trans_nil' _ _ _ _ _ _ _ _ _ I_Ty_trans_invert)
    (TE_trans_nil'_H1 _ _ _ _ _ id _ GJ_TE_Trans_invert)
    (TE_trans_nil'_H2 _ _ _ _ _ id _ (fun _ _ => id) GJ_TE_Trans_invert).
    
  Definition Free_Vars_Subst_P (ty : Ty) := 
    forall (Xs Ys : list nat) (Us : list Ty),
      (forall X, In X Xs -> ~ In X Ys) -> Free_Vars ty Xs -> Ty_trans ty Ys Us = ty.
  
  Definition Free_Vars_Subst_Q (te : ty_ext) :=
    forall Ys Us Xs, 
      (forall X : nat, In X Xs -> ~ In X Ys) -> TE_Free_Vars te Xs -> TE_trans te Ys Us = te.
    
  Lemma GJ_TE_Free_Vars_invert : forall (te : GTy_ext Ty) (txs : list nat),
    TE_Free_Vars (id te) txs -> GJ_TE_Free_Vars _ Ty _ Free_Vars te txs.
    unfold id; unfold TE_Free_Vars; auto.
  Qed.

  Lemma I_Ty_Wrap_inject : forall ty ty' , I_Ty_Wrap ty = I_Ty_Wrap ty' -> ty = ty'.
    unfold I_Ty_Wrap; intros; injection H; auto.
  Qed.

  Lemma I_Free_Vars_invert : forall (ty : I_Ty _ _) (txs : list _),
    Free_Vars (I_Ty_Wrap ty) txs ->
    I_Free_Vars _ _ _ ty_ext _ N_Wrap I_N_Wrap TE_Free_Vars (I_Ty_Wrap ty) txs.
    intros; inversion H; inversion H0; subst; assumption.
  Qed.

  Definition Free_Vars_Subst :=
    ty_rect Free_Vars_Subst_P Free_Vars_Subst_Q
    (Free_Vars_Subst_H1 _ eq_nat_dec _ Gty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject)
    (Free_Vars_Subst_H2 _ _ _ _ N N_Wrap cFJ_N FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert
      TE_trans)
    (I_Free_Vars_Subst _ _ _ _ _ _ _ _ _ _ I_Free_Vars_invert I_Ty_Wrap_inject)
    (Free_Vars_Subst_H3 _ _ _ Ty_trans _ TE_Free_Vars id)
    (Free_Vars_Subst_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert 
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).
  
  Definition map_Ty_trans_P := map_Ty_trans_P _ _ N Ty_trans Free_Vars.
  
  Definition map_Ty_trans_Q := map_Ty_trans_Q _ _ _ N Ty_trans TE_Free_Vars TE_trans.
  
  Lemma NIn_Ty_trans : forall X Xs Us, ~In X Xs -> Ty_trans (Gty (TyVar _ X)) Xs Us = Gty (TyVar _ X).
    simpl; eapply (GNIn_Ty_trans _ eq_nat_dec Ty Gty _ _ Empty build_fresh TUpdate).
  Qed.
    
  Lemma Ty_trans_FJ : forall ty Xs Us, Ty_trans (FJ_Ty_Wrap ty) Xs Us = 
    FJ_Ty_Trans _ _ _ _ _  FJ_Ty_Wrap id TE_trans ty Xs Us.
    simpl; reflexivity.
  Qed.

  Definition map_Ty_trans :=
    ty_rect map_Ty_trans_P map_Ty_trans_Q
    (map_Ty_trans_H1 _ eq_nat_dec _ Gty _ Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject NIn_Ty_trans)
    (map_Ty_trans_H2 _ _ _ _ N N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars 
      FJ_Free_Vars_invert TE_trans Ty_trans_FJ)
    (I_map_Ty_trans _ _ _ _ _ _ N_Wrap I_N_Wrap _ _ _ I_Free_Vars_invert I_Ty_trans_invert I_Ty_Wrap_inject)
    (map_Ty_trans_H3 _ _ _ _ Ty_trans _ TE_Free_Vars id)
    (map_Ty_trans_H4 _ _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert 
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).
  
  Definition map_Ty_trans_P' ty := 
    forall (Xs Ys : list _) (Us tys : list Ty) (typs : TyP_List),
      Free_Vars ty Ys -> length typs = length tys -> 
      (forall X : _, In X Ys -> In X (Extract_TyVar _ _ typs)) ->
      Ty_trans (Ty_trans ty (Extract_TyVar _ _ typs) tys) Xs Us =
      Ty_trans ty (Extract_TyVar _ _ typs)
      (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
  
  Definition map_Ty_trans_Q' te := forall Xs Ys Us tys typs,
    TE_Free_Vars te Ys -> length typs = length tys -> 
    (forall X : nat, In X Ys -> In X (Extract_TyVar _ N typs)) ->
    TE_trans (TE_trans te (Extract_TyVar _ _ typs) tys) Xs Us =
    TE_trans te (Extract_TyVar _ _ typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
  
  Definition map_Ty_trans' :=
    ty_rect map_Ty_trans_P' map_Ty_trans_Q'
    (map_Ty_trans'_H1 _ eq_nat_dec _ Gty _ Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject)
    (map_Ty_trans'_H2 _ _ _ _ N N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars 
      FJ_Free_Vars_invert TE_trans Ty_trans_FJ)
    (I_map_Ty_trans' _ _ _ _ _ _  N_Wrap I_N_Wrap _ _ _ I_Free_Vars_invert I_Ty_trans_invert I_Ty_Wrap_inject)
    (map_Ty_trans'_H3 _ _ _ _ Ty_trans _ TE_Free_Vars id)
    (map_Ty_trans'_H4 _ _ _ _ Ty_trans _ Free_Vars TE_Free_Vars (fun x => x) GJ_TE_Free_Vars_invert 
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Definition wf_free_vars_P := Generic.wf_free_vars_P _ _ _ _ Empty WF_Type TUpdate Free_Vars.

  Definition wf_free_vars_Q := Generic.wf_free_vars_Q _ _ _ N N_Wrap _ Empty subtype
    Ty_trans WF_Type TUpdate I_cld_ext unit TE_Free_Vars id.
  
  Definition wf_free_vars_Q_P1 := wf_free_vars_Q_P1 _ _ _ _ Empty WF_Type TUpdate Free_Vars.

  Definition wf_free_vars_Q'' := wf_free_vars_Q'' _ _ _ _ _ wf_int_ext TUpdate Empty TE_Free_Vars.
  
  Variables (TLookup_TUpdate_eq : forall (gamma : Context) (X : _) (ty : _), TLookup (TUpdate gamma X ty) X ty)
    (TLookup_TUpdate_neq' : forall (gamma : Context) (Y X : _) (ty ty' : _),
      TLookup (TUpdate gamma Y ty') X ty -> X <> Y -> TLookup gamma X ty)
    (TLookup_id : forall (gamma : Context) (X : _) (ty ty' : _),
      TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty').

  Definition wf_free_vars :=
    WF_Type_rect' wf_free_vars_P wf_free_vars_Q wf_free_vars_Q_P1 wf_free_vars_Q''
    (wf_free_vars_ext_H1 _ _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate
      _ _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert)
    (wf_free_vars_ext_H2 _ _ _ _ Empty WF_Type TUpdate Free_Vars)
    (wf_free_vars_ext_H3 _ _ _ _ Empty WF_Type TUpdate Free_Vars)
    (I_wf_free_vars_ext _ _ N _ WF_Type subtype Ty_trans N_Wrap TUpdate Empty 
      unit _ Free_Vars)
    (GJ_wf_free_vars _ eq_nat_dec _ Gty _ _ Empty TLookup WF_Type
      GJ_WF_Type TUpdate TLookup_Empty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject
      TLookup_TUpdate_eq TLookup_TUpdate_neq' TLookup_id)
    (FJ_wf_free_vars_H1 _ _ _ _ _ N_Wrap _ _ Empty WF_Type _ _ _ TUpdate _ FJ_Ty_Wrap_inject md_ext 
      cld_ext CT wf_class_ext wf_object_ext cFJ_WF_Type Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert (GJ_TE_Free_Vars_obj _ _ _ _ Free_Vars))
    (FJ_wf_free_vars_H2 _ _ _ _ _ N_Wrap _ _ Empty WF_Type _ _ _ TUpdate _ FJ_Ty_Wrap_inject
      _ _ CT wf_class_ext wf_object_ext cFJ_WF_Type Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert)
    (I_wf_free_vars _ _ _ _ _ _ _ _ N _ WF_Type wf_int_ext N_Wrap I_N_Wrap _ _ IT I_WF_Type_Wrap _ _ 
      I_Free_Vars_invert I_Ty_Wrap_inject).

  Definition exists_Free_Vars :=
    ty_rect (exists_Free_Vars_P nat Ty Free_Vars) (exists_Free_Vars_Q nat _ TE_Free_Vars)
    (exists_Free_Vars_H1 _ _ Gty _ GJ_Free_Vars')
    (exists_Free_Vars_H2 _ _ _ _ _ _ _ _ _ FJ_Free_Vars')
    (I_exists_Free_Vars _ _ _ _ _ N_Wrap I_N_Wrap _ _ I_Free_Vars')
    (exists_Free_Vars_H3 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id))
    (exists_Free_Vars_H4 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id) (fun _ _ => id)).
  
  Lemma L_build_context'_Empty_1 : forall ce  (gamma : Context)
    (XNs : Generic.TyP_List nat N) (T : Ty),
    L_build_context' ce gamma ->
    WF_Type (update_Tlist gamma XNs) T ->
    WF_Type (update_Tlist Empty XNs) T.
    intros; inversion H; subst; assumption.
  Qed.
    
  Definition Type_Subst_Sub_2_5_P := 
    Generic.Type_Subst_Sub_2_5_P nat Ty N N_Wrap Context TLookup
    subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.
  
  Lemma Ty_trans_eq_NTy_trans : forall (N0 : N) (Xs : list _) (Us : list Ty),
    N_Wrap (N_trans N0 Xs Us) = Ty_trans (N_Wrap N0) Xs Us.
    intros; destruct N0; simpl.
    destruct f; simpl; unfold Generic.FJ_Ty_Wrap; reflexivity.
    destruct i; simpl; unfold I_Ty_Wrap; reflexivity.
  Qed.
  
  Lemma N_Wrap_inject : forall n n' : N, N_Wrap n = N_Wrap n' -> n = n'.
    intros; injection H; auto.
  Qed.
  
  Lemma FJ_WF_Type_Wrap_invert : forall delta S, WF_Type delta ( FJ_Ty_Wrap S) ->
    cFJ.FJ_WF_Type _ _ _ _ _ _  FJ_Ty_Wrap _ _ _ CT Context 
    (wf_class_ext' WF_Type) wf_object_ext delta ( FJ_Ty_Wrap S).
    intros; inversion H; subst; try eapply H0.
    inversion H0.
    inversion H0.
  Qed.

  Lemma I_WF_Type_invert : forall (gamma : Context) (ity : I_Ty _ ty_ext),
    WF_Type gamma (I_Ty_Wrap ity) -> Interface.I_WF_Type nat ty_ext Ty
    I_Ty_Wrap mty_ext nat nat Interface_ext Context IT wf_int_ext gamma (I_Ty_Wrap ity).
    intros; inversion H; inversion H0; subst; auto.
  Qed.

  Lemma L_build_context_unique : forall ce gamma gamma', 
    L_build_context ce gamma -> L_build_context ce gamma' -> gamma = gamma'.
    intros; inversion H; inversion H0; subst; injection H5; intros; subst.
    inversion H1; inversion H4; subst; reflexivity.
  Qed.

  Lemma L_WF_GI_L_WF_Ext : forall (gamma : Context) (ce : cld_ext) (c : nat)
    (ty : cFJ.FJ_Ty nat (GTy_ext Ty)) (fs : list (cFJ.FD nat Ty))
    (k' : K nat nat Ty) (ms : list (cFJ.MD nat nat Ty E md_ext)),
  Generic.L_build_context nat N Context TUpdate L_build_context' ce gamma ->
  Generic_Interface.L_WF nat Ty (GTy_ext Ty) nat nat N Context WF_Type
    subtype N_Wrap cld_ext ce_build_cte cFJ_N Empty Update nat E md_ext CT
    fields E_WF
    (Generic.L_build_context nat N Context TUpdate L_build_context') override
    L_WF_Ext Meth_build_context Meth_WF_Ext
    (cld (GTy_ext Ty) Ty nat nat nat nat E md_ext cld_ext ce c ty fs k' ms) ->
    GI_L_WF_Ext _ Ty ty_ext N _ WF_Type N_Wrap I_N_Wrap _ implements Empty gamma ce.
    intros; inversion H; inversion H0; inversion H18; subst.
    rewrite (L_build_context_unique _ _ _ H10 H) in H20; tauto.
  Qed.

  Lemma L_WF_GI_L_WF_Ext' : forall c cld, 
    CT c = Some cld -> 
    Generic_Interface.L_WF _ Ty ty_ext _ _ N Context WF_Type subtype N_Wrap cld_ext ce_build_cte cFJ_N
    Empty Update _ _ md_ext CT fields E_WF (Generic.L_build_context nat N Context TUpdate L_build_context')
    override L_WF_Ext Meth_build_context Meth_WF_Ext cld.
    intros; generalize (WF_CT _ _ H); intros; inversion H0; subst.
    econstructor; try eassumption; reflexivity.
  Qed.

  Fixpoint Type_Subst_Sub_2_5 delta S T (sub_S_T : subtype delta S T) : 
    Type_Subst_Sub_2_5_P delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return (Type_Subst_Sub_2_5_P delta S T sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => Type_Subst_Sub_2_5_FJ _ _ _ _ N N_Wrap cFJ_N
        _ Empty TLookup subtype Ty_trans
        WF_Type _ fields _ _ TUpdate app_context Update _ FJ_Ty_Wrap_inject _ _ CT
        build_te cFJ_sub wf_class_ext wf_object_ext E_WF Free_Vars TE_trans FJ_Ty_trans_invert 
        exists_Free_Vars N_trans subst_context
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
        FJ_WF_Type_Wrap_invert WF_CT (@Generic.GJ_Type_Subst_Sub_2_5_TE _ _ _ N_Wrap _
           Empty subtype Ty_trans WF_Type TUpdate _ _ Free_Vars exists_Free_Vars
          N_trans wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 
          _)
        (@GJ_Type_Subst_Sub_2_5_TE' _ _ _ _ _ subtype Ty_trans _ _ _ _ _ _ _)
        Type_Subst_Sub_2_5 delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => Type_Subst_Sub_2_5_GJ _ eq_nat_dec _ Gty _ _ _ TLookup subtype
        GJ_sub Ty_trans WF_Type TUpdate app_context TLookup_app Weakening_2_1_1
        Free_Vars GJ_Free_Vars' GJ_Ty_trans_invert Ty_trans_nil NIn_Ty_trans exists_Free_Vars 
        N_Wrap_inject N_trans
        subst_context TLookup_subst map_Ty_trans TLookup_dec TLookup_unique TLookup_app'
        TLookup_app'' TLookup_update_eq TLookup_update_neq' Free_Vars_Subst Ty_trans_eq_NTy_trans
        delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => I_Type_Subst_Sub_2_5 _ _ _ _ _ _ _ _ _ N _
        TLookup WF_Type subtype Ty_trans wf_int_ext N_Wrap I_N_Wrap TUpdate cld_ext ce_build_cte
        implements cFJ_N Empty Update _ _ _ _ CT _ I_subtype_Wrap IT _ _ I_Ty_trans_invert
        I_Ty_Wrap_inject FJ_Ty_trans_invert _ _ _ _ _ override _ _ _ 
        (@Generic_Interface.GJ_Type_Subst_Sub_2_5_TE _ _ _ _ WF_Type 
          subtype Ty_trans N_Wrap TUpdate Empty _ _ Free_Vars N_trans _ 
          _ exists_Free_Vars map_Ty_trans' wf_free_vars L_build_context'_Empty_1 _)
        L_WF_GI_L_WF_Ext' I_WF_Type_invert L_WF_GI_L_WF_Ext delta S' T' sub_S_T'
    end.

  Definition Type_Subst_WF_2_6_P := Generic.Type_Subst_WF_2_6_P _ _ _ N_Wrap
    _ TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.

  Definition cld_typs (cld' : cFJ.L nat nat nat nat ty_ext Ty E md_ext cld_ext) :=
    match cld' with cFJ.cld (typs, _) _ _ _ _ _  => typs
    end.
  
  Definition Type_Subst_WF_2_6_Q := Type_Subst_WF_2_6_Q _ _ _ _ N_Wrap
    _ TLookup subtype WF_Type TUpdate app_context _ 
    wf_class_ext Free_Vars TE_trans N_trans subst_context (@fst _ _).
  
  Definition Type_Subst_WF_2_6_P1 := Generic.Type_Subst_WF_2_6_P1 _ _ _  N_Wrap _ 
    TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.

  Definition Type_Subst_WF_2_6_Q'' := Type_Subst_WF_2_6_Q'' _ _ _ _ N _ 
    TLookup WF_Type subtype wf_int_ext N_Wrap TUpdate app_context  
    Free_Vars TE_trans N_trans subst_context (@fst _ _).

  Definition Ty_trans_trans_subst :=
    ty_rect (Ty_trans_trans_subst_P _ _ Ty_trans Free_Vars)
  (Ty_trans_trans_subst_Q _ _ _ Ty_trans TE_Free_Vars TE_trans)
  (fun n => (GJ_Ty_trans_trans_subst _ eq_nat_dec _ Gty _ Ty_trans build_fresh
    Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert (TyVar _ n)))
  (FJ_Ty_trans_trans_subst _ _ _ _ _ N_Wrap _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert
    TE_trans FJ_Ty_trans_invert)
  (I_Ty_trans_trans_subst _ _ _ _ _ Ty_trans N_Wrap I_N_Wrap _ _ _ I_Free_Vars_invert
    I_Ty_trans_invert I_Ty_Wrap_inject)
  (Ty_trans_trans_subst_H3 _ _ _ Ty_trans _ Free_Vars id GTy_ext_Wrap_inject)
  (Ty_trans_trans_subst_H4 _ _ _ _ Ty_trans build_fresh _ 
    Free_Vars TE_Free_Vars id (fun _ _ => id) TE_trans
    GTy_ext_Wrap_inject GJ_TE_Trans_invert).
 
  Lemma Int_build_context'_Empty_1 : forall ce gamma XNs T, (I_Int_build_context Context Empty) ce gamma -> 
    WF_Type (update_Tlist gamma XNs) T -> WF_Type (update_Tlist Empty XNs) T.
    intros; inversion H; subst; assumption.
  Qed.

  Lemma Int_WF_bound : forall int, I_WF int -> exists Ys,
      List_P2' (fun (typ : _ * N) => Free_Vars (N_Wrap (snd typ))) (fst (Interface_ie _ _ _ _ _ _ int)) Ys /\
      forall Y, In Y (fold_right (@app _) nil Ys) -> 
        In Y (Extract_TyVar _ _ (fst (Interface_ie _ _ _ _ _ _ int))).
    intros; inversion H; subst; simpl.
    eapply GI_I_WF_bound.
    apply exists_Free_Vars.
    eapply wf_free_vars.
    Focus 2.
    apply H0.
    apply Int_build_context'_Empty_1.
    apply H2.
  Qed.

  Definition cld_typs' : cld_ext -> Generic.TyP_List nat N := (@fst _ _).

Lemma L_WF_bound : forall cld : cFJ.L nat nat nat nat ty_ext Ty E md_ext cld_ext,
  Generic.L_WF Ty ty_ext nat N N_Wrap cFJ_N Context Empty subtype WF_Type
    nat fields nat nat Update E md_ext cld_ext CT E_WF ce_build_cte
    Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override cld ->
  exists Ys : list (list nat),
    List_P2' (fun typ : Generic.GTy nat * N => Free_Vars (N_Wrap (snd typ)))
      (Generic.cld_typs' nat Ty ty_ext nat N nat nat nat E md_ext cld_ext
         cld_typs' cld) Ys /\
    (forall Y : nat,
     In Y (fold_right (@app _) nil Ys) ->
     In Y
       (Extract_TyVar nat N
          (Generic.cld_typs' nat Ty ty_ext nat N nat nat nat E md_ext cld_ext
             cld_typs' cld))).
    intros; inversion H; subst; simpl.
    eapply GJ_L_WF_bound.
    apply exists_Free_Vars.
    eapply wf_free_vars.
    Focus 2.
    apply H0.
    intros; inversion H1; subst; assumption.
    apply H8.
  Qed.


  Definition Type_Subst_WF_2_6 :=
    WF_Type_rect' Type_Subst_WF_2_6_P Type_Subst_WF_2_6_Q Type_Subst_WF_2_6_P1
    Type_Subst_WF_2_6_Q''
    (Type_Subst_WF_2_6_ext_H1 _ _ N N_Wrap
      _ TLookup subtype Ty_trans WF_Type TUpdate app_context _ _
      Free_Vars N_trans subst_context Type_Subst_Sub_2_5 Ty_trans_trans_subst)
    (Type_Subst_WF_2_6_ext_H2 _ _ _ _ _ TLookup subtype Ty_trans WF_Type TUpdate app_context
      Free_Vars N_trans subst_context)
    (Type_Subst_WF_2_6_ext_H3 _ _ _ _ _ TLookup subtype Ty_trans WF_Type TUpdate app_context
      Free_Vars N_trans  subst_context)
    (I_Type_Subst_WF_2_6_ext _ _ _ _ TLookup _ _ _ N_Wrap TUpdate _ _ app_context
      Free_Vars N_trans subst_context Type_Subst_Sub_2_5 Ty_trans_trans_subst)
    (GJ_Type_Subst_WF_2_6 _ eq_nat_dec _ Gty _ _ _ TLookup subtype
      Ty_trans WF_Type GJ_WF_Type TUpdate app_context TLookup_app Weakening_2_1_2
      Free_Vars GJ_Ty_trans_invert Ty_trans_nil Ty_trans_nil' N_trans subst_context
      TLookup_subst TLookup_dec TLookup_app' TLookup_app''
       TLookup_update_neq')
    (FJ_Type_Subst_WF_2_6_H1 _ _ _ _ _ N_Wrap _ _ TLookup subtype Ty_trans
      WF_Type _ _ _ TUpdate app_context _ _ _ CT wf_class_ext wf_object_ext
      cFJ_WF_Type Free_Vars TE_trans FJ_Ty_trans_invert N_trans subst_context 
      (GJ_Type_Subst_WF_2_6_obj_ext _ _ _ Ty_trans app_context _ subst_context))
    (FJ_Type_Subst_WF_2_6_H2 _ _ _ _ _ N_Wrap _ _ Empty TLookup subtype Ty_trans
      WF_Type _ fields _ _ TUpdate app_context Update _ _ _ CT wf_class_ext 
      wf_object_ext cFJ_WF_Type E_WF Free_Vars TE_trans FJ_Ty_trans_invert N_trans subst_context 
      _ _ _ _ _ override WF_CT cld_typs' L_WF_bound)
    (I_Type_Subst_WF_2_6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ wf_int_ext N_Wrap I_N_Wrap _ _ IT
      I_WF_Type_Wrap _ _ I_Ty_trans_invert N_trans _ (@fst _ _) _ _ _ _ WF_IT Int_WF_bound).

  Variable (subst_context_Empty : forall Xs Us, subst_context Empty Xs Us = Empty)
    (app_context_Empty : forall gamma, app_context gamma Empty = gamma).
  
  Fixpoint Ty_rename ty n : Ty :=
    match ty with 
      | N_Wrap (I_N_Wrap ty) => I_Ty_rename _ _ _ _ _ N_Wrap I_N_Wrap (GJ_TE_rename nat _ unit Ty_rename) ty n
      | N_Wrap (cFJ_N ty) => FJ_Ty_rename _ _ _ _ N N_Wrap cFJ_N (GJ_TE_rename nat _ unit Ty_rename) ty n
      | Gty ty' => GJ_Ty_rename _ _ Gty plus ty' n
    end.
  
  Definition TE_rename := GJ_TE_rename nat _ unit Ty_rename.
  
  Definition NTy_rename n n' : N := 
    match n with 
      | I_N_Wrap ty => I_Ty_rename _ _ _ _ _ I_N_Wrap id (GJ_TE_rename nat _ unit Ty_rename) ty n'
      | cFJ_N ty => FJ_Ty_rename _ _ _ _ N id cFJ_N (GJ_TE_rename nat _ unit Ty_rename) ty n'
    end.
  
  Variables (rename_context : Context -> nat -> Context)
    (TLookup_rename_context : forall gamma x ty n, 
      TLookup gamma x ty -> TLookup (rename_context gamma n) (x + n) (NTy_rename ty n))
    (TLookup_rename_context' : forall gamma x ty n, 
      TLookup (rename_context gamma n) x ty -> exists x', exists ty', x = x' + n /\ 
        ty = NTy_rename ty' n /\ TLookup gamma x' ty').
  
  Lemma rename_X_eq : forall Y Y' X', plus Y X' = plus Y' X' -> Y = Y'.
    intros; omega.
  Qed.
  
  Lemma GJ_Ty_rename_invert : forall ty Y, Ty_rename (Gty ty) Y = GJ_Ty_rename _ _ Gty plus ty Y.
    reflexivity.
  Qed.
  
  Lemma I_Ty_rename_invert : forall (ty : _) Y, 
    Ty_rename (I_Ty_Wrap ty) Y = I_Ty_rename _ _ _ _ N N_Wrap I_N_Wrap TE_rename ty Y.
    reflexivity.
  Qed.

  Definition Ty_rename_Ty_trans :=
    ty_rect (Generic.Ty_rename_Ty_trans_P _ _ Ty_trans plus Ty_rename)
    (Generic.Ty_rename_Ty_trans_Q _ _ _ TE_trans plus Ty_rename TE_rename)
    (GJ_Ty_rename_Ty_trans _ eq_nat_dec _ Gty Ty_trans GJ_Ty_trans_invert Ty_trans_nil' 
      plus Ty_rename rename_X_eq GJ_Ty_rename_invert)
    (FJ_Ty_rename_Ty_trans _ _ _ _ _ _ _ Ty_trans TE_trans FJ_Ty_trans_invert plus Ty_rename
      TE_rename (fun _ _ => refl_equal _))
    (I_Ty_rename_Ty_trans _ _ _ _ _ _ _ _ _ I_Ty_trans_invert _ _ plus I_Ty_rename_invert)
    (Ty_rename_Ty_trans_H3 _ _ Ty_trans _ plus Ty_rename)
    (Ty_rename_Ty_trans_H4 _ _ _ Ty_trans _ id TE_trans GTy_ext_Wrap_inject 
      GJ_TE_Trans_invert plus Ty_rename TE_rename (fun _ _ => refl_equal _)).     
  
  Definition FV_subst_tot := ty_rect (FV_subst_tot_P _ _ Ty_trans Free_Vars)
    (FV_subst_tot_Q _ _ _ Free_Vars TE_Free_Vars TE_trans)
    (GJ_FV_subst_tot _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_FV_subst_tot _ _ _ _ _ N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars
      FJ_Free_Vars' FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (I_FV_subst_tot _ _ _ _ _ _ _ _ _ _ _ I_Free_Vars' I_Free_Vars_invert I_Ty_trans_invert
      I_Ty_Wrap_inject)
    (FV_subst_tot_H3 _ _ Ty_trans _ Free_Vars)
    (FV_subst_tot_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id (fun _ _ => id) 
      (fun _ _  => id) TE_trans GJ_TE_Trans_invert).

  Definition Ty_rename_eq_Ty_trans := ty_rect 
    (Generic.Ty_rename_eq_Ty_trans_P _ _ Gty Ty_trans Free_Vars plus Ty_rename)
    (Generic.Ty_rename_eq_Ty_trans_Q _ _ _ Gty TE_Free_Vars TE_trans plus TE_rename)
    (GJ_Ty_rename_eq_Ty_trans _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert plus Ty_rename GJ_Ty_rename_invert)
    (FJ_Ty_rename_eq_Ty_trans _ _ _ Gty _ _ N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert plus Ty_rename
      TE_rename (fun _ _ => refl_equal _))
    (I_Ty_rename_eq_Ty_trans _ _ _ _ _ _ _ N_Wrap I_N_Wrap _ _ _ 
      I_Free_Vars_invert I_Ty_trans_invert I_Ty_Wrap_inject
      Ty_rename TE_rename plus I_Ty_rename_invert)
    (Ty_rename_eq_Ty_trans_H3 _ _ Gty Ty_trans _ Free_Vars plus Ty_rename)
    (Ty_rename_eq_Ty_trans_H4 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id (fun _ _ => id)
      TE_trans (fun _ _ => id) (fun _ _ _ => refl_equal _) plus Ty_rename TE_rename (fun _ _ => refl_equal _)).

  Lemma Ty_rename_eq_NTy_rename : forall (n : N) (X : _), Ty_rename (N_Wrap n) X = N_Wrap (NTy_rename n X).
    destruct n.
    simpl; unfold FJ_Ty_rename; unfold Generic.FJ_Ty_rename; intros; destruct f;
      unfold Generic.FJ_Ty_Wrap; unfold id; reflexivity.
    simpl; unfold I_Ty_rename; intros; destruct i; unfold I_Ty_Wrap; reflexivity.
  Qed.

  Lemma FJ_Ty_rename_invert : forall (ty : cFJ.FJ_Ty nat ty_ext) Y,
    Ty_rename (FJ_Ty_Wrap ty) Y =
    Generic.FJ_Ty_rename _ Ty ty_ext nat N N_Wrap cFJ_N TE_rename ty Y.
    reflexivity.
  Qed.

  Lemma L_WF_GI_L_WF_Ext'' : forall (gamma : Context) (ce : cld_ext) 
    (c : _) (ty : cFJ.FJ_Ty _ ty_ext) (fs : list (cFJ.FD _ Ty)) (k' : K _ _ Ty)
    (ms : list (cFJ.MD _ _ Ty E md_ext)),
    L_build_context ce gamma ->
    Generic_Interface.L_WF _ Ty ty_ext _ _ N Context
    WF_Type subtype N_Wrap cld_ext ce_build_cte cFJ_N
    Empty Update _ E md_ext CT fields E_WF L_build_context override L_WF_Ext Meth_build_context
    Meth_WF_Ext (cld ty_ext Ty _ _ _ _ _ md_ext cld_ext ce c ty fs k' ms) ->
    GI_L_WF_Ext _ Ty ty_ext N Context WF_Type N_Wrap
    I_N_Wrap cld_ext implements Empty gamma ce.
    intros; inversion H; inversion H0; inversion H18; subst.
    rewrite (L_build_context_unique _ _ _ H10 H) in H20.
    tauto.
  Qed.

  Fixpoint Ty_rename_subtype delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in (subtype delta S T) return (Ty_rename_subtype_P _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => 
        FJ_Ty_rename_subtype nat Ty ty_ext nat N  N_Wrap cFJ_N Context Empty
        subtype WF_Type nat fields nat nat Update E FJ_Ty_Wrap_inject md_ext cld_ext CT
        build_te cFJ_sub wf_class_ext wf_object_ext E_WF 
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext 
        L_build_context override FJ_WF_Type_Wrap_invert WF_CT Ty_rename
        TE_rename rename_context (fun _ _ => refl_equal _) 
        (fun (gamma : Context) (ce : cld_ext) (c : nat) 
          (te te'' te' : GTy_ext Ty) (n : nat) cld' (bld : L_build_context ce gamma)
          (L_WF_E : L_WF_Ext gamma ce c) H1 H2 => 
          @GJ_rename_build_te nat Ty Gty nat N N_Wrap Context Empty subtype Ty_trans
          WF_Type TUpdate _ _ Free_Vars exists_Free_Vars wf_free_vars
          L_build_context' L_build_context'_Empty_1 Ty_trans_trans_subst plus
          Ty_rename Ty_rename_eq_Ty_trans FV_subst_tot _
          (fun gamma (ie : I_cld_ext) c => FJ_L_WF_Ext _ _ gamma (@snd _ _ ie) c)
          gamma ce c te te'' te' n cld' bld (match L_WF_E with conj H3 _ => H3 end) H1 H2)
        (fun (gamma : Context) (ce : cld_ext) (c : nat) 
          (te te'' te' : GTy_ext Ty) (n : nat) (bld : L_build_context ce gamma)
          (L_WF_E : L_WF_Ext gamma ce c) => 
          @GJ_rename_build_te_obj _ _ _ _ N_Wrap _ Ty_trans WF_Type TUpdate _ _ L_build_context' Ty_rename
          (fun (ice : I_cld_ext) te te' te'' => FJ_build_te (snd ice) te te' te'') 
          (fun gamma (ie : I_cld_ext) c => FJ_L_WF_Ext _ _ gamma (@snd _ _ ie) c )
          gamma ce c te te'' te' n bld (match L_WF_E with conj H3 _ => H3 end)) 
        Ty_rename_subtype delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Ty_rename_subtype _ _ Gty _ _ _ TLookup subtype 
        GJ_sub plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename rename_context 
        TLookup_rename_context GJ_Ty_rename_invert delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => I_Ty_rename_subtype _ _ _ _ _ _ _ _ _ N
        Context WF_Type subtype wf_int_ext N_Wrap I_N_Wrap _ ce_build_cte implements cFJ_N
        Empty Update _ _ _ CT
        isub_build_te I_subtype_Wrap IT I_Ty_Wrap_inject fields E_WF Ty_rename TE_rename
        L_build_context override L_WF_Ext
        Meth_build_context Meth_WF_Ext WF_CT I_WF_Type_invert
        L_WF_GI_L_WF_Ext'' rename_context I_Ty_rename_invert FJ_Ty_rename_invert
        (fun (gamma : Context) (ce : cld_ext) (ie : GInterface_ext nat N)
          (c : nat) (te te'' te' : GTy_ext Ty) (n : nat)
          (H : L_build_context ce gamma) (H0 : L_WF_Ext gamma ce c)
          (H1 : wf_int_ext gamma ie te') (H2 : isub_build_te ce te te' te'') =>
          I_rename_isub_build_te nat nat Ty N Gty Context WF_Type subtype Ty_trans
          N_Wrap TUpdate Empty unit unit Free_Vars Ty_rename I_cld_ext
          L_build_context' exists_Free_Vars wf_free_vars L_build_context'_Empty_1
          Ty_trans_trans_subst plus Ty_rename_eq_Ty_trans FV_subst_tot gamma ce ie
          c te te'' te' n H match H0 with
                              | conj H3 _ => H3
                            end H1 H2) _ _ _ sub_S_T'
    end.

  Definition Free_Vars_id := ty_rect
    (Free_Vars_id_P _ _ Free_Vars) (Free_Vars_id_Q _ _ TE_Free_Vars)
    (GJ_Free_Vars_id _ _ Gty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject)
    (FJ_Free_Vars_id _ _ _ _ _ N_Wrap cFJ_N FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert)
    (I_Free_Vars_id _ _ _ _ _ _ _ _ _ I_Free_Vars_invert I_Ty_Wrap_inject)
    (Free_Vars_id_H3 _ _ _ Free_Vars)
    (Free_Vars_id_H4 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id)).

  Definition Ty_rename_WF_Type := WF_Type_rect' 
    (Ty_rename_WF_Type_P _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_Q _ _ _ _ N_Wrap _ _ wf_class_ext Free_Vars cld_typs' TE_rename 
      rename_context)
    (Ty_rename_WF_Type_P1 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_Q'' _ _ _ _ _ _ wf_int_ext N_Wrap Free_Vars TE_rename (@fst _ _) rename_context)
    (Ty_rename_WF_Type_ext_H1 _ _ Gty N N_Wrap _ subtype Ty_trans WF_Type _ _ Free_Vars
      exists_Free_Vars Ty_trans_trans_subst plus Ty_rename rename_context Ty_rename_eq_Ty_trans 
      FV_subst_tot Ty_rename_subtype Free_Vars_id)
    (Ty_rename_WF_Type_ext_H2 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext_H3 _ _ _ WF_Type Ty_rename rename_context)
    (I_Ty_rename_WF_Type_ext _ _ _ Gty _ WF_Type _ Ty_trans N_Wrap _ _ Free_Vars
    Ty_rename exists_Free_Vars Ty_trans_trans_subst plus rename_context Ty_rename_eq_Ty_trans
    FV_subst_tot Free_Vars_id Ty_rename_subtype)
    (GJ_Ty_rename_WF_Type _ _ Gty _ _ TLookup WF_Type GJ_WF_Type plus Ty_rename _ rename_context 
      TLookup_rename_context GJ_Ty_rename_invert)
    (FJ_Ty_rename_WF_Type_H1 _ _ _ _ _ N_Wrap cFJ_N _ WF_Type _ _ _ _ _ _ CT wf_class_ext
      wf_object_ext cFJ_WF_Type Ty_rename TE_rename rename_context (fun _ _ => refl_equal _)
      (GJ_Ty_rename_WF_object _ _ _ _ Ty_rename rename_context))
    (FJ_Ty_rename_WF_Type_H2 _ _ _ _ _ N_Wrap cFJ_N _ Empty subtype WF_Type _ fields _ _ Update
      _ _ _ CT wf_class_ext wf_object_ext cFJ_WF_Type E_WF Free_Vars
      ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
      WF_CT cld_typs' L_WF_bound Ty_rename TE_rename rename_context (fun _ _ => refl_equal _))
    (I_Ty_rename_WF_Type _ _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap I_N_Wrap
      IT I_WF_Type_Wrap Free_Vars Ty_rename TE_rename (@fst _ _) rename_context 
      I_Ty_rename_invert _ _ _ _ WF_IT Int_WF_bound).
  
  Fixpoint subtype_context_shuffle delta S T (sub_S_T : subtype delta S T) {struct sub_S_T} :=
    match sub_S_T in subtype delta S T return 
      (subtype_context_shuffle_P _ _ _ _ TLookup subtype app_context delta S T sub_S_T) with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_subtype_context_shuffle _ _ _ _ _ _ _ _ TLookup
        subtype _ _ _ app_context _ _ _ CT build_te cFJ_sub subtype_context_shuffle
        _ _ _ sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_subtype_context_shuffle _ _ Gty _ _ _ 
        TLookup subtype GJ_sub app_context TLookup_app TLookup_dec
        TLookup_unique TLookup_app' TLookup_app'' _ _ _ sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' => I_subtype_context_shuffle _ _ _ _ _ _ _ _ _
        TLookup subtype N_Wrap I_N_Wrap _ implements cFJ_N app_context _ _ _ CT
        isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.
    
  Definition WF_context_shuffle := WF_Type_rect' 
    (WF_context_shuffle_P _ _ _ _ TLookup WF_Type app_context)
    (Generic.WF_context_shuffle_Q _ _ _ _ TLookup app_context _ wf_class_ext)
    (WF_context_shuffle_P1 _ _ _ _ TLookup WF_Type app_context)
    (WF_context_shuffle_Q'' _ _ _ _ _ TLookup wf_int_ext app_context)    
    (WF_context_shuffle_ext_H1 _ _ _ N_Wrap _ TLookup subtype Ty_trans WF_Type 
      app_context _ _ subtype_context_shuffle)
    (WF_context_shuffle_ext_H2 _ _ _ _ TLookup WF_Type app_context)
    (WF_context_shuffle_ext_H3 _ _ _ _ TLookup WF_Type app_context)
    (I_WF_context_shuffle_ext _ _ N _ TLookup WF_Type subtype Ty_trans N_Wrap
      _ _ app_context subtype_context_shuffle)
    (GJ_WF_context_shuffle _ _ Gty _ _ TLookup WF_Type GJ_WF_Type app_context
      TLookup_app TLookup_dec TLookup_app' TLookup_app'')
    (FJ_WF_context_shuffle_H1 _ _ _ _ _ _ _ _ TLookup WF_Type _ _ _ app_context _
      _ _ CT wf_class_ext wf_object_ext cFJ_WF_Type 
      (GJ_WF_context_shuffle_obj_ext _ _ app_context _))
    (FJ_WF_context_shuffle_H2 _ _ _ _ _ _ _ _ TLookup WF_Type _ _ _ app_context _ _ _ CT
      wf_class_ext wf_object_ext cFJ_WF_Type)
    (I_WF_context_shuffle _ _ _ _ _ _ _ _ _ _ TLookup WF_Type wf_int_ext
      N_Wrap I_N_Wrap app_context IT I_WF_Type_Wrap).
      
  Lemma rename_X_inject : forall X Y n, plus X n = plus Y n -> X = Y.
    clear; intros; omega.
  Qed.
    
  Lemma Ty_Wrap_discriminate' : forall ty ty',Generic_Interface.FJ_Ty_Wrap _ Ty ty_ext N N_Wrap
    cFJ_N ty <> I_Ty_Wrap ty'.
    unfold FJ_Ty_Wrap; unfold not; intros; discriminate.
  Qed.

  Lemma Ty_Wrap_discriminate'' : forall (ty : GTy _) (ty' : I_Ty _ ty_ext), Gty ty <> I_Ty_Wrap ty'.
    unfold not; intros; discriminate.
  Qed.

  Definition Ty_rename_FJ_Ty_Wrap_eq ty :=
    match ty return (Generic.Ty_rename_FJ_Ty_Wrap_eq_P _ Ty _ _ N N_Wrap cFJ_N Ty_rename
      TE_rename ty) with
      | N_Wrap (cFJ_N (ty_def te c)) => FJ_Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ _ N_Wrap _ FJ_Ty_Wrap_inject 
        Ty_rename TE_rename FJ_Ty_rename_invert te c
      | Gty (TyVar X) => GJ_Ty_rename_FJ_Ty_Wrap_eq _ _ _ Gty _ _ N_Wrap _ Ty_Wrap_discriminate 
        plus Ty_rename TE_rename GJ_Ty_rename_invert X 
      | N_Wrap (I_N_Wrap (ity_def te i)) => I_Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ _ _ N_Wrap I_N_Wrap cFJ_N
        _ _ I_Ty_rename_invert Ty_Wrap_discriminate' te i
    end.

  Definition Ty_rename_GJ_Ty_Wrap_eq ty :=
    match ty return (Ty_rename_GJ_Ty_Wrap_eq_P _ _ Gty Ty_rename ty) with
      | N_Wrap (cFJ_N (ty_def te c)) => FJ_Ty_rename_GJ_Ty_Wrap_eq _ _ _ Gty _ _ N_Wrap _ 
        Ty_Wrap_discriminate Ty_rename TE_rename FJ_Ty_rename_invert te c
      | Gty (TyVar X) => GJ_Ty_rename_GJ_Ty_Wrap_eq _ _ Gty plus Ty_rename 
        GJ_Ty_rename_invert X 
      | N_Wrap (I_N_Wrap (ity_def te i)) => I_Ty_rename_GJ_Ty_Wrap_eq _ _ _ _ _ Gty 
        N_Wrap I_N_Wrap _ _ I_Ty_rename_invert Ty_Wrap_discriminate'' te i
    end.

  Definition Ty_rename_I_Ty_Wrap_eq ty :=
    match ty return (Ty_rename_I_Ty_Wrap_eq_P _ _ _ _ _ N_Wrap I_N_Wrap Ty_rename ty) with
      | N_Wrap (cFJ_N ty') => FJ_Ty_rename_I_Ty_Wrap_eq _ _ _ _ _ N
        N_Wrap I_N_Wrap cFJ_N Ty_rename TE_rename FJ_Ty_rename_invert Ty_Wrap_discriminate' ty'
      | Gty ty' => GJ_Ty_rename_I_Ty_Wrap_eq _ _ _ _ _ Gty _ _ _ plus 
        Ty_Wrap_discriminate'' GJ_Ty_rename_invert ty'
      | N_Wrap (I_N_Wrap (ity_def te i)) => I_Ty_rename_I_Ty_Wrap_eq _ _ _ _ _ _
        I_N_Wrap _ _ I_Ty_rename_invert te i
    end.

  Definition Ty_rename_inject := ty_rect
    (Ty_rename_inject_P _ _ Ty_rename)
    (Ty_rename_inject_Q _ _ TE_rename)
    (GJ_Ty_rename_inject _ _ Gty GJ_Ty_Wrap_inject plus Ty_rename rename_X_inject (fun _ _ => refl_equal _)
      Ty_rename_GJ_Ty_Wrap_eq)
    (FJ_Ty_rename_inject _ _ _ _ _ _ id Ty_rename TE_rename FJ_Ty_rename_invert Ty_rename_FJ_Ty_Wrap_eq)
    (I_Ty_rename_inject _ _ _ _ _ N_Wrap I_N_Wrap I_Ty_Wrap_inject _ _ I_Ty_rename_invert Ty_rename_I_Ty_Wrap_eq)
    (Ty_rename_inject_H3 _ _ _ Ty_rename)
    (Ty_rename_inject_H4 _ _ _ _ id GTy_ext_Wrap_inject Ty_rename
      TE_rename (fun _ _ => refl_equal _)).
  
  Fixpoint ex_Ty_rename_subtype delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in subtype delta S T return
      (ex_Ty_rename_subtype_P_r _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_ex_Ty_rename_subtype_P_r _ _ _ _ _ N_Wrap cFJ_N
        _ Empty subtype WF_Type _ fields _ _ Update _ FJ_Ty_Wrap_inject _ _ CT build_te
        cFJ_sub wf_class_ext wf_object_ext E_WF _ _ _ _ _ 
        override FJ_WF_Type_Wrap_invert WF_CT Ty_rename TE_rename rename_context
        FJ_Ty_rename_invert Ty_rename_FJ_Ty_Wrap_eq
        (fun gamma ce c te te' te''  n ce' (bld : L_build_context ce gamma) (E_WF_Ext : L_WF_Ext gamma ce c) => 
          GJ_TE_rename_build_te _ _ Gty _ _ N_Wrap _ Empty subtype Ty_trans WF_Type
          TUpdate _ _ Free_Vars exists_Free_Vars wf_free_vars _ L_build_context'_Empty_1
          Ty_trans_trans_subst plus Ty_rename Ty_rename_eq_Ty_trans FV_subst_tot
        gamma ce c te te' te''  n ce' bld (match E_WF_Ext with | conj H3 _ => H3 end))
        (GJ_TE_rename_build_obj_te _ _ _ _ Ty_trans _ _ Ty_rename)
        ex_Ty_rename_subtype gamma S' T' sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_ex_Ty_rename_subtype_P_r 
        _ _ Gty _ _ _ TLookup subtype GJ_sub plus Ty_rename NTy_rename
        Ty_rename_eq_NTy_rename rename_context TLookup_rename_context' gamma S' T' sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' => I_ex_Ty_rename_subtype _ _ _ _ _ _ _ _ _ N
        _ WF_Type subtype wf_int_ext N_Wrap I_N_Wrap _ _ _ cFJ_N Empty Update
        _ _ _ CT isub_build_te I_subtype_Wrap IT I_Ty_Wrap_inject fields E_WF _ _ 
        L_build_context _ _ _ _ WF_CT I_WF_Type_invert L_WF_GI_L_WF_Ext'' rename_context
        I_Ty_rename_invert Ty_rename_FJ_Ty_Wrap_eq 
        (fun gamma ce c te te' te'' n int (bld : L_build_context ce gamma) (E_WF_Ext : L_WF_Ext gamma ce c)=>
          I_TE_rename_build_te _ _ _ _ Gty _ _ _ Ty_trans N_Wrap TUpdate Empty
          _ _ Free_Vars Ty_rename _ L_build_context' exists_Free_Vars wf_free_vars
          L_build_context'_Empty_1 Ty_trans_trans_subst plus Ty_rename_eq_Ty_trans
          FV_subst_tot gamma ce int c te te'' te' n bld 
          (match E_WF_Ext with | conj H3 _ => H3 end)) _ _ _ sub_S_T'
    end.
  
  Fixpoint Ty_rename_subtype' delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in subtype delta S T return 
      (Ty_rename_subtype_P' _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | cFJ_sub gamma S' T' sub_S_T' => FJ_Ty_rename_subtype' _ _ _ _ _ N_Wrap cFJ_N _ 
        Empty subtype WF_Type _ fields _ _ Update _ FJ_Ty_Wrap_inject _ _ CT build_te cFJ_sub
        wf_class_ext wf_object_ext E_WF _ _ _ _ _ override
        FJ_WF_Type_Wrap_invert WF_CT Ty_rename TE_rename rename_context 
        Ty_rename_FJ_Ty_Wrap_eq Ty_rename_inject 
        (fun gamma ce c te te' te''  n ce' (bld : L_build_context ce gamma) (E_WF_Ext : L_WF_Ext gamma ce c) =>
          GJ_TE_rename_build_te' _ _ Gty nat _ _ _ Empty subtype
          Ty_trans WF_Type TUpdate _ _ Free_Vars exists_Free_Vars
          wf_free_vars L_build_context' L_build_context'_Empty_1 Ty_trans_trans_subst plus Ty_rename 
          Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_inject 
          gamma ce c te te' te''  n ce' bld (match E_WF_Ext with | conj H3 _ => H3 end))
        (GJ_TE_rename_build_obj_te' _ _ _ _ Ty_trans _ _ Ty_rename)
        ex_Ty_rename_subtype
        Ty_rename_subtype' _ _ _ sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_Ty_rename_subtype' _ _ Gty _ _ _ TLookup
        subtype GJ_sub GJ_Ty_Wrap_inject plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename
        rename_X_inject rename_context TLookup_rename_context' GJ_Ty_rename_invert 
        Ty_rename_GJ_Ty_Wrap_eq Ty_rename_inject _ _ _ sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' => I_Ty_rename_subtype' _ _ _ _ _ _ _ _ _ _ 
        _ WF_Type subtype wf_int_ext N_Wrap I_N_Wrap _ _ _ cFJ_N _ Update _ _ _ CT
        isub_build_te I_subtype_Wrap IT I_Ty_Wrap_inject fields E_WF _ _
        _ _ _ _ _ WF_CT I_WF_Type_invert L_WF_GI_L_WF_Ext'' _ I_Ty_rename_invert
        Ty_rename_I_Ty_Wrap_eq Ty_rename_FJ_Ty_Wrap_eq
        (fun gamma ce c te te' te'' n int (bld : L_build_context ce gamma) (E_WF_Ext : L_WF_Ext gamma ce c)=>
          I_TE_rename_build_te _ _ _ _ Gty _ _ _ Ty_trans N_Wrap TUpdate Empty
          _ _ Free_Vars Ty_rename _ L_build_context' exists_Free_Vars wf_free_vars
          L_build_context'_Empty_1 Ty_trans_trans_subst plus Ty_rename_eq_Ty_trans
          FV_subst_tot gamma ce int c te te'' te' n bld 
          (match E_WF_Ext with | conj H3 _ => H3 end))
        (fun gamma ce c te te' te'' n int (bld : L_build_context ce gamma) (E_WF_Ext : L_WF_Ext gamma ce c)=>
          I_TE_rename_build_te' _ _ _ _ Gty _ _ _ Ty_trans N_Wrap TUpdate Empty
          _ _ Free_Vars Ty_rename _ L_build_context' exists_Free_Vars wf_free_vars
          L_build_context'_Empty_1 Ty_trans_trans_subst plus Ty_rename_eq_Ty_trans
          FV_subst_tot Ty_rename_inject gamma ce int c te te'' te' n bld 
          (match E_WF_Ext with | conj H3 _ => H3 end)) _ _ _ sub_S_T'
    end.
  
  Definition Ty_rename_WF_Type' := WF_Type_rect' 
    (Ty_rename_WF_Type'_P _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type'_Q _ _ _ _ N_Wrap _ _ wf_class_ext Free_Vars cld_typs'
      TE_rename rename_context)
    (Ty_rename_WF_Type'_P1 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type'_Q'' _ _ _ _ _ _ wf_int_ext N_Wrap Free_Vars TE_rename
      (@fst _ _) rename_context)
    (Ty_rename_WF_Type_ext'_H1 _ _ Gty _ N_Wrap _ subtype Ty_trans WF_Type
      _ _ Free_Vars exists_Free_Vars Ty_trans_trans_subst plus Ty_rename
      rename_context Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype'
      Free_Vars_id)
    (Ty_rename_WF_Type_ext'_H2 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext'_H3 _ _ _ WF_Type Ty_rename rename_context)
    (I_Ty_rename_WF_Type_ext' _ _ _ Gty _ _ _ _ N_Wrap _ _ _ _ exists_Free_Vars
      Ty_trans_trans_subst _ _ Ty_rename_eq_Ty_trans FV_subst_tot Free_Vars_id Ty_rename_subtype')
    (GJ_Ty_rename_WF_Type' _ _ Gty _ _ TLookup WF_Type GJ_WF_Type
      GJ_Ty_Wrap_inject plus Ty_rename NTy_rename rename_X_inject rename_context
      TLookup_rename_context' GJ_Ty_rename_invert Ty_rename_GJ_Ty_Wrap_eq)
    (FJ_Ty_rename_WF_Type'_H1 _ _ _ _ _ _ id _ WF_Type _ _ _ _ _ _ CT
      wf_class_ext wf_object_ext cFJ_WF_Type Ty_rename TE_rename rename_context
      Ty_rename_FJ_Ty_Wrap_eq 
      (GJ_Ty_rename_WF_object' _ _ _ _ Ty_rename rename_context))
    (FJ_Ty_rename_WF_Type'_H2 _ _ _ _ _ N_Wrap cFJ_N _ Empty subtype WF_Type _ fields
      _ _ Update _ _ _ CT wf_class_ext wf_object_ext cFJ_WF_Type E_WF Free_Vars
      _ _ _ _ _ _ WF_CT cld_typs' L_WF_bound Ty_rename TE_rename rename_context
      Ty_rename_FJ_Ty_Wrap_eq)
    (I_Ty_rename_WF_Type' _ _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap I_N_Wrap
      IT I_WF_Type_Wrap _ I_Ty_Wrap_inject _ _ (@fst _ _) _ I_Ty_rename_invert _ _ _ _ WF_IT
      Int_WF_bound Ty_rename_I_Ty_Wrap_eq).
    
  Variable (Finite_Context : forall gamma : Context, exists n,
    forall X ty ty' Ys, TLookup gamma X ty -> Free_Vars (Ty_rename ty' n) Ys -> ~ In X Ys).

  Definition Type_Subst_Sub_2_5_P' := Generic.Type_Subst_Sub_2_5_P' _ _ N N_Wrap _ Empty subtype Ty_trans
    WF_Type TUpdate app_context subst_context.

  Fixpoint Type_Subst_Sub_2_5' delta S T (sub_S_T : subtype delta S T) : 
    Type_Subst_Sub_2_5_P' delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return (Type_Subst_Sub_2_5_P' delta S T sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => 
        FJ_Type_Subst_Sub_2_5' _ _ _ _ N N_Wrap
        _ _ Empty subtype Ty_trans
        WF_Type _ fields _ _ TUpdate app_context Update _ FJ_Ty_Wrap_inject _ _ CT
        build_te cFJ_sub wf_class_ext wf_object_ext E_WF Free_Vars TE_trans FJ_Ty_trans_invert
        exists_Free_Vars N_trans subst_context
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
        FJ_WF_Type_Wrap_invert WF_CT (@Generic.GJ_Type_Subst_Sub_2_5_TE _ _ _ N_Wrap
          _ Empty subtype Ty_trans WF_Type TUpdate _ _ Free_Vars exists_Free_Vars
          N_trans wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 
          _) (@GJ_Type_Subst_Sub_2_5_TE' _ _ _ _ _ subtype Ty_trans _ _ _ _ _ _ _)
        Ty_trans_eq_NTy_trans Type_Subst_Sub_2_5' delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Type_Subst_Sub_2_5' _ eq_nat_dec _ Gty _ _ _ Empty TLookup subtype
        GJ_sub Ty_trans WF_Type GJ_WF_Type TUpdate app_context Free_Vars
        GJ_Free_Vars' GJ_Ty_trans_invert TLookup_TUpdate_eq TLookup_TUpdate_neq' wf_free_vars subst_context 
        TLookup_unique Ty_rename subst_context_Empty app_context_Empty Finite_Context
        delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => I_Type_Subst_Sub_2_5' _ _ _ _ _ _ _ _ _ N _
        WF_Type subtype Ty_trans wf_int_ext N_Wrap I_N_Wrap TUpdate cld_ext ce_build_cte
        implements cFJ_N Empty Update _ _ _ _ CT _ I_subtype_Wrap IT _ I_Ty_trans_invert
        I_Ty_Wrap_inject FJ_Ty_trans_invert _ _ _ _ _ override _ _ _ 
        (@Generic_Interface.GJ_Type_Subst_Sub_2_5_TE _ _ _ _ WF_Type 
          subtype Ty_trans N_Wrap TUpdate Empty _ _ Free_Vars N_trans _ 
          _ exists_Free_Vars map_Ty_trans' wf_free_vars L_build_context'_Empty_1 _)
        L_WF_GI_L_WF_Ext' I_WF_Type_invert L_WF_GI_L_WF_Ext Ty_trans_eq_NTy_trans _ _ _ sub_S_T'
    end.

  Definition Free_Vars_Ty_Rename := ty_rect
    (Generic.Free_Vars_Ty_Rename_P _ _ Free_Vars plus Ty_rename)
    (Generic.Free_Vars_TE_Rename_P _ _ TE_Free_Vars plus TE_rename)
    (GJ_Free_Vars_Ty_Rename _ _ Gty Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject plus Ty_rename GJ_Ty_rename_invert)
    (FJ_Free_Vars_Ty_Rename _ _ _ _ _ N_Wrap cFJ_N FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert _
    Ty_rename TE_rename FJ_Ty_rename_invert)
    (I_Free_Vars_Ty_Rename _ _ _ _ N N_Wrap I_N_Wrap _ _ I_Free_Vars_invert I_Ty_Wrap_inject _ _ plus 
      I_Ty_rename_invert)
    (Free_Vars_Ty_Rename_H3 _ _ _ _ _ _)
    (Free_Vars_Ty_Rename_H4 _ _ _ _ Free_Vars TE_Free_Vars id
      (fun _ _ => id) plus Ty_rename TE_rename (fun _ _ => refl_equal _)).

  Definition Type_Subst_WF_2_6' := Generic.Type_Subst_WF_2_6' _ eq_nat_dec _ Gty _ _ _ Empty
    TLookup subtype Ty_trans WF_Type TUpdate app_context Weakening_2_1_2 Free_Vars GJ_Free_Vars' 
    exists_Free_Vars N_trans wf_free_vars subst_context TLookup_update_eq
    TLookup_update_neq TLookup_update_neq' Ty_trans_eq_NTy_trans Ty_trans_trans_subst
    plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename rename_context TLookup_rename_context'
    GJ_Ty_rename_invert Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype
    subst_context_Empty app_context_Empty Finite_Context Ty_rename_WF_Type
    Ty_rename_WF_Type' WF_context_shuffle Free_Vars_Ty_Rename Type_Subst_WF_2_6.

  Variable (CT_eq : forall c ce c' d fds k' mds,
           CT c = Some (cFJ.cld nat nat nat nat ty_ext Ty E md_ext cld_ext ce c' d fds k' mds) ->
           c = c').

  Lemma L_build_context'_Empty_2 : forall (ce : _) (gamma : Context)
    (XNs : Generic.TyP_List _ _) (S T : Ty),
    L_build_context' ce gamma ->
    subtype (Generic.update_Tlist _ _ Context TUpdate gamma XNs) S T ->
    subtype (Generic.update_Tlist _ _ Context TUpdate Empty XNs) S T.
    intros; inversion H; subst.
    assumption.
  Qed.

  Definition WF_cld_ext_Lem := Generic.WF_cld_ext_Lem _ _ _ _ N N_Wrap cFJ_N _ Empty subtype
    WF_Type _ fields _ _ Update _ _ _ CT wf_class_ext E_WF Free_Vars ce_build_cte
    Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
    WF_CT cld_typs' L_WF_bound _ 
    (fun gamma ce te wf_e te'' c c1 gamma' gamma'' gamma''' ce' te' c1_WF c_WF =>
      GJ_WF_cld_ext_Lem' _ eq_nat_dec _ Gty nat _ N_Wrap _ Empty TLookup subtype
      Ty_trans WF_Type TUpdate app_context _ _ Weakening_2_1_2 Free_Vars
      GJ_Free_Vars' exists_Free_Vars N_trans wf_free_vars subst_context map_Ty_trans'
      _ L_build_context'_Empty_1 L_build_context'_Empty_2 TLookup_update_eq
      TLookup_update_neq TLookup_update_neq' Ty_trans_eq_NTy_trans Ty_trans_trans_subst
      plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename rename_context TLookup_rename_context'
      GJ_Ty_rename_invert Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype
      subst_context_Empty app_context_Empty Finite_Context Ty_rename_WF_Type Ty_rename_WF_Type'
      Type_Subst_Sub_2_5' WF_context_shuffle Free_Vars_Ty_Rename Type_Subst_WF_2_6 
      (fun (ice : I_cld_ext) te te' te'' => FJ_mtype_build_te (snd ice) te te' te'')
      gamma ce te wf_e te'' c c1 gamma' gamma'' gamma''' ce' te' 
      (match c1_WF with | conj H3 _ => H3 end) (match c_WF with | conj H3 _ => H3 end)).

  Definition WF_Type_par_Lem' delta ty (WF_ty : WF_Type delta ty) :
    WF_Type_par_Lem_P' delta ty WF_ty := 
    match WF_ty in (WF_Type delta ty) return WF_Type_par_Lem_P' delta ty WF_ty with 
      | cFJ_WF_Type gamma ty WF_base => 
        FJ_WF_Type_par_Lem' _ _ _ _ _ _ _
        _ _ _ CT Context wf_class_ext wf_object_ext WF_Type cFJ_WF_Type
        mtype_build_te L_build_context cFJ_inject
        WF_cld_ext_Lem
        gamma ty WF_base
      | GJ_WF_Type gamma ty WF_ty => GJ_WF_Type_par_Lem' _ _ _ _ _ _ N_Wrap _
        _ _ _ GJ_WF_Type _ _ _ _  Ty_Wrap_discriminate _ _ CT wf_class_ext L_build_context
        _ _ _ WF_ty
      | I_WF_Type_Wrap _ _ WF_ty => I_WF_Type_par_Lem' _ _ _ _ _ _ _ _ _ _ WF_Type
        wf_int_ext N_Wrap I_N_Wrap _ cFJ_N _ _ _ CT IT I_WF_Type_Wrap _ _ Ty_Wrap_discriminate'
        mtype_build_te _ _ WF_ty
    end.     
    
  Lemma WF_fields_map_id''' : forall (gamma : Context) (ty ty' ty'' : Ty),
    WF_fields_map gamma ty ty' -> WF_fields_map gamma ty ty'' -> ty' = ty''.
    intros; inversion H; inversion H0; inversion H1; inversion H5; subst;
      try discriminate.
    injection H15; intros; subst; rewrite (TLookup_id _ _ _ _ H13 H9); 
      reflexivity.
    injection H13; intros; subst; reflexivity.
  Qed.

  Lemma N_Bound'_invert : forall (delta : Context) (n : N) (ty : Ty),
    Bound delta (N_Wrap n) ty -> Generic.N_Bound Ty N  N_Wrap Context delta (N_Wrap n) ty.
    intros; inversion H; inversion H0; subst; assumption.
  Qed.

  Lemma fields_build_te_id'' : forall ce te te' te'' te''',
    build_te ce te te' te'' -> fields_build_te ce te te' te''' -> te'' = te'''.
    intros; inversion H; inversion H0; inversion H7; subst.
    injection H11; injection H10; injection H9; intros; subst.
    destruct te'0; destruct te'1; reflexivity.
  Qed.

  Lemma FJ_N_Ty_Wrap_inject : forall n n', cFJ_N n = cFJ_N n' -> n = n'.
    intros; injection H; auto.
  Qed.

  Lemma fields_build_te_id' : forall (gamma : Context) (ty : cFJ.FJ_Ty nat ty_ext),
    Bound gamma (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N ty)
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N ty).
    intros; constructor 2; unfold Generic.FJ_Ty_Wrap; unfold id; constructor.
  Qed.

  Lemma GJ_Bound'_invert : forall (delta : Context) (n : GTy _) (ty : N),
    Bound delta (Gty n) (N_Wrap ty) ->
    Generic.GJ_Bound _ Ty Gty N Context TLookup delta (Gty n) ty.
    intros; inversion H; subst; try assumption; inversion H0.
  Qed.

  Lemma GJ_Bound_ty : forall (delta : Context) (ty : GTy _) (ty' : Ty),
    Bound delta (Gty ty) ty' -> exists n : N, ty' = N_Wrap n.
    intros; inversion H; subst; try (inversion H0; fail);
      exists ty'0; reflexivity.
  Qed.

  Lemma GJ_Bound'_invert' : forall (delta : Context) (Y : GTy _) (ty : Ty),
    Bound delta (Gty Y) ty -> exists n, ty = N_Wrap n /\ 
      Generic.GJ_Bound nat _ Gty N _ TLookup delta (Gty Y) n.
    intros; inversion H; inversion H0; subst; exists ty'; split; auto.
  Qed.

  Definition Bound_id gamma ty ty' (Bnd : Bound gamma ty ty') :=
    match Bnd in (Bound gamma ty ty') return (forall ty'', Bound gamma ty ty'' -> ty' = ty'') with
      | GJ_Bound _ _ _ Bnd' => GJ_Bound_id _ _ Gty _ _ _ TLookup Bound
        GJ_Ty_Wrap_inject TLookup_unique GJ_Bound'_invert GJ_Bound'_invert' _ _ _ Bnd'
      | N_Bound _ _ _ Bnd' => N_Bound_id _ _ _ _ Bound N_Bound'_invert _ _ _ Bnd'
    end.

  Definition Bound_id' ty :=
    match ty return Bound'_id_P _ _ Bound ty with 
      | N_Wrap (cFJ_N ty') => FJ_Bound'_id _ _ _ _ _ _ _ Bound N_Wrap_inject N_Bound'_invert ty'
      | N_Wrap (I_N_Wrap ty) => Generic_Interface.Bound_id' _ _ _ _ _ N_Wrap I_N_Wrap Bound
        N_Bound'_invert ty
      | Gty ty' => GJ_Bound'_id _ _ Gty _ _ _ TLookup Bound GJ_Ty_Wrap_inject TLookup_id
        GJ_Bound'_invert' ty'
    end.
    
  Lemma N_Bound'_invert' : forall (delta : Context) (n : N) (ty : Ty),
    Bound delta (N_Wrap n) ty ->
    Generic_Interface.N_Bound Ty N Context N_Wrap delta (N_Wrap n) ty.
    intros; inversion H; inversion H0; subst.
    unfold FJ_Ty_Wrap; unfold id; constructor.
  Qed.

  Lemma FJ_Fields_Ity_False : forall gamma ity fds,  
    ~ fields gamma (Generic_Interface.I_Ty_Wrap nat Ty (GTy_ext Ty) N N_Wrap I_N_Wrap ity) fds.
    unfold not; intros.
    inversion H; subst.
    eapply (FJ_Fields_Ity_False _ _ _ _ _ _ _ _ N_Wrap I_N_Wrap 
            _ cFJ_N _ _ _ CT fields Ty_Wrap_discriminate' fields_build_te 
            fields_build_tys); eauto.
  Qed.

  Definition bld_te_eq_fields_build_te := Generic.bld_te_eq_fields_build_te nat Ty N Ty_trans _ _
    (fun ce : I_cld_ext => cFJ.FJ_bld_te_eq_fields_build_te (snd ce)).

  Definition WF_mtype_ty_0_map_refl := Generic.GJ_WF_mtype_ty_0_map_refl _ _ _ _ N_Wrap cFJ_N _ 
    Bound N_Bound.

  Definition fields_build_tys_tot := GJ_fields_build_tys_tot nat Ty N Ty_trans 
    (fun (ice : I_cld_ext) te te' te''=> FJ_build_te (snd ice) te te' te'')
    (fun te ice tys tys' => FJ_fields_build_tys Ty te (snd ice) tys tys')
    (fun te ce => cFJ.FJ_fields_build_tys_tot Ty te (snd ce)).

  Fixpoint Lem_2_8' delta S T sub_S_T : 
    cFJ.Lem_2_8_P nat Ty Context subtype fields Bound Empty delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return 
      (cFJ.Lem_2_8_P nat Ty Context subtype fields Bound Empty delta S T sub_S_T) with
      | cFJ_sub gamma' S' T' sub_S_T' =>
        FJ_Lem_2_8 nat nat nat nat ty_ext Ty _ E _ _
        CT Context subtype build_te cFJ_sub fields fields_build_te
        fields_build_tys FJ_fields Bound Empty 
        (Bound_tot _ _ _ _ _ _ _ Bound N_Bound) fields_build_tys_tot Bound_id'
        (fun gamma ty => N_Bound _ _ _ (N_bound _ _ N_Wrap _ gamma (cFJ_N ty)))
        bld_te_eq_fields_build_te gamma' S' T' sub_S_T' Lem_2_8'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Lem_2_8 _ _ Gty N N_Wrap _ Empty TLookup 
        subtype GJ_sub _ fields Bound GJ_Bound N_Wrap_inject N_Bound'_invert'
        gamma' S' T' sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' => I_Lem_2_8 _ _ _ I_Ty_Wrap _ _ _ _ _ _ _ _
        CT isub_build_te _ FJ_Ty_Wrap subtype I_subtype_Wrap _ fields Bound
        (FJ_Map_Fields_Ity_False _ _ _ _ _ N_Wrap I_N_Wrap Bound _ fields
        N_Bound'_invert FJ_Fields_Ity_False) _ _ _ sub_S_T'
    end.
      
  Variable build_fresh_id : forall tys ty tys' Xs Ys Xs' Xs'', build_fresh tys ty tys' Xs Ys Xs' -> 
    build_fresh tys ty tys' Xs Ys Xs'' -> Xs' = Xs''.

  Definition build_V' gamma1 m ty mde' Ws W (H : override gamma1 m ty mde' Ws W) := H.

  Definition WF_Bound_id delta S T T' (Bound_S : Bound delta S T) :=
    match Bound_S in Bound delta S T return Bound delta S T' -> T = T' with
      | GJ_Bound delta' S' T'' Bound_S' => GJ_Bound_id _ _ Gty _ N_Wrap _ 
        TLookup Bound GJ_Ty_Wrap_inject TLookup_unique GJ_Bound'_invert
        GJ_Bound'_invert' _ _ _ Bound_S' T'
      | N_Bound delta' S' T'' Bound_S' => N_Bound_id _ _ N_Wrap _ Bound
        N_Bound'_invert _ _ _ Bound_S' T'
    end.
      
  Definition In_m_mds_dec := cFJ.In_m_mds_dec _ nat Ty E md_ext eq_nat_dec.
   
  Definition WF_mtype_ty_0_map_TLookup := GJ_WF_mtype_ty_0_map_TLookup _ _ Gty _ 
    N_Wrap _ TLookup Bound GJ_Bound.

  Variable build_fresh_len : forall tys ty vds Xs Ws Ys, 
    build_fresh tys ty vds Xs Ws Ys -> length Ws = length Ys.

  Variable build_fresh_tot : forall tys ty tys' Xs Ys, exists Xs', build_fresh tys ty tys' Xs Ys Xs'.

  Definition mtype_build_mtye_tot := Generic.mtype_build_mtye_tot _ _ Gty _ Ty_trans _ _ 
    build_fresh N_Trans _ _ _ build_fresh_tot build_fresh_len _ 
    (fun ce te me ty vds (mtye : unit) => True) (fun ce : I_cld_ext => FJ_mtype_build_mtye_tot nat Ty (snd ce)). 

  Definition mtype_build_tys_tot := Generic.mtype_build_tys_tot _ _ Gty _ Ty_trans _ build_fresh
    N_Trans _ _ _ build_fresh_tot build_fresh_len _ 
    (fun (ice : I_cld_ext) te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys')
    (fun ce : I_cld_ext => FJ_mtype_build_tys_tot nat Ty (snd ce)).

  Lemma N_Wrap_inject' : forall n n', 
    N_Wrap (cFJ_N n) = N_Wrap (cFJ_N n') -> n = n'.
    intros; injection H; auto.
  Qed.

  Definition WF_mtype_ty_0_map_id := Bound_id'.

  Definition build_te_build_mtye_te'' := 
    Generic.GJ_build_te_build_mtye_te'' _ _ N Ty_trans _ _ 
    (fun (ice : I_cld_ext) te te' te'' => FJ_mtype_build_te (snd ice) te te' te'')
    (fun (ice : I_cld_ext) te te' te''=>  FJ_build_te (snd ice) te te' te'') 
    (fun ce : I_cld_ext => FJ_build_te_build_mtye_te'' (snd ce)).

  Definition build_te_build_ty_0_id := Generic.build_te_build_ty_0_id _ _ _ _ _ _ _
    FJ_Ty_Wrap_inject _ build_te WF_mtype_ty_0_map mtype_build_te WF_mtype_ty_0_map_id
    WF_mtype_ty_0_map_refl build_te_build_mtye_te''.

  Definition mtype_build_tys_len' := Generic.mtype_build_tys_len' _ _ _ Gty N Ty_trans _ build_fresh _
    _ (fun (ice : I_cld_ext) te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys')
    mtype_build_tys_len.

  Lemma WF_Type_invert : forall (delta : Context) (S : cFJ.FJ_Ty _ ty_ext), 
    WF_Type delta (N_Wrap (cFJ_N S)) ->
    cFJ.FJ_WF_Type _ _ _ _ ty_ext Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) E md_ext cld_ext CT Context 
    wf_class_ext wf_object_ext delta (N_Wrap (cFJ_N S)).
    intros; inversion H; subst; auto; inversion H0.
  Qed.

  Variable I_Lem_2_9 : forall gamma S T sub_S_T, 
    cFJ.Lem_2_9_P _ _ _ _ _ subtype mtype Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ 
    (I_subtype_Wrap gamma S T sub_S_T).

  Fixpoint Lem_2_9 gamma S T (sub_S_T : subtype gamma S T) : 
    cFJ.Lem_2_9_P _ _ _ _ _ subtype mtype Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T :=
    match sub_S_T return cFJ.Lem_2_9_P _ _ _ _ _ subtype mtype Bound 
      WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T with
      | cFJ_sub gamma S' T' sub_S_T' => cFJ.FJ_Lem_2_9 _ _ _ _ _ _ FJ_Ty_Wrap
        _ _ _ _ _ CT _ subtype build_te cFJ_sub wf_class_ext wf_object_ext
        WF_Type fields mtype mtype_build_te mtype_build_tys
        mtype_build_mtye FJ_mtype E_WF Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty
        Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
        WF_CT FJ_Ty_Wrap_inject WF_mtype_ty_0_map_total mtype_build_tys_len' 
        WF_Type_invert (fun g S T T' Bnd => Bound_id g S T Bnd T') eq_nat_dec
        build_te_build_ty_0_id WF_mtype_ty_0_map_refl mtype_build_tys_tot 
        mtype_build_mtye_tot build_V' gamma S' T' sub_S_T' Lem_2_9
      | GJ_sub gamma S' T' sub_S_T' => Generic.GJ_Lem_2_9 _ _ _ Gty _ _ N_Wrap
        _ _ Empty TLookup subtype GJ_sub _ _ _ _ mtype _ _ _ CT build_te 
        cFJ_sub _ Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext 
        WF_mtype_ty_0_map_id (fun gamma ty => N_Bound _ _ _ (N_bound _ _ N_Wrap _ gamma (ty)))
        WF_mtype_ty_0_map_TLookup gamma S' T' sub_S_T'
      | I_subtype_Wrap gamma' S' T' sub_S_T' => I_Lem_2_9 gamma' S' T' sub_S_T'
    end.

  Fixpoint Subtype_Weaken gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T in (subtype gamma S T) return (Subtype_Weaken_P Ty Context subtype Empty gamma S T sub_S_T) with
      | cFJ_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Weaken _ _ _ _ _ _ _ _ _ _ CT _ subtype build_te
        cFJ_sub Empty gamma' S' T' sub_S_T' Subtype_Weaken
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Subtype_Weaken _ _ Gty _ _ _ Empty TLookup _ GJ_sub TLookup_Empty _ _ _ sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' => I_Subtype_Weaken _ _ _ _ _ _ _ _ subtype N_Wrap I_N_Wrap
        _ _ cFJ_N _ _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

  Variable TLookup_TUpdate_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
       TLookup (TUpdate gamma Y ty') X ty.

  Fixpoint Weaken_subtype_app_TList delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return (Weaken_subtype_app_TList_P _ _ _ _  Empty subtype TUpdate _ _ _ sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => 
        FJ_Weaken_subtype_app_TList _ _ _ _ _ N_Wrap cFJ_N _ Empty subtype _ _ _ TUpdate
        _ _ _ CT build_te cFJ_sub Weaken_subtype_app_TList delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Weaken_subtype_app_TList _ eq_nat_dec _ Gty _ _
        _ Empty TLookup subtype GJ_sub TUpdate TLookup_Empty TLookup_TUpdate_eq TLookup_TUpdate_neq
        TLookup_TUpdate_neq' TLookup_id delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => I_Weaken_subtype_app_TList _ _ _ _ _ _ _ _ _ subtype N_Wrap
        I_N_Wrap TUpdate _ implements cFJ_N Empty _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

  Definition Weaken_WF_Type_app_TList :=
    WF_Type_rect' (Weaken_WF_Type_app_TList_P _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_Q _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate _ _)
    (Weaken_WF_Type_app_TList_P1 _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_Q'' _ _ _ _ _ wf_int_ext TUpdate Empty)
    (Weaken_WF_Type_app_TList_ext_H1 _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate _ _ 
      Weaken_subtype_app_TList)
    (Weaken_WF_Type_app_TList_ext_H2 _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_ext_H3 _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_int_ext _ _ _ _ WF_Type subtype Ty_trans N_Wrap TUpdate Empty
      _ _ Weaken_subtype_app_TList)
    (GJ_Weaken_WF_Type_app_TList _ eq_nat_dec _ Gty _ _ Empty TLookup WF_Type 
      GJ_WF_Type TUpdate TLookup_Empty TLookup_TUpdate_eq TLookup_TUpdate_neq TLookup_TUpdate_neq'
      TLookup_id)
    (FJ_Weaken_WF_Type_app_TList_H1 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ _ _ CT wf_class_ext
      wf_object_ext cFJ_WF_Type (Weaken_WF_Type_app_TList_obj_ext _ _ _ _ Empty TUpdate _))
    (FJ_Weaken_WF_Type_app_TList_H2 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ _ _
      CT wf_class_ext wf_object_ext cFJ_WF_Type)
    (I_Weaken_WF_Type_app_TList_int _ _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap
      I_N_Wrap TUpdate Empty IT I_WF_Type_Wrap).
          
  Definition FJ_NTy_trans_invert (ty : Generic.Base_Ty ty_ext nat) (txs : list nat) (tys : list Ty) : 
    Ty_trans ((Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) (id ty)) txs tys =
    FJ_Ty_Trans _ Ty ty_ext _ N N_Wrap cFJ_N TE_trans ty txs tys :=
    refl_equal _.

  Definition Bound'_Trans := Generic.Bound'_Trans _ _ _ _ _ Ty_trans Bound N_Bound
    N_trans Ty_trans_eq_NTy_trans.

  Lemma GJ_WF_Type_invert : forall gamma ty , WF_Type gamma (Gty ty) ->
    Generic.GJ_WF_Type _ Ty Gty N Context TLookup gamma (Gty ty).
    intros; inversion H; subst; auto; inversion H0.
  Qed.

  Fixpoint ex_WF_Bound' (S : Ty) := 
    match S return ex_WF_Bound'_P Ty N N_Wrap Context WF_Type Bound S with
      | N_Wrap (cFJ_N (ty_def te c)) => FJ_ex_WF_Bound' _ _ _ _ N_Wrap cFJ_N _ WF_Type Bound N_Bound te c
      | Gty (TyVar X) => GJ_ex_WF_Bound' _ _ Gty _ _ _ TLookup WF_Type Bound GJ_Bound GJ_Ty_Wrap_inject
        GJ_WF_Type_invert X
      | N_Wrap (I_N_Wrap i) => I_ex_WF_Bound' _ _ _ _ _ WF_Type N_Wrap I_N_Wrap Bound N_Bound i
      end.

  Fixpoint sub_Bound delta S T (sub_S_T : subtype delta S T) : 
    (sub_Bound'_P _ _ subtype Bound _ _ _ sub_S_T) :=
    match sub_S_T return (sub_Bound'_P _ _ subtype Bound  _ _ _ sub_S_T) with
      | cFJ_sub delta S' T' sub_S_T' => 
        FJ_sub_Bound' _ _ _ _ _ _
        _ subtype _ _ _ _ Bound _ _ CT build_te cFJ_sub
        N_Wrap_inject N_Bound'_invert WF_mtype_ty_0_map_total Bound_id'
        sub_Bound delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => 
        GJ_sub_Bound' _ _ _ Gty _ _ _ _ _ TLookup subtype GJ_sub _ _ _ _ 
        Bound _ _ CT build_te cFJ_sub GJ_Ty_Wrap_inject TLookup_id
        N_Wrap_inject N_Bound'_invert' GJ_Bound'_invert' delta S' T' sub_S_T'
      | I_subtype_Wrap delta S' T' sub_S_T' => I_sub_Bound _ _ _ _ _ _ _ _ subtype N_Wrap I_N_Wrap _
        implements cFJ_N Bound _ _ _ CT isub_build_te I_subtype_Wrap N_Bound'_invert _ _ _ sub_S_T'
    end.

  Definition Lem_2_7 (T :Ty) :=
    match T return Generic.Lem_2_7_P _ _ _ N_Wrap
      _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound T with 
      | N_Wrap (cFJ_N (ty_def te c)) => FJ_Lem_2_7 _ _ _ _ _ _ _
        Context Empty subtype Ty_trans WF_Type _ _ _ TUpdate Update _ Bound
        N_Bound _ _ CT build_te cFJ_sub TE_trans FJ_Ty_trans_invert
        N_Wrap_inject N_Bound'_invert FJ_NTy_trans_invert te c
      | Gty (TyVar X) => GJ_Lem_2_7 _ eq_nat_dec _ Gty _ _
        _ Empty TLookup subtype Ty_trans WF_Type _ TUpdate Update TLookup_Update
        TLookup_Empty Bound N_Bound GJ_Ty_Wrap_inject GJ_Ty_trans_invert 
        TLookup_TUpdate_eq TLookup_TUpdate_neq TLookup_TUpdate_neq' TLookup_id 
        _ Ty_trans_eq_NTy_trans GJ_Bound'_invert' sub_Bound ex_WF_Bound' X
      | N_Wrap (I_N_Wrap i) => I_Lem_2_7 _ _ _ _ _ _ _ _ _ WF_Type subtype Ty_trans
        N_Wrap I_N_Wrap TUpdate _ cFJ_N Empty Update Bound N_Bound _ _ _ CT TE_trans
        I_Ty_trans_invert N_Bound'_invert N_Wrap_inject build_te cFJ_sub i
    end.

  Lemma map_e_invert : forall XNs Us e e',
    E_Ty_Trans XNs Us (cFJ_E e) e' -> Generic.E_Ty_Trans _ _ _ _ _ _ _ _ _ _
    cFJ_E mbody_m_call_map mbody_new_map E_Ty_Trans XNs Us (cFJ_E e) e'.
    intros; inversion H; subst; auto; inversion H0.
  Qed.

  Definition WF_fields_map_sub (X : Ty) : Bound'_sub_P _ _ subtype Bound X :=
    match X return Bound'_sub_P _ _ subtype Bound X with
      | N_Wrap (cFJ_N ty) => N_Bound'_sub _ _ _ _ N_Wrap _ _ subtype _ _ _ _ Bound _ _ CT
      _ cFJ_sub N_Bound'_invert ty
      | Gty ty => GJ_Bound'_sub _ _ Gty _ _ _ TLookup subtype GJ_sub Bound
        GJ_Ty_Wrap_inject GJ_Bound'_invert' ty
      | N_Wrap (I_N_Wrap i) => I_Bound'_sub _ _ _ _ _ _ _ _ subtype N_Wrap I_N_Wrap _ 
        cFJ_N Bound _ _ _ CT N_Bound'_invert build_te cFJ_sub i
    end.
    
  Variable lookup_TUpdate : forall gamma X N x ty, lookup (TUpdate gamma X N) x ty -> lookup gamma x ty.
  Variable lookup_TUpdate' : forall gamma X N x ty, lookup gamma x ty -> lookup (TUpdate gamma X N) x ty.
    
  Lemma EWrap_inject : forall e e', cFJ_E e = cFJ_E e' -> e = e'.
    intros; injection H; intros; assumption.
  Qed.

  Definition WF_mtype_map_sub gamma ty ty' (Bnd : Bound gamma ty ty') :=
    match Bnd in Bound gamma ty ty' return (WF_mtype_mab_sub_def Ty Context subtype Bound gamma ty ty' Bnd) with 
      | N_Bound _ _ _ Bnd' => N_WF_mtype_map_sub _ _ _ _ _ _ _ subtype _ _ _ _ Bound N_Bound _ _ 
        CT build_te cFJ_sub _ _ _ Bnd'
      | GJ_Bound _ _ _ Bnd' => GJ_WF_mtype_map_sub _ _ _ _ _ _ TLookup _ GJ_sub Bound GJ_Bound _ _ _ Bnd'
    end.
  
  Fixpoint Trans_Bound' T :=
    match T return Trans_Bound'_P _ _ _ Ty_trans Bound T with
      | N_Wrap (cFJ_N T') => FJ_Trans_Bound' _ _ _ _ _ _ _ _ Ty_trans Bound N_Bound 
        TE_trans FJ_Ty_trans_invert N_Wrap_inject N_Bound'_invert T'
      | Gty T' => GJ_Trans_Bound' _ _ Gty _ _ _ TLookup Ty_trans Bound N_Bound GJ_Ty_Wrap_inject
        _ Ty_trans_eq_NTy_trans GJ_Bound'_invert' T'
      | N_Wrap (I_N_Wrap i) => I_Trans_Bound' _ _ _ _ _ _ Ty_trans N_Wrap I_N_Wrap Bound N_Bound 
        N_trans Ty_trans_eq_NTy_trans N_Bound'_invert i
    end.

  Definition Trans_WF_mtype_map := Trans_Bound'.
  Definition Trans_WF_fields_map := Trans_Bound'.

  Variable Ty_trans_mtype : forall (delta : Context) (m : _) 
    (S : Ty) (mty' : Mty Ty _)
    (mtype_S : mtype delta m S mty'),
    Ty_trans_mtype_P _ Ty N N_Wrap Context Empty subtype
    Ty_trans WF_Type _ _ _ mtype TUpdate Update
    m_call_ext WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext
    mbody_m_call_map delta m S mty' mtype_S.

  Fixpoint Bound_total gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T return Bound_total_P _ _ subtype Bound _ _ _ sub_S_T with 
      | cFJ_sub gamma' S' T' sub_S_T' => FJ_Bound_total _ _ _ _ _ _ _ subtype _ _ _ _ 
        Bound N_Bound _ _ CT build_te cFJ_sub Bound_total _ _ _ sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => GJ_Bound_total _ _ Gty _ _ 
        _ TLookup subtype GJ_sub Bound GJ_Bound _ _ _ sub_S_T'
      | I_subtype_Wrap gamma' S' T' sub_S_T' => I_Bound_total _ _ _ _ _ _ _ _ subtype N_Wrap
        I_N_Wrap _ implements cFJ_N _ N_Bound _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

  Fixpoint Lem_2_7'' (S : Ty) :=
    match S return Lem_2_7''_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound S with
      | N_Wrap (cFJ_N S') => FJ_Lem_2_7'' _ _ _ _ _ _ _ _ Empty subtype Ty_trans WF_Type _ _ _ 
        TUpdate Update _ Bound N_Bound _ _ CT build_te cFJ_sub TE_trans FJ_Ty_trans_invert
        N_Wrap_inject N_Bound'_invert S'
      | Gty S' => GJ_Lem_2_7'' _ eq_nat_dec _ Gty _ _ _ Empty TLookup subtype Ty_trans
        WF_Type _ TUpdate Update TLookup_Update TLookup_Update' TLookup_Empty Bound
        GJ_Ty_Wrap_inject GJ_Ty_trans_invert TLookup_TUpdate_eq TLookup_TUpdate_neq
        TLookup_TUpdate_neq' TLookup_id Bound_total GJ_Bound'_invert' Trans_Bound'
        sub_Bound S'
      | N_Wrap (I_N_Wrap i) => I_Lem_2_7'' _ _ _ _ _ _ _ _ _ WF_Type subtype Ty_trans N_Wrap 
        I_N_Wrap TUpdate _ cFJ_N Empty Update Bound N_Bound _ _ _ CT N_trans Ty_trans_eq_NTy_trans 
        N_Bound'_invert build_te cFJ_sub i
    end.

  Fixpoint subtype_update_list_id' delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return subtype_update_list_id'_P _ _ subtype _ Update _ _ _ sub_S_T with
      | cFJ_sub delta' S' T' sub_S_T' => FJ_subtype_update_list_id' _ _ _ _ _ _ _ 
        subtype _ _ _ Update _ _ _ CT build_te cFJ_sub subtype_update_list_id' _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_subtype_update_list_id' _ _ _ _ _ _ 
        TLookup subtype GJ_sub _ Update TLookup_Update' _ _ _ sub_S_T'
      | I_subtype_Wrap delta' S' T' sub_S_T' => I_subtype_update_list_id' _ _ _ _ _ _ _ _ subtype N_Wrap 
        I_N_Wrap _ implements cFJ_N Update _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

    Definition WF_Type_update_list_id' :=
    WF_Type_rect' (WF_Type_update_list_id'_P _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_Q _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _)
    (WF_Type_update_list_id'_P1 _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_Q'' _ _ _ _ _ wf_int_ext Update)
    (WF_Type_update_list_id'_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _ 
      subtype_update_list_id')
    (WF_Type_update_list_id'_ext_H2 _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_ext_H3 _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_int_ext _ _ _ _ _ WF_Type subtype Ty_trans N_Wrap Update _ 
      subtype_update_list_id')
    (GJ_WF_Type_update_list_id' _ _ Gty _ _ TLookup WF_Type GJ_WF_Type _ Update TLookup_Update')
    (FJ_WF_Type_update_list_id'_H1 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _ CT wf_class_ext
      wf_object_ext cFJ_WF_Type (WF_Type_update_list_id'_obj_ext _ _ _ Update _))
    (FJ_WF_Type_update_list_id'_H2 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _ CT wf_class_ext wf_object_ext
      cFJ_WF_Type)
    (I_WF_Type_update_list_id' _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap I_N_Wrap Update IT
      I_WF_Type_Wrap).

  Definition WF_mtype_ext_update_list := GJ_WF_mtype_ext_update_list _ _ N N_Wrap _ subtype Ty_trans
    WF_Type _ _ Update _ (FJ_WF_mtype_ext Context) subtype_update_list_id' WF_Type_update_list_id'
    (FJ_WF_mtype_ext_update_list _ _ _ _ ).

  Definition WF_mtype_Us_map_update_list := Generic.GJ_WF_mtype_Us_map_update_list _ _ N _ Ty_trans
    _ _ Update _ (FJ_WF_mtype_Us_map Ty Context) (FJ_WF_mtype_Us_map_update_list _ _ _ Update).

  Definition WF_mtype_U_map_update_list := Generic.GJ_WF_mtype_U_map_update_list _ _ N _ Ty_trans
    _ _ Update _ (FJ_WF_mtype_U_map Ty Context) (FJ_WF_mtype_U_map_update_list _ _ _ Update).

    Definition Strengthen_Bound (S : Ty) := 
      match S return Strengthen_Bound''_P _ _ _ Update Bound S with 
        | N_Wrap (cFJ_N (ty_def te' c')) => 
          FJ_Strengthen_Bound'' _ _ _ _ _ cFJ_N _ _ Update Bound N_Bound N_Wrap_inject N_Bound'_invert te' c'
        | Gty (TyVar X) => GJ_Strengthen_Bound'' _ _ Gty _ _ _ TLookup _ Update TLookup_Update' Bound 
          GJ_Bound GJ_Ty_Wrap_inject GJ_Bound'_invert' X
        | N_Wrap (I_N_Wrap i) => I_Strengthen_Bound'' _ _ _ _ _ _ N_Wrap I_N_Wrap Update Bound N_Bound 
          N_Bound'_invert i
      end.

    Definition Strengthen_Bound' (S : Ty) := 
      match S return Strengthen_Bound'_P _ _ _ Update Bound S with 
        | N_Wrap (cFJ_N (ty_def te' c')) => 
          FJ_Strengthen_Bound' _ _ _ _ _ cFJ_N _ _ Update Bound N_Bound N_Wrap_inject N_Bound'_invert te' c'
        | Gty (TyVar X) => GJ_Strengthen_Bound' _ _ Gty _ _ _ TLookup _ Update TLookup_Update Bound 
          GJ_Bound GJ_Ty_Wrap_inject GJ_Bound'_invert' X
          | N_Wrap (I_N_Wrap i) => I_Strengthen_Bound' _ _ _ _ _ _ N_Wrap I_N_Wrap Update Bound N_Bound 
          N_Bound'_invert i
      end.

  Definition update_list_WF_mtype_ty_0_map := Strengthen_Bound.

  Fixpoint subtype_update_Tupdate delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return subtype_update_Tupdate_P _ _ _ _ subtype _ TUpdate Update _ _ _ sub_S_T with
      | cFJ_sub delta' S' T' sub_S_T' => FJ_subtype_update_Tupdate _ _ _ _ _ _ _ _ subtype
        _ _ _ TUpdate Update _ _ _ CT build_te cFJ_sub subtype_update_Tupdate _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_subtype_update_Tupdate _ eq_nat_dec _ Gty _ _ _ TLookup
        subtype GJ_sub _ TUpdate Update TLookup_Update TLookup_Update' TLookup_TUpdate_eq
        TLookup_TUpdate_neq TLookup_TUpdate_neq' TLookup_id _ _ _ sub_S_T'
      | I_subtype_Wrap delta' S' T' sub_S_T' => I_subtype_update_Tupdate _ _ _ _ _ _ _ _ _ subtype N_Wrap
        I_N_Wrap TUpdate _ implements cFJ_N Update _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

    Definition WF_Type_update_Tupdate :=
    WF_Type_rect' (WF_Type_update_Tupdate_P _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_Q _ _ _ _ _ subtype Ty_trans WF_Type _ TUpdate Update _ _)
    (WF_Type_update_Tupdate_P1 _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_Q'' _ _ _ _ _ _ _ wf_int_ext TUpdate Update)
    (WF_Type_update_Tupdate_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ TUpdate Update _ _ 
      subtype_update_Tupdate)
    (WF_Type_update_Tupdate_ext_H2 _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_ext_H3 _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_int_ext _ _ _ _ _ WF_Type subtype Ty_trans N_Wrap TUpdate Update _
      subtype_update_Tupdate)
    (GJ_WF_Type_update_Tupdate _ eq_nat_dec _ Gty _ _ TLookup WF_Type GJ_WF_Type _ 
      TUpdate Update TLookup_Update TLookup_Update' TLookup_TUpdate_eq TLookup_TUpdate_neq
      TLookup_TUpdate_neq' TLookup_id)
    (FJ_WF_Type_update_Tupdate_H1 _ _ _ _ _ _ _ _ WF_Type _ _ _ TUpdate Update _ _ _ CT 
      wf_class_ext wf_object_ext cFJ_WF_Type 
      (WF_Type_update_Tupdate_obj_ext _ _ _ _ _ TUpdate Update _))
    (FJ_WF_Type_update_Tupdate_H2 _ _ _ _ _ _ _ _ WF_Type _ _ _ TUpdate Update _ _ _ 
      CT wf_class_ext wf_object_ext cFJ_WF_Type)
    (I_WF_Type_update_Tupdate _ _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap I_N_Wrap TUpdate Update IT
      I_WF_Type_Wrap).

    Definition WF_fields_build_tys' gamma te (ce : I_cld_ext) := 
      Generic.FJ_WF_fields_build_tys Ty Context WF_Type gamma te (snd ce).

    Fixpoint Ty_trans_fields delta S fds (fields_S : fields delta S fds) :=
      match fields_S return Ty_trans_fields_P _ _ _ Empty Ty_trans _ fields _ _ _ fields_S with
        | FJ_fields gamma ty fds FJ_case => FJ_fields_rect' _ _ _ _ _ _ _ _ _ _ CT 
          _ fields fields_build_te fields_build_tys FJ_fields 
          (Ty_trans_fields_P _ _ _ Empty Ty_trans _ fields)
          (Ty_trans_fields_H1 _ _ _ _ _ _ _ _ Empty Ty_trans _ fields _ _ _ _ _ CT 
          TE_trans FJ_Ty_trans_invert _ _ FJ_fields)
          (Ty_trans_fields_H2 _ _ _ _ _ _ _
            _ Empty subtype Ty_trans WF_Type _ fields _ _ Update
          _ FJ_Ty_Wrap_inject _ _ CT wf_class_ext wf_object_ext E_WF TE_trans FJ_Ty_trans_invert
          ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override WF_CT
          fields_build_te fields_build_tys
          (Generic.GJ_obj_TE_trans_fields_build_te' _ _ _ _ Ty_trans TUpdate _ _ _ _)
          (Generic.GJ_class_TE_trans_fields_build_te' _ _ _ _ _ _ Empty subtype Ty_trans
            WF_Type TUpdate _ _ Free_Vars TE_Free_Vars id (fun te txs FV => FV) 
            (fun te txs FV => FV) TE_trans (fun te te' eq => eq) GJ_TE_Trans_invert
            exists_Free_Vars wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 _)
          (GJ_TE_trans_fields_build_tys' _ _ _ _ _ Empty Ty_trans WF_Type TUpdate _ _ Free_Vars
            TE_Free_Vars id (fun te txs FV => FV) 
            (fun te txs FV => FV) TE_trans (fun te te' eq => eq) GJ_TE_Trans_invert
            exists_Free_Vars wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 _ _ 
            WF_fields_build_tys')
          FJ_fields WF_Type_invert) _ _ _ FJ_case Ty_trans_fields
      end.

    Definition Strengthen_WF_Cast_map := Strengthen_Bound.

    Definition WF_Cast_Map_total := Bound_total.

    Definition WF_Cast_map_sub := WF_mtype_map_sub.

    Lemma Cast_E_inject : forall e e', Cast_E e = Cast_E e' -> e = e'.
      intros; congruence.
    Qed.

    Lemma Cast_map_e_invert : forall XNs (Us : list Ty) (e : Generic_Cast.Cast_E nat ty_ext E) (e' : E),
      E_Ty_Trans XNs Us (Cast_E e) e' ->
      Generic_Cast.E_Ty_Trans nat nat Ty ty_ext E _ Cast_E TE_trans E_Ty_Trans XNs
      Us (Cast_E e) e'.
      intros; inversion H; subst; try (inversion H0; fail); eauto.
    Qed.

  Fixpoint Lem_2_11 gamma e T (WF_e : E_WF gamma e T) :
    Generic.Lem_2_11_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ TUpdate
    Update E E_WF E_Ty_Trans gamma e T WF_e :=
    match WF_e in E_WF gamma e T return Generic.Lem_2_11_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ 
      TUpdate Update E E_WF E_Ty_Trans gamma e T WF_e with
      | Cast_E_WF gamma e ty Cast_case => Generic_Cast.Cast_Lem_2_11 _ _ _ _ _ _ _ _     
        _ _ _ Ty_trans Cast_E TE_trans
        _ app_context E_WF Bound subtype Cast_E_WF subtype_dec 
        Ty_eq_dec _ _ CT build_te cFJ_sub Update E_Ty_Trans TUpdate
        WF_Type Empty Cast_map_e_invert Cast_E_inject WF_mtype_ty_0_map_total
        Trans_WF_mtype_map Subtype_Update_list_id subtype_update_Tupdate
        subst_context Type_Subst_Sub_2_5' WF_Cast_map_sub
        subst_context_Empty app_context_Empty Strengthen_WF_Cast_map subtype_update_list_id'
        sub_Bound FJ_NTy_trans_invert gamma e ty Cast_case Lem_2_11
      | FJ_E_WF gamma e ty FJ_case => Generic.FJ_Lem_2_11 _ eq_nat_dec _ _ Gty _ _ 
        N_Wrap _ _ Empty TLookup subtype Ty_trans
        WF_Type _ fields _ _ _ mtype TUpdate app_context Update _ Subtype_Update_list_id
        _ _ CT build_te cFJ_sub Weakening_2_1_2 _ cFJ_E E_WF lookup
        Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Bound FJ_E_WF Free_Vars
        GJ_Free_Vars' TE_trans FJ_Ty_trans_invert exists_Free_Vars
        N_trans wf_free_vars subst_context TLookup_update_eq TLookup_update_neq
        TLookup_update_neq' Ty_trans_eq_NTy_trans Ty_trans_trans_subst plus Ty_rename NTy_rename
        Ty_rename_eq_NTy_rename rename_context TLookup_rename_context' GJ_Ty_rename_invert
        Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype subst_context_Empty app_context_Empty
        Finite_Context Ty_rename_WF_Type Ty_rename_WF_Type' Type_Subst_Sub_2_5'
        WF_context_shuffle Free_Vars_Ty_Rename Type_Subst_WF_2_6
        subtype_update_Tupdate subtype_update_list_id' WF_Type_update_list_id' WF_Type_update_Tupdate
        mbody_m_call_map mbody_new_map Lem_2_7 E_Ty_Trans map_e_invert
        EWrap_inject lookup_TUpdate lookup_update_eq lookup_update_neq
        lookup_update_neq' lookup_Empty lookup_id eq_nat_dec WF_fields_map_sub
        Lem_2_8' Strengthen_Bound  Ty_trans_fields Trans_WF_fields_map
        (Generic.GJ_mbody_new_map_TE_Trans _ _ _ Ty_trans _) 
        WF_Type_update_list_id  
        update_list_WF_mtype_ty_0_map WF_mtype_U_map_update_list
        WF_mtype_Us_map_update_list WF_mtype_ext_update_list Lem_2_7''
        WF_mtype_map_sub WF_mtype_ty_0_map_total Ty_trans_mtype Lem_2_9 Trans_WF_mtype_map
        _ _ _ FJ_case Lem_2_11
    end.
        
  Definition Ty_trans_app :=
    ty_rect (Ty_trans_app_P _ _ Ty_trans Free_Vars)
    (TE_trans_app_Q _ _ _ TE_Free_Vars TE_trans)
    (GJ_Ty_trans_app _ eq_nat_dec _ Gty _ _ GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_Ty_trans_app _ _ _ _ _ N_Wrap cFJ_N _ FJ_Ty_Wrap_inject _ _ FJ_Free_Vars_invert _ FJ_Ty_trans_invert)
    (I_Ty_trans_app _ _ _ _ _ Ty_trans N_Wrap I_N_Wrap Free_Vars TE_Free_Vars TE_trans I_Free_Vars_invert
      I_Ty_trans_invert I_Ty_Wrap_inject)
    (TE_trans_app_H1 _ _ _ _ Free_Vars)
    (TE_trans_app_H2 _ _ _ _ _ ).

  Definition build_cte_Free_Vars := Generic.build_cte_Free_Vars _ _ Gty N _ _ Free_Vars
    GJ_Free_Vars_invert GJ_Ty_Wrap_inject (fun ce : I_cld_ext => FJ_ce_build_cte (snd ce)).

  Definition GJ_TE_Free_Vars_Wrap (te : GTy_ext Ty) (txs : list _) :
                          GJ_TE_Free_Vars _ _ _ Free_Vars te txs ->
                          TE_Free_Vars (id te) txs := id.

  Definition Ty_trans_no_op := ty_rect
    (Ty_trans_no_op_P _  _ Ty_trans Free_Vars)
    (Ty_trans_no_op_Q _ _ _ TE_Free_Vars TE_trans)
    (GJ_Ty_trans_no_op _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert 
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_Ty_trans_no_op _ _ _ _ _ N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars
      TE_Free_Vars FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (I_Ty_trans_no_op _ _ _ _ _ Ty_trans N_Wrap I_N_Wrap Free_Vars TE_Free_Vars TE_trans
      I_Free_Vars_invert I_Ty_trans_invert I_Ty_Wrap_inject)
    (Ty_trans_no_op_H3 _ _ _ Ty_trans _ Free_Vars id GTy_ext_Wrap_inject)
    (Ty_trans_no_op_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_Wrap
      TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Definition GJ_Free_Vars_Wrap := GJ_Free_Vars'.

  Definition  Ty_trans_fresh_vars :=
    ty_rect (Ty_trans_fresh_vars_P _ _ Gty Ty_trans Free_Vars)
    ( Ty_trans_fresh_vars_Q _ _ _ Gty Free_Vars TE_Free_Vars TE_trans)
    (GJ_Ty_trans_fresh_vars _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_Wrap
      GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert Ty_trans_nil Free_Vars_Subst
      Ty_trans_trans_subst Ty_trans_app Ty_trans_no_op)
    (FJ_Ty_trans_fresh_vars _ _ _ Gty _ _ N_Wrap cFJ_N Ty_trans FJ_Ty_Wrap_inject Free_Vars
      TE_Free_Vars FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (I_Ty_trans_fresh_vars _ _ _ _ _ Ty_trans N_Wrap I_N_Wrap Gty _ _ _ 
      I_Free_Vars_invert I_Ty_trans_invert I_Ty_Wrap_inject)
    (Ty_trans_fresh_vars_H3 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id TE_trans
      GJ_TE_Trans_invert)
    (Ty_trans_fresh_vars_H4 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_Wrap
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Lemma Ty_trans_eq_N_Trans : forall N0 XNs Us,
    N_Wrap (N_Trans XNs Us N0) = Ty_trans (N_Wrap N0) (Extract_TyVar _ N XNs) Us.
    destruct N0; simpl; first [destruct f | destruct i]; reflexivity.
  Qed.

  Definition WF_mtype_U_map'_id := Generic.FJ_WF_mtype_U_map'_id Ty Context.

  Definition WF_mtype_Us_map'_id := Generic.FJ_WF_mtype_Us_map'_id Ty Context.

  Definition mtype_build_tys'_id (ce : I_cld_ext) := Generic.FJ_mtype_build_tys'_id Ty nat (snd ce).

  Definition TE_trans_app (te : ty_ext) := GJ_TE_trans_app _ _ Ty_trans _ Free_Vars Ty_trans_app te.

  Definition exists_TE_Free_Vars (te : ty_ext) := GJ_exists_TE_Free_Vars _ _ _ Free_Vars exists_Free_Vars te.
 
  Fixpoint Strengthen_subtype_update_TList delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return Strengthen_subtype_update_TList_P _ _ subtype _ Update _ _ _ sub_S_T with
      | cFJ_sub delta' S' T' sub_S_T' => FJ_Strengthen_subtype_update_TList _ _ _ _ _ _ _ 
        subtype _ _ _ Update _ _ _ CT build_te cFJ_sub Strengthen_subtype_update_TList _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_Strengthen_subtype_update_TList _ _ Gty _ _ _ TLookup 
        subtype GJ_sub _ Update TLookup_Update _ _ _ sub_S_T'
      | I_subtype_Wrap delta' S' T' sub_S_T' => I_Strengthen_subtype_update_TList _ _ _ _ _ _ _ _ subtype
        N_Wrap I_N_Wrap _ implements cFJ_N Update _ _ _ CT isub_build_te I_subtype_Wrap _ _ _ sub_S_T'
    end.

  Definition Strengthen_WF_Type_update_TList :=
    WF_Type_rect' (Strengthen_WF_Type_update_TList_P _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_Q _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _)
    (Strengthen_WF_Type_update_TList_P1 _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_Q'' _ _ _ _ _ wf_int_ext Update)
    (Strengthen_WF_Type_update_TList_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _
      Strengthen_subtype_update_TList)
    (Strengthen_WF_Type_update_TList_ext_H2 _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_ext_H3 _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_int_ext _ _ _ _ _ WF_Type subtype Ty_trans N_Wrap 
      Update _ Strengthen_subtype_update_TList)
    (GJ_Strengthen_WF_Type_update_TList _ _ Gty _ _ TLookup WF_Type GJ_WF_Type
      _ Update TLookup_Update)
    (FJ_Strengthen_WF_Type_update_TList_H1 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _
      CT wf_class_ext wf_object_ext cFJ_WF_Type
    (Strengthen_WF_Type_update_TList_obj_ext _ _ _ Update _))
    (FJ_Strengthen_WF_Type_update_TList_H2 _ _ _ _ _ _ _ WF_Type _ _ _ 
      Update _ _ _ CT wf_class_ext wf_object_ext cFJ_WF_Type)
    (I_Strengthen_WF_Type_update_TList _ _ _ _ _ _ _ _ _ WF_Type wf_int_ext N_Wrap I_N_Wrap 
      Update IT I_WF_Type_Wrap).

  Definition build_context'_Empty_1 (ce : I_cld_ext) me vds gamma := 
    FJ_build_context'_Empty_1 _ _ _ _ Empty WF_Type _ TUpdate Update (snd ce) me vds gamma.
  
  Definition build_context'_Empty_2  (ce : I_cld_ext) me vds gamma :=
    FJ_build_context'_Empty_2 _ _ _ _ Empty subtype _ TUpdate Update (snd ce) me vds gamma.

  Definition build_context'_Empty_3 (ce : I_cld_ext) me vds gamma := 
    FJ_build_context'_Empty_3 _ _ _ _ Empty _ TUpdate Update _ E_WF (snd ce) me vds gamma.

  Variable build_fresh_distinct : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> distinct Zs.
  Variable build_fresh_new : forall tys ty vds Zs Xs Ws Ys, List_P2' (Free_Vars) tys Zs -> 
    build_fresh tys ty vds Xs Ws Ys -> List_P1 (fun Zs' => forall Y, In Y Ys -> ~ In Y Zs') Zs.
  Variable build_fresh_new' : forall tys ty vds Zs Xs Ws Ys, List_P2' (Free_Vars) vds Zs -> 
    build_fresh tys ty vds Xs Ws Ys -> List_P1 (fun Zs' => forall Y, In Y Ys -> ~ In Y Zs') Zs.
  Variable build_fresh_new'' : forall tys ty vds Ws Xs Ys Zs, Free_Vars ty Ws ->
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Ws.
  Variable build_fresh_new''' : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Xs.
  Variable build_fresh_new''''' : forall tys ty vds Ws Xs Ys Zs, 
    List_P2' Free_Vars (map (fun n => N_Wrap (snd n)) Ys) Ws ->
    build_fresh tys ty vds Xs Ys Zs -> 
    List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.

  Definition Build_S0''' : forall (ce : cld_ext) (me : md_ext)
                   (gamma gamma' : Context) (te te' : ty_ext) 
                   (c : _) (vds : list (Generic.VD Ty _)) 
                   (S0 T0 : Ty) (delta : Context) (e e' : E) 
                   (D D' : Ty) (mtye : mty_ext) 
                   (mce : m_call_ext) (Ds Ds' : list Ty)
                   (Vars : list (Var _ * Ty))
                 (H : L_WF_Ext gamma' ce c),
                 L_build_context ce gamma' ->
                 Meth_WF_Ext gamma ce me ->
                 ce_build_cte ce te' ->
                 (forall (Y : _) (Zs : list _),
                  TE_Free_Vars te' Zs ->
                  In Y Zs ->
                  In Y (Extract_TyVar _ N (fst ce))) ->
                 Meth_build_context ce me
                   (cFJ.update_list _ Ty Context Update Empty
                      ((this _,
                        Generic.FJ_Ty_Wrap Ty ty_ext _ N N_Wrap cFJ_N
                         (ty_def _ ty_ext te' (cl _ c)))
                       :: map
                            (fun Tx : Generic.VD Ty _ =>
                             match Tx with
                             | vd ty x => (var _ x, ty)
                             end) vds)) gamma ->
                 E_WF gamma e S0 ->
                 subtype gamma S0 T0 ->
                 wf_class_ext delta ce te ->
                 mtype_build_mtye ce te T0 vds me mtye ->
                 map_mbody ce te mce me e e' ->
                 mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) ->
                 WF_mtype_U_map delta mce mtye D D' ->
                 WF_mtype_ext delta mce mtye ->
                 WF_mtype_Us_map delta mce mtye Ds Ds' ->
                 List_P1
                   (fun Tx : Generic.VD Ty _ =>
                    match Tx with
                    | vd ty _ => WF_Type gamma ty
                    end) vds ->
                 zip
                   (this _
                    :: map
                         (fun Tx : Generic.VD Ty _ =>
                          match Tx with
                          | vd _ x => var _ x
                          end) vds)
                   (Generic.FJ_Ty_Wrap Ty ty_ext _ N N_Wrap cFJ_N
                      (ty_def _ ty_ext
                         (TE_trans te'
                            (Extract_TyVar _ N (fst ce))
                            (fst te))
                         (cl _ c)) :: Ds') (@pair _ _) = Some Vars ->
                 mtype_build_tys ce te T0 vds me
                   (map
                      (fun vd' : Generic.VD Ty _ =>
                       match vd' with
                       | vd ty _ => ty
                       end) vds) Ds ->
                 exists S0'' : Ty,
                   subtype delta S0'' D' /\
                   E_WF (cFJ.update_list _ Ty Context Update delta Vars) e'
                     S0'' :=
    (fun ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce Ds Ds' Vars H => 
      Generic.GJ_Build_S0''' _ _ _ Gty _ _ N_Wrap cFJ_N
      _ Empty subtype Ty_trans WF_Type _ _ _ build_fresh N_Trans TUpdate
      app_context Update _ _ _ Subtype_Update_list_id _ _ CT build_te
      cFJ_sub E_WF Free_Vars TE_Free_Vars TE_trans FJ_Ty_trans_invert exists_Free_Vars
      wf_free_vars subst_context L_build_context' L_build_context'_Empty_1 Free_Vars_id subst_context_Empty
      app_context_Empty Type_Subst_Sub_2_5' (@id_map_2 _ _ FJ_ty_ext) build_fresh_len subtype_update_Tupdate Ty_trans_app
      TE_trans_app WF_Type_update_Tupdate Strengthen_WF_Type_update_TList E_Ty_Trans _ _ _ _
      (fun gamma (ie : I_cld_ext) c => FJ_L_WF_Ext _ _ gamma (@snd _ _ ie) c )
      (fun (ice : I_cld_ext) mde gamma gamma' => FJ_Meth_build_context _ (snd ice) mde gamma gamma') _ 
      (fun ice te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys') _ _
      (FJ_WF_mtype_Us_map Ty Context) _ _ 
      mtype_build_tys_len Weaken_WF_Type_app_TList build_context'_Empty_1
      build_context'_Empty_2 build_context'_Empty_3 Ty_trans_eq_N_Trans
      Lem_2_11 build_fresh_distinct build_fresh_id Ty_trans_fresh_vars build_fresh_new build_fresh_new' 
      build_fresh_new'' build_fresh_new''' build_fresh_new''''' WF_mtype_U_map'_id 
      WF_mtype_Us_map'_id mtype_build_tys'_id exists_TE_Free_Vars id 
      ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce Ds Ds' Vars (proj1 H)).

  Lemma WF_class_ext_TE_trans (gamma delta : Context) (c : nat) (ce : cld_ext) 
    (te te' : ty_ext) (_ : ce_build_cte ce te') (_ : L_WF_Ext gamma ce c)
    (wf_c : wf_class_ext delta ce te) : 
    te = TE_trans te' (Extract_TyVar _ _ (fst (ce))) (fst (te)) .
    eapply GJ_WF_class_ext_TE_trans.
    apply GJ_Ty_trans_invert.
    destruct te0; destruct te'0; reflexivity.
    unfold wf_class_ext in wf_c; unfold wf_class_ext' in wf_c.
    unfold id; apply wf_c.
    unfold id; apply H0.
    apply H.
  Qed.


  Definition Build_S0'' :=
    Generic.Build_S0'' _ _ _ _ _ N_Wrap cFJ_N _ 
    Empty subtype WF_Type _ _ Update _ I_cld_ext _ _ wf_class_ext
    m_call_ext E_WF WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext TE_Free_Vars TE_trans ce_build_cte 
    Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context FJ_ty_ext id mtype_build_mtye
    id build_cte_Free_Vars WF_class_ext_TE_trans map_mbody mtype_build_tys
    Build_S0'''.  
  
  Definition Term_subst_pres_typ_def := 
    cFJ.Term_subst_pres_typ_P _ _ _ _ subtype E_WF Update trans.
  
  Fixpoint Weaken_subtype_Update_list delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return 
      (Generic.Weaken_subtype_Update_list_P _ _ subtype _ Update delta S T sub_S_T) with
      | cFJ_sub gamma' S' T' sub_S_T' =>
        FJ_Weaken_subtype_Update_list _ _ _ _ _ _ _ subtype _ _ _ Update _ _ _ CT
        build_te cFJ_sub Weaken_subtype_Update_list _ _ _ sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Weaken_subtype_Update_list
        _ _ _ _ _ _ TLookup subtype GJ_sub _ Update TLookup_Update _ _ _ sub_S_T'
      | I_subtype_Wrap _ _ _ sub_S_T' =>
        I_Weaken_subtype_Update_list _ _ _ _ _ _ N _ _ N_Wrap I_N_Wrap _ _ cFJ_N _ _ _ _ CT
        _ I_subtype_Wrap _ _ _ sub_S_T'
    end.

  Definition Weaken_WF_Update_list :=
    WF_Type_rect' (Generic.Weaken_WF_Update_list_P _ _ WF_Type _ Update)
    (Weaken_WF_Update_list_Q _ _ _ _ Update _ wf_class_ext)
    (Generic.Weaken_WF_Update_list_P1 _ _ WF_Type _ Update)
    (Weaken_WF_Update_list_Q'' _ _ _ _ _ wf_int_ext Update)
    (Weaken_WF_Update_list_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update
      _ _ Weaken_subtype_Update_list)
    (Weaken_WF_Update_list_ext_H2 _ _ _ _ _)
    (Weaken_WF_Update_list_ext_H3 _ _ _ _ _)
    (I_Weaken_WF_Update_list_ext _ _ _ _ _ _ _ Ty_trans N_Wrap _ _ _ Weaken_subtype_Update_list)
    (GJ_Weaken_WF_Update_list _ _ Gty _ _ TLookup _ GJ_WF_Type _ Update TLookup_Update)
    (FJ_Weaken_WF_Update_list_H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CT _ _ cFJ_WF_Type
      (GJ_Weaken_WF_Update_list_obj_ext _ _ _ Update _))
    (FJ_Weaken_WF_Update_list_H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cFJ_WF_Type)
    (I_Weaken_WF_Update_list _ _ _ _ _ _ _ _ _ _ _ N_Wrap I_N_Wrap _ IT
      I_WF_Type_Wrap).

  Definition WF_mtype_ext_update_list_id' := Generic.WF_mtype_ext_update_list_id' _ _ N N_Wrap _ 
    subtype Ty_trans WF_Type _ Update Weaken_subtype_Update_list
    Weaken_WF_Update_list _ _ _ 
    (fun delta mce mtye vars => FJ_WF_mtype_ext_update_list_id _ _ _ Update delta vars mce mtye).
  
  Definition Term_subst_pres_typ_P := 
    cFJ.Term_subst_pres_typ_P _ _ _ _ subtype E_WF Update trans.

  Definition WF_mtype_ext_Weaken_update_list gamma vars mce mtye := 
    WF_mtype_ext_update_list_id' gamma mce mtye vars.

  Lemma Cast_E_trans_Wrap : forall (e : Cast.Cast_E nat ty_ext E) (vars : list (Var nat)) (es' : list E),
    trans (Cast_E e) vars es' =
    Cast_E (Cast_E_trans nat ty_ext E nat trans e vars es').
    simpl; reflexivity.
  Qed.

  Fixpoint Subtype_Update_list_id'' gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T in (subtype gamma S T) return 
      (Cast.Subtype_Update_list_id'_P _ _ subtype nat Update gamma S T sub_S_T) with
      | cFJ_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Update_list_id' _ _ _ _ _ _ subtype _ _ _ _ _ CT
        build_te Update cFJ_sub gamma' S' T' sub_S_T' Subtype_Update_list_id''
      | GJ_sub gamma' S' T' sub_S_T' => 
        Generic_Cast.Subtype_Update_list_id' _ _ _ _ _
        _ subtype TLookup Gty GJ_sub Update TLookup_Update' gamma' S' T' sub_S_T'
      | I_subtype_Wrap gamma' S' T' sub_S_T' => I_Subtype_Update_list_id'
        _ _ _ I_Ty_Wrap  _ _ _ _ _ _ _ _ CT isub_build_te implements FJ_Ty_Wrap subtype
        I_subtype_Wrap Update _ _ _ sub_S_T'
    end.

  Fixpoint Term_subst_pres_typ gamma e T (WF_e : E_WF gamma e T) :
    Term_subst_pres_typ_P gamma e T WF_e :=
    match WF_e with 
      | Cast_E_WF gamma e ty Cast_case => Cast_Term_subst_pres_typ _ _ _ _
        _ _ Cast_E E_WF Bound subtype Cast_E_WF _ _ _ _ _ CT build_te Update
        cFJ_sub subtype_dec Ty_eq_dec trans Cast_E_trans_Wrap 
        Subtype_Update_list_id Subtype_Update_list_id''
        WF_mtype_ty_0_map_Weaken_update_list WF_mtype_ty_0_map_total sub_Bound _ _ _ 
        Cast_case Term_subst_pres_typ        
      | FJ_E_WF gamma e ty FJ_case => FJ_Term_subst_pres_typ _ _ _ _ _ _ 
        _ _ _ cFJ_E mty_ext _ _ CT _ subtype build_te
        cFJ_sub WF_Type fields mtype 
        E_WF lookup Bound Bound WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF Update
        trans eq_nat_dec lookup_update_eq lookup_update_neq'
        lookup_id E_trans_Wrap Lem_2_8' Lem_2_9 
        (fun d v ty ty' B => WF_mtype_ty_0_map_Weaken_update_list _ _ _ B d v (refl_equal _))
        (fun d v ty ty' B => WF_mtype_ty_0_map_Weaken_update_list _ _ _ B d v (refl_equal _))
        (fun g v mc mty u u' => WF_mtype_U_map_Weaken_update_list g v mc u u' mty)
        (fun d v mc mt us us' => WF_mtype_Us_map_Weaken_update_list d v mc us us' mt)
        WF_mtype_ext_Weaken_update_list WF_mtype_ty_0_map_total 
        Subtype_Update_list_id WF_Type_update_list_id gamma e ty FJ_case Term_subst_pres_typ
    end.

  Definition build_te_id' :=
    build_te_id' _ _ N Ty_trans _ _ (fun (ice : I_cld_ext) te te' te''=> FJ_mbody_build_te (snd ice) te te' te'') 
    (fun (ice : I_cld_ext) te te' te'' => FJ_build_te (snd ice) te te' te'') (fun ice => FJ_build_te_id (snd ice)).
     
  Lemma mtype_invert : forall (gamma : Context) (m0 : nat) (te : ty_ext) 
    (c : nat) (mty : Mty Ty mty_ext),
    mtype gamma m0 (FJ_Ty_Wrap (ty_def nat ty_ext te (cl nat c))) mty ->
    cFJ.FJ_mtype nat nat nat nat ty_ext Ty FJ_Ty_Wrap E mty_ext
    md_ext cld_ext CT Context mtype mtype_build_te mtype_build_tys
    mtype_build_mtye gamma m0
    (FJ_Ty_Wrap (ty_def nat ty_ext te (cl nat c))) mty.
    intros; inversion H; subst; try assumption.
    inversion H0.
  Qed.
  
  Definition WF_mtype_Us_map_len' := WF_mtype_Us_map_len' _ _ N _ Ty_trans _ _ 
    _ (FJ_WF_mtype_Us_map_len _ Context).

  Lemma Base_inject : forall ty ty', FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.

  Definition methods_build_te_id' := methods_build_te_id' _ _ _ N Ty_trans _ _ _ 
    (fun (ce : I_cld_ext) te te' te'' => FJ_methods_build_te_id (snd ce) te te' te'').

   Definition WF_Type_par delta ty (WF_ty : WF_Type delta ty) := 
     match WF_ty in (WF_Type delta ty) return 
       cFJ.WF_Type_par_P _ _ _ _ ty_ext Ty FJ_Ty_Wrap E _ _ CT _ WF_Type mtype_build_te
       L_build_context delta ty WF_ty with 
       | I_WF_Type_Wrap gamma ty WF_int => 
         Interface.WF_Type_par _ _ _ I_Ty_Wrap _ _ _ _ _ IT _ _ _ _ cld_ext CT
         (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) 
         wf_int_ext WF_Type I_WF_Type_Wrap mtype_build_te L_build_context 
         Ty_discriminate gamma ty WF_int
       | cFJ_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par _ _ _ _ _ _ _ _ _ _ CT Context 
         wf_class_ext wf_object_ext WF_Type cFJ_WF_Type mtype_build_te
         L_build_context Base_inject WF_Type_par_Lem WF_Type_par_Lem' gamma ty WF_base
       | GJ_WF_Type delta ty WF_ty => GJ_WF_Type_par _ _ _ Gty _ _ N_Wrap _ _ 
         TLookup WF_Type GJ_WF_Type _ _ _ _ Ty_Wrap_discriminate _ _ CT L_build_context 
         _ delta ty WF_ty
     end.

  Definition WF_mb_ext (gamma : Context) (mbe : mb_ext) : Prop := True.

  Lemma WF_Build_mb_ext : forall (ce : cld_ext) (me : md_ext) 
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
                          ((this _, FJ_Ty_Wrap (ty_def _ ty_ext te' (cl _ c)))
                           :: map
                                (fun Tx : cFJ.VD _ Ty =>
                                 match Tx with
                                 | vd ty x => (var _ x, ty)
                                 end) vds)) gamma ->
                     WF_Type delta (FJ_Ty_Wrap (ty_def _ ty_ext te (cl _ c))) ->
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
                       (FJ_Ty_Wrap (ty_def _ ty_ext te'' (cl _ c)) :: Ds') (@pair _ _) =
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
    mb_ext build_mb_ext map_mbody
    E_WF Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty Update
    ce_build_cte Meth_build_context Meth_WF_Ext
    override L_WF_Ext L_build_context WF_CT Base_inject 
    Build_S0''  WF_mb_ext WF_Build_mb_ext WF_mtype_Us_map_len' mtype_build_tys_len' methods_build_te_id' WF_Type_par
    build_te_id' mtype_invert 
    (WF_mtype_ty_0_map_cl_id'' _ _ _ _ _ _ _ Bound N_Bound'_invert) 
    (WF_mtype_ty_0_map_tot' _ _ _ _ _ _ _ Bound N_Bound) WF_Type_invert.

  Lemma FJ_E_WF_invert : forall gamma (e : FJ_E _ _ _ _ _ _ _ ) c0, 
    E_WF gamma (cFJ_E e) c0 -> cFJ.FJ_E_WF _ _ _ _ _ Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N)
    _ _ cFJ_E mty_ext
    Context subtype WF_Type fields mtype
    E_WF lookup Bound Bound WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty gamma (cFJ_E e) c0.
    intros; inversion H; subst; try assumption; inversion H0.
  Qed.
  
  Definition preservation_def := cFJ.preservation Ty E Context subtype E_WF Reduce.
  
  Definition Reduce_List_preservation es es' (red_es : Congruence_List_Reduce es es') :=
    cFJ.Reduce_List_preservation _ _ _ subtype E_WF Congruence_List_Reduce es es' red_es.
        
  Definition WF_fields_map_sub' := 
    WF_fields_map_sub' _ _ _ _ _ _ _ Empty subtype _ fields _ _ _ Bound _ _ CT build_te
    cFJ_sub N_Wrap_inject N_Bound'_invert FJ_N_Ty_Wrap_inject fields_id.
  
    Lemma FJ_E_WF_new_invert : forall gamma e T T0, 
      E_WF gamma (cFJ_E (cFJ.new nat nat nat nat ty_ext E m_call_ext T e)) T0 ->
      N_Wrap (cFJ_N T) = T0.
      intros; inversion H; subst.
      inversion H0; subst.
      destruct te; reflexivity.
      inversion H0.
    Qed.

    Lemma Cast_E_WF_invert : forall gamma e c0, E_WF gamma (Cast_E e) c0 -> 
      Cast.Cast_E_WF _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ 
      Cast_E E_WF Bound subtype gamma (Cast_E e) c0.
      intros; inversion H; subst.
      inversion H0.
      assumption.
    Qed.

  Fixpoint preservation e e' (red_e : Reduce e e') : preservation_def _ _ red_e :=
    match red_e with 
      |  FJ_S_Reduce t t' red_t => FJ_pres _ _ _ _ _ _ _ _ _ 
        cFJ_E _ _ _ CT _ subtype build_te cFJ_sub WF_Type fields
        mtype mbody_build_te mb_ext build_mb_ext
        map_mbody E_WF lookup
        Bound Bound WF_mtype_Us_map WF_mtype_U_map
        WF_mtype_ext Empty FJ_E_WF Update trans
        Reduce FJ_S_Reduce FJ_E_WF_invert EWrap_inject
        Fields_eq fds_distinct WF_fields_map_id 
        (fun g tye c ty' Bnd => WF_fields_map_id' g _ _ Bnd tye c (refl_equal _))
        WF_fields_map_sub' Subtype_Weaken WF_mtype_map_sub Term_subst_pres_typ WF_mb_ext Lem_2_12
        t t' red_t
      | Cast_Reduce e e' cast_red_e => Cast_preservation' _ _ _ 
        (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ Cast_E
        E_WF Bound subtype Reduce _ _ _ _ _ _ cFJ_E CT build_te Empty Cast_Reduce 
        cFJ_sub Cast_E_WF_invert Cast_E_inject FJ_E_WF_new_invert
        Subtype_Weaken WF_mtype_map_sub e e' cast_red_e
      | Cast_C_Reduce e e' cast_c_red_e => Cast_C_preservation' _ _ _ _ _ _ Cast_E
        E_WF Bound subtype Cast_E_WF _ _ _ _ _ CT build_te Reduce Cast_C_Reduce
        cFJ_sub subtype_dec Ty_eq_dec WF_mtype_ty_0_map_total sub_Bound Cast_E_WF_invert Cast_E_inject
        e e' cast_c_red_e preservation       
      | FJ_C_Reduce e e' fj_red_e' => FJ_C_preservation _ _ _ _ ty_ext _ _ _ _ cFJ_E _ _ _ CT
        _ subtype build_te cFJ_sub WF_Type fields mtype E_WF lookup Bound
        Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF 
        Reduce Congruence_List_Reduce FJ_C_Reduce FJ_E_WF_invert EWrap_inject
        Lem_2_8' Lem_2_9 WF_mtype_ty_0_map_total e e' fj_red_e'
        preservation (fix preservation_list (es es' : list E) (red_es : Congruence_List_Reduce es es') : 
          Reduce_List_preservation _ _ red_es :=
          match red_es return Reduce_List_preservation _ _ red_es with
            FJ_Reduce_List es es' red_es' => FJ_C_List_preservation _ _ _ _ _ _ _ _ _ _ 
            CT _ subtype build_te cFJ_sub E_WF Reduce
            Congruence_List_Reduce FJ_Reduce_List es es' red_es' preservation preservation_list end)      
    end.

  Inductive subexpression : E -> E -> Prop :=
    FJ_subexpression_Wrap : forall e e', FJ_subexpression _ _ _ _ _ _ _ cFJ_E subexpression subexpression_list e e' -> subexpression e e'
  | Cast_subexpression_Wrap : forall e e', Cast_subexpression _ _ _ Cast_E subexpression e e' -> subexpression e e'
  with subexpression_list : E -> list E -> Prop :=
    subexpression_list_Wrap : forall e es, FJ_subexpression_list _ subexpression subexpression_list e es ->
      subexpression_list e es.

  Definition progress_1_P := cFJ.progress_1_P _ _ _ _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N)
    _ _ cFJ_E _ fields E_WF Empty subexpression.
  
  Definition progress_1_list_P := cFJ.progress_1_list_P _ _ _ _ _ _ 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ cFJ_E 
    _ fields E_WF Empty subexpression_list.
  
  Lemma subexp_invert : forall (e : E) e',
    subexpression e (cFJ_E e') ->
    FJ_subexpression nat nat nat nat ty_ext E m_call_ext cFJ_E subexpression subexpression_list e (cFJ_E e').
    clear; intros; inversion H; subst; auto; inversion H0.
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
    (S : cFJ.FJ_Ty _ ty_ext) (e' : E), cFJ_E e <> Cast_E (cast _ ty_ext E S e').
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
      | FJ_E_WF gamma e ty FJ_case => cFJ.progress_1 _ _ _ _ _ _ _ _ _ cFJ_E _ _ subtype
        WF_Type fields mtype E_WF lookup Bound Bound WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert EWrap_inject
        WF_fields_map_id (fun g tye c ty' Bnd => WF_fields_map_id' g _ _ Bnd tye c (refl_equal _))
        subexpression subexpression_list 
        subexp_invert subexpression_list_nil subexpression_list_destruct gamma e ty FJ_case progress_1
      | Cast_E_WF gamma e ty Cast_case => Cast_progress_1 _ _ _ _
        _ _ Cast_E E_WF Bound subtype Cast_E_WF _ _ _ _ cFJ_E Empty Cast_E_inject fields 
        subexpression Cast_subexp_invert FJ_Cast_discriminate gamma e ty Cast_case progress_1
    end.
  
  Definition progress_2_P := cFJ.progress_2_P _ _ _ _ _ _ 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ cFJ_E _ _ CT _ 
    mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty subexpression.
  
  Definition progress_2_list_P := cFJ.progress_2_list_P _ _ _ _ _ _ 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) _ _ cFJ_E _ _ 
    CT _ mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty 
    subexpression_list.
  
  Definition WF_mtype_ty_0_map_Empty_refl := FJ_WF_mtype_ty_0_map_Empty_refl _ _ _ 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) Context.
  
  Definition build_mb_ext_tot := Generic.build_mb_ext_tot _ _ Gty N Ty_trans _ build_fresh _ _ _ _ _ 
    (fun (ice : I_cld_ext) => FJ_build_mb_ext (snd ice))
    (fun (ice : I_cld_ext) te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys')
    (fun ice => FJ_build_mb_ext_tot nat Ty (snd ice)).

  Definition mbody_m_call_map_tot := GJ_mbody_m_call_map_tot _ _ N Ty_trans FJ_m_call_ext.
    
  Definition mbody_new_map_tot := GJ_mbody_new_map_tot _ _ N Ty_trans FJ_ty_ext.

  Fixpoint E_Ty_trans_tot (e : E) :=
    match e return E_Ty_Trans_tot_P _ _ _ _ E_Ty_Trans e with
      | cFJ_E e' => FJ_E_Ty_Trans_tot _ _ _ _ _ _ _ _ _ _ cFJ_E mbody_m_call_map mbody_new_map
        E_Ty_Trans Base_E_Ty_Trans mbody_m_call_map_tot mbody_new_map_tot E_Ty_trans_tot e'
      | Cast_E e' => Cast_E_Ty_Trans_tot _ _ _ _ _ _ Cast_E TE_trans _ Cast_E_Ty_Trans E_Ty_trans_tot e'
    end.

  Definition map_mbody_tot := Generic.map_mbody_tot _ _ Gty _ Ty_trans _ build_fresh _ _ FJ_m_call_ext _ _ _ 
    (fun (ice : I_cld_ext) te ty vds mce tys tys' => FJ_mtype_build_tys nat _ (snd ice) te ty vds mce tys tys')
    E_Ty_trans_tot.
  
  Definition mtype_mbody_build_te := mtype_mbody_build_te _ _ _ N Ty_trans I_cld_ext 
    (fun (ice : I_cld_ext) te te' te'' => FJ_mtype_build_te (snd ice) te te' te'') _ 
    (fun ice => FJ_mtype_mbody_build_te (snd ice)).

  Fixpoint mtype_implies_mbody gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
    match mtype_m with 
      | FJ_mtype gamma' m' ty' mty' fj_mtype_m => 
        FJ_mtype_implies_mbody _ _ _ _ _ _ _
        _ _ _ _ _ CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye
        FJ_mtype mbody_build_te mb_ext build_mb_ext map_mbody
        Empty cFJ_inject mtype_build_tys_len' map_mbody_tot
        mtype_mbody_build_te build_mb_ext_tot gamma' m' ty' mty' fj_mtype_m mtype_implies_mbody
      | I_mtype_Wrap gamma' m' ty' mty' i_mtype_m' => I_mtype_implies_mbody _ _ _ I_Ty_Wrap
        _ _ _ _ _ IT imtype_build_tys imtype_build_mtye mtype I_mtype_Wrap _ _ _ _ _ CT
        (Generic.FJ_Ty_Wrap Ty ty_ext nat N N_Wrap cFJ_N) 
        Empty Ty_discriminate m_call_ext mbody_build_te mb_ext 
        (fun ty mce ty' mde mbe => True) map_mbody gamma' m' ty' mty' i_mtype_m'
    end.
    
  Fixpoint progress_2 gamma e T (WF_e : E_WF gamma e T) :
    progress_2_P gamma e T WF_e :=
    match WF_e with 
      | FJ_E_WF gamma e ty FJ_case => FJ_progress_2 _ _ _ _ _ _ _ _ _ cFJ_E 
        _ _ _ CT _ subtype WF_Type fields mtype mbody_build_te mb_ext
        build_mb_ext map_mbody E_WF lookup Bound Bound
        WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert
        EWrap_inject WF_mtype_Us_map_len' subexpression subexpression_list
        subexp_invert subexpression_list_nil subexpression_list_destruct
        (WF_mtype_ty_0_map_Empty_refl' _ _ _ _ _ _ _ Bound N_Bound'_invert) 
        mtype_implies_mbody gamma e ty FJ_case progress_2
      | Cast_E_WF gamma e ty Cast_case => Cast_progress_2 _ _ _ _
        _ _ Cast_E E_WF Bound subtype Cast_E_WF _ _ _ _ _ _ cFJ_E CT Empty Cast_E_inject  
        subexpression mbody_build_te mb_ext (fun ce te mce mde mbe => True) map_mbody
        Cast_subexp_invert FJ_Cast_discriminate gamma e ty Cast_case progress_2
  end.

End Preservation.
