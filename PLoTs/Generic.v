Require Import FJ_tactics.
Require Import cFJ.
Section GJ_definitions.

Require Import List.
Variable TX : Set.
Variable TX_eq_dec : forall (tx ty : TX), {tx = ty} + {tx <> ty}.

Inductive GTy : Set :=
  TyVar : TX -> GTy.

Variables (Ty : Set)
  (ty_ext : Set)
  (Ty_Wrap : GTy -> Ty).

Coercion Ty_Wrap : GTy >-> Ty.

Definition GTy_ext {ty_ext : Set} := (prod (list Ty) ty_ext).

Definition GTy_Pass {ty_ext A B: Set} (f : list Ty -> A) (g : ty_ext -> B) (ty : @GTy_ext ty_ext) := 
  (f (fst ty), g (snd ty)).

Variable C : Set.

Variable N : Set.
Variable N_Wrap : N -> Ty.
Coercion N_Wrap : N >-> Ty.

Definition Base_Ty := FJ_Ty C ty_ext.

Variable FJ_N_Ty_Wrap : Base_Ty -> N.
Coercion FJ_N_Ty_Wrap : Base_Ty >-> N.

Definition TyP_List := list (GTy * N).

Definition mty_ext {mty_ext : Set} := (prod TyP_List mty_ext).
Definition MD_ext {md_def_ext : Set} := (prod TyP_List md_def_ext).

Definition cld_ext {cld_def_ext : Set} := prod TyP_List cld_def_ext.

Variable Context : Set.

Variable Empty : Context. (*** The Empty Context ***)
Definition GJ_Context {Context : Set} := prod (list (TX * Ty)) Context.
Definition GJ_Empty {Context : Set} {Empty : Context} : @GJ_Context Context := (nil, Empty).

Variable TLookup : Context -> TX -> N -> Prop.

Inductive GJ_subtype : Context -> Ty -> Ty -> Prop :=
  sub_Var : forall gamma x ty, TLookup gamma x ty -> GJ_subtype gamma (TyVar x) ty.

Variables (subtype : Context -> Ty -> Ty -> Prop)
  (subtype_Wrap : forall {gamma : Context} {ty ty' : Ty}, GJ_subtype gamma ty ty' -> subtype gamma ty ty').

Definition TyVar_Context {Context : Set} := prod (list (TX * Ty)) Context.
Inductive TyVar_Lookup : list (TX * Ty) -> TX -> Ty -> Prop :=
  Found : forall tx ty delta, TyVar_Lookup ((tx, ty) :: delta) tx ty
| Next : forall d tx ty delta, TyVar_Lookup delta tx ty -> TyVar_Lookup (d :: delta) tx ty.
Definition TLookup_Context {Context : Set} : @TyVar_Context Context -> TX -> Ty -> Prop :=
  fun delta tx ty => TyVar_Lookup (fst delta) tx ty.

Fixpoint GTy_trans gty txs tys : Ty :=
  match txs, tys, gty with
    tx :: txs', ty' :: tys', TyVar y => if (TX_eq_dec tx y) then ty' else GTy_trans gty txs' tys'
    | _, _, _ => gty
  end.

Fixpoint GTy_rename gty txs tys : GTy :=
  match txs, tys, gty with
    tx :: txs', ty' :: tys', TyVar y => if (TX_eq_dec tx y) then TyVar ty' else GTy_rename gty txs' tys'
    | _, _, _ => gty
  end.

Variable Ty_trans : Ty -> list TX -> list Ty -> Ty.

Definition Extract_TyVar (typs : TyP_List) : list TX := 
  map (fun x => match (@fst GTy N x) with TyVar y => y end) typs.

Definition Tys_Trans (typs : TyP_List) (tys tys' : list Ty) : list Ty :=
  map (fun ty' => Ty_trans ty' (Extract_TyVar typs) tys) tys'.

Inductive GJ_build_te {cld_def_ext ty_ext : Set}
  (build_te : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) : 
  @cld_ext cld_def_ext -> (@GTy_ext ty_ext) -> (@GTy_ext ty_ext) -> (@GTy_ext ty_ext) -> Prop :=
| Build_te : forall ce te te' te'' (typs : TyP_List) tys tys', 
  build_te ce te te'' te' -> 
  length typs = length tys -> 
  GJ_build_te build_te (typs, ce) (tys, te) (tys', te'') (Tys_Trans typs tys tys', te').

Inductive GJ_WF_Type : Context -> Ty -> Prop :=
  WF_TVar : forall delta tx ty, TLookup delta tx ty -> GJ_WF_Type delta (TyVar tx).

Variables (WF_Type : Context -> Ty -> Prop)
  (GJ_WF_Type_Wrap : forall {gamma : Context} {ty : Ty}, GJ_WF_Type gamma ty -> WF_Type gamma ty).

Inductive GJ_wf_class_ext {cld_def_ext ty_ext : Set} : 
  Context -> @cld_ext cld_def_ext -> (@GTy_ext ty_ext) -> Prop :=
  wf_class_ext : forall ce delta (typs : TyP_List) tys te, 
    List_P1 (WF_Type delta) tys -> (*** All type are well-formed ***)
    length typs = length tys -> (*** Same number of type arguments and type parameters ***)
    List_P2 tys (*** Each type argument is a subtype of the declared type bound ***)
    (map (fun (typ' : GTy * N) => Ty_trans 
      (snd typ') (Extract_TyVar typs) tys) typs) (subtype delta) ->
    GJ_wf_class_ext delta (typs, ce) (tys, te).

Inductive GJ_wf_object_ext {ty_ext : Set} : 
  Context -> (@GTy_ext ty_ext) -> Prop :=
  wf_object_ext : forall delta te, GJ_wf_object_ext delta (nil, te).

Variable F : Set.
Definition FD := FD F Ty.
Variable fields : Context -> Ty -> list FD -> Prop.

Inductive GJ_fields : Context -> Ty -> list FD -> Prop :=
  Var_fields : forall gamma tx fds ty, TLookup gamma tx ty -> fields Empty ty fds -> GJ_fields gamma (TyVar tx) fds.

Inductive fields_build_te {cld_def_ext ty_ext : Set} 
  (fields_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) :
  @cld_ext cld_def_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> Prop :=
  GJ_field_build_te : forall (ce : cld_def_ext) (te te' te'' : ty_ext) typs (tys tys' : list Ty), 
    fields_build_te' ce te te'' te' ->
    length typs = length tys -> 
    fields_build_te fields_build_te' (typs, ce) (tys, te) (tys', te'') (Tys_Trans typs tys tys', te').

Inductive fields_build_tys {cld_def_ext ty_ext : Set} 
  (fields_build_tys' : ty_ext -> cld_def_ext -> list Ty -> list Ty -> Prop) :
  @GTy_ext ty_ext -> @cld_ext cld_def_ext -> list Ty -> list Ty -> Prop :=
  GJ_build_tys : forall (ce : cld_def_ext) (te : ty_ext) (typs : TyP_List) (tys tys' fd_tys : list Ty),
    fields_build_tys' te ce fd_tys tys' ->
    fields_build_tys fields_build_tys' (tys, te) (typs, ce) fd_tys (Tys_Trans typs tys tys').


Variable (M X mty_def_ext : Set).

Definition Mty := cFJ.Mty Ty mty_def_ext.

Variable (mtype : Context -> M -> Ty -> Mty -> Prop)
  (build_fresh : list Ty -> Ty -> list Ty -> list TX -> TyP_List -> list TX -> Prop).

Inductive GJ_mtype : Context -> M -> Ty -> Mty -> Prop :=
  Var_mtype : forall gamma m tx ty mty, TLookup gamma tx ty -> mtype gamma m ty mty -> GJ_mtype gamma m ty mty.

Inductive mtype_build_te {cld_def_ext ty_ext : Set} 
  (mtype_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) :
  @cld_ext cld_def_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> Prop :=
  GJ_mtype_build_te : forall (ce : cld_def_ext) (te te' te'' : ty_ext) typs (tys tys' : list Ty), 
    mtype_build_te' ce te te'' te' -> length typs = length tys -> 
    mtype_build_te mtype_build_te' (typs, ce) (tys, te) (tys', te'')
    (Tys_Trans typs tys tys', te').

Definition VD := cFJ.VD X Ty.

Inductive mtype_build_tys {cld_def_ext ty_ext md_def_ext : Set}
  (mtype_build_tys' : cld_def_ext -> ty_ext -> Ty -> list VD -> md_def_ext -> list Ty -> list Ty -> Prop) :
  @cld_ext cld_def_ext -> @GTy_ext ty_ext -> Ty -> list VD -> @MD_ext md_def_ext -> list Ty -> list Ty -> Prop :=
  GJ_mtype_build_tys : forall (ce : cld_def_ext) (te : ty_ext) (typs typs': TyP_List) 
    (ty : Ty) vds (me : md_def_ext) (fresh_tys : list TX) (tys tys' vd_tys : list Ty),
    length typs = length tys -> 
    mtype_build_tys' ce te ty vds me vd_tys tys' -> (*** Map the parameter types using the previous definitions ***)
    build_fresh tys ty (map (fun vd' : VD => match vd' with | vd ty _ => ty end) vds)
    (Extract_TyVar typs) typs' fresh_tys -> (*** Get fresh vars that aren't in tys ***)
    mtype_build_tys mtype_build_tys' (typs, ce) (tys, te) ty vds (typs', me) 
    vd_tys (Tys_Trans typs tys (Tys_Trans typs' (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys) tys')).

Definition GJ_N_Trans {ty_ext : Set} 
  (N_Trans' : TyP_List -> list Ty -> ty_ext -> ty_ext) (typs : TyP_List) (tys : list Ty) (te : @GTy_ext ty_ext) :  
  @GTy_ext ty_ext :=
  match te with
    (tys', te') => (Tys_Trans typs tys tys', N_Trans' typs tys te')
  end.

Variable N_Trans : TyP_List -> list Ty -> N -> N.

Definition Typs_Trans (typs : TyP_List) (tys : list Ty) (typs' : TyP_List) : TyP_List :=
  map (fun (typ' : GTy * N) => (fst typ', N_Trans typs tys (snd typ'))) typs'. 

Inductive mtype_build_mtye {cld_def_ext ty_def_ext md_def_ext mty_def_ext : Set}
  (mtype_build_mtye' : cld_def_ext -> ty_def_ext -> Ty -> list VD -> md_def_ext -> mty_def_ext -> Prop) : 
  @cld_ext cld_def_ext -> @GTy_ext ty_def_ext -> Ty -> list VD -> @MD_ext md_def_ext -> @mty_ext mty_def_ext -> Prop :=
  GJ_mtype_build_mtye : forall (ce : cld_def_ext) (te : ty_def_ext) (me : md_def_ext) (mtye : mty_def_ext)
    (typs typs' : TyP_List) (ty : Ty) (vds : list VD) (tys : list Ty)
    (fresh_tys : list TX) (ZQs' : TyP_List)
    (eq_ZQs' : zip fresh_tys 
      (map (fun (typ' : GTy * N) => N_Trans typs' (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys) (snd typ')) typs') (*** Patch up Bounds***)
    (fun x => @pair _ _ (TyVar x)) = Some ZQs'),
    mtype_build_mtye' ce te ty vds me mtye -> 
    build_fresh tys ty (map (fun vd' : VD => match vd' with | vd ty _ => ty end) vds)
    (Extract_TyVar typs) typs' fresh_tys -> (*** Get fresh vars that aren't in tys ***)
    mtype_build_mtye mtype_build_mtye' (typs, ce) (tys, te) ty vds (typs', me) 
    (Typs_Trans typs tys ZQs', mtye).

Inductive mbody_build_te {cld_def_ext ty_ext : Set} 
  (mbody_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) :
  @cld_ext cld_def_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> @GTy_ext ty_ext -> Prop :=
  GJ_mbody_build_te : forall (ce : cld_def_ext) (te te' te'' : ty_ext) typs (tys tys' : list Ty), 
    mbody_build_te' ce te te'' te' -> length typs = length tys -> 
    mbody_build_te mbody_build_te' (typs, ce) (tys, te) (tys', te'') (Tys_Trans typs tys tys', te').

Definition MCall_ext {m_call_ext : Set} := (prod (list Ty) m_call_ext).
Definition New_ext {new_ext : Set} := (prod (list Ty) new_ext).

Section map_mbody_Section.

  Variable m_call_ext m_call_ext' : Set.
  Variable ty_def_ext : Set.
  Variable E : Set.
  Variable FJ_E_Wrap : FJ_E C F M X ty_ext E m_call_ext -> E.
  Variable mbody_m_call_map : TyP_List -> list Ty  -> m_call_ext -> m_call_ext -> Prop.
  Variable mbody_new_map : TyP_List -> list Ty -> ty_ext -> ty_ext -> Prop.

  Inductive E_Ty_Trans (E_Ty_Trans' : TyP_List -> list Ty -> E -> E -> Prop) :
    TyP_List -> list Ty -> E -> E -> Prop :=
  | GJ_E_Ty_Trans_e_var : forall XNs Us v, 
    E_Ty_Trans E_Ty_Trans' XNs Us (FJ_E_Wrap (e_var _ _ _ _ _ _ _ v)) (FJ_E_Wrap (e_var _ _ _ _ _ _ _ v))
  | GJ_E_Ty_Trans_fd_access : forall XNs Us e e' f, 
    E_Ty_Trans' XNs Us e e' ->
    E_Ty_Trans E_Ty_Trans' XNs Us 
    (FJ_E_Wrap (fd_access _ _ _ _ _ _ _ e f)) (FJ_E_Wrap (fd_access _ _ _ _ _ _ _ e' f))
  | GJ_E_Ty_Trans_m_call : forall XNs Us e e' m es es' mce' mce'', 
    E_Ty_Trans' XNs Us e e' ->
    List_P2' (E_Ty_Trans' XNs Us) es es' ->
    mbody_m_call_map XNs Us mce' mce'' -> 
    E_Ty_Trans E_Ty_Trans' XNs Us 
    (FJ_E_Wrap (m_call _ _ _ _ _ _ _ mce' e m es)) (FJ_E_Wrap (m_call _ _ _ _ _ _ _ mce'' e' m es'))
  | GJ_E_Ty_Trans_new : forall XNs Us te' te'' cl es es', 
    List_P2' (E_Ty_Trans' XNs Us) es es' ->
    mbody_new_map XNs Us te' te'' -> 
    E_Ty_Trans E_Ty_Trans' XNs Us 
    (FJ_E_Wrap (new _ _ _ _ _ _ _ (ty_def _ _ te' cl) es)) (FJ_E_Wrap (new _ _ _ _ _ _ _ (ty_def _ _ te'' cl) es')).

  Inductive GJ_mbody_m_call_map XNs Us :
    @MCall_ext m_call_ext' -> @MCall_ext m_call_ext' -> Prop :=
  | GJ_mbody_map_m_call_ext : forall mce tys,
    GJ_mbody_m_call_map XNs Us (tys, mce) (Tys_Trans XNs Us tys, mce).
    
  Inductive GJ_mbody_new_map XNs Us : @GTy_ext ty_def_ext -> @GTy_ext ty_def_ext -> Prop :=
  | GJ_mbody_map_new_ext : forall te tys,
    GJ_mbody_new_map XNs Us (tys, te) (Tys_Trans XNs Us tys, te).

  Inductive map_mbody cld_def_ext md_ext (E_Ty_Trans' : TyP_List -> list Ty -> E -> E -> Prop) : 
    @cld_ext cld_def_ext -> @GTy_ext ty_def_ext -> @MCall_ext m_call_ext' -> @MD_ext md_ext -> E -> E -> Prop :=
  | GJ_map_mbody : forall XNs ce Us te YOs mce Vs mde e e',
    E_Ty_Trans' (XNs ++ YOs) (Us ++ Vs) e e' ->
    map_mbody cld_def_ext md_ext E_Ty_Trans' (XNs, ce) (Us, te) (Vs, mde) (YOs, mce) e e'.

End map_mbody_Section.

Section WF_Expressions.

  Variables (**** The missing pieces for E_WF ****)
    (m_call_ext : Set)
    (mty_def_ext' : Set)
    (ty_ext' : Set)
    (WF_fields_map : Context -> Ty -> Ty -> Prop) 
    (WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_def_ext' -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_def_ext' -> Ty -> Ty -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_def_ext' -> Prop).

  Inductive GJ_Bound : Context -> Ty -> N -> Prop :=
    GJ_bound : forall gamma x ty, TLookup gamma x ty -> GJ_Bound gamma (TyVar x) ty.
  
  Inductive N_Bound : Context -> Ty -> Ty -> Prop := 
    N_bound : forall gamma (n : N), N_Bound gamma n n.
  
  Variable (bound : Context -> Ty -> N -> Prop).
  
  Definition GJ_WF_fields_map := bound.
  
  Definition GJ_WF_mtype_ty_0_map := bound.
  
  Inductive GJ_WF_mtype_Us_map : Context -> @MCall_ext m_call_ext -> @mty_ext mty_def_ext' -> list Ty -> list Ty -> Prop :=
    GJ_Us_map : forall gamma mce mtye tys tys' Vs YOs, 
      WF_mtype_Us_map gamma mce mtye tys tys' -> (*** Map using old extensions ***)
      GJ_WF_mtype_Us_map gamma (Vs, mce) (YOs, mtye) tys (Tys_Trans YOs Vs tys'). 
  
  Inductive GJ_WF_mtype_U_map : Context -> @MCall_ext m_call_ext -> @mty_ext mty_def_ext' -> Ty -> Ty -> Prop :=
    GJ_U_map : forall gamma mce mtye ty ty' Vs YOs, 
      WF_mtype_U_map gamma mce mtye ty ty' -> (*** Map using old extensions ***)
      GJ_WF_mtype_U_map gamma (Vs, mce) (YOs, mtye) ty (Ty_trans ty' (Extract_TyVar YOs) Vs).
  
  Definition GJ_WF_mtype_ext (gamma : Context) (mce : @MCall_ext m_call_ext) (mtye : @mty_ext mty_def_ext') :  Prop :=
    match mce, mtye with 
      (Vs, mce'), (YOs, mtye') => WF_mtype_ext gamma mce' mtye' /\ (*** Extension for Previous Definitions ***)
      List_P1 (WF_Type gamma) Vs /\ (*** Each of the Type Parameters needs to be well-formed ***)
      List_P2 Vs (Tys_Trans YOs Vs (map (fun yo => N_Wrap (snd yo)) YOs)) (subtype gamma) 
    end.

End WF_Expressions.

Inductive GJ_ce_build_cte {cld_def_ext ty_ext : Set}
  (ce_build_cte' : cld_def_ext -> ty_ext -> Prop) : @cld_ext cld_def_ext -> @GTy_ext ty_ext -> Prop :=
  build_cte : forall (ce : cld_def_ext) (te : ty_ext) typs, ce_build_cte' ce te -> 
    GJ_ce_build_cte ce_build_cte' (typs, ce) (map (fun x => Ty_Wrap (TyVar x)) (Extract_TyVar typs), te).

Variable TUpdate : Context -> TX -> N -> Context.

Fixpoint update_Tlist (gamma : Context) (lkp_list : TyP_List) : Context :=
  match lkp_list with
    nil => gamma
    | (TyVar tx, ty) :: lkp_list' => TUpdate (update_Tlist gamma lkp_list') tx ty
  end.

Definition GJ_TUpdate {Context : Set} (gamma : @GJ_Context Context) (tx : TX) (ty : Ty) : @GJ_Context Context := 
  match gamma with 
    (delta, gamma') => ((tx, ty) :: delta, gamma')
  end.

Inductive GJ_build_context {cld_def_ext md_def_ext : Set} 
  (build_context' : cld_def_ext -> md_def_ext -> Context -> Context -> Prop) :
  @cld_ext cld_def_ext -> @MD_ext md_def_ext -> Context -> Context -> Prop :=
  build_context : forall ce mde gamma gamma' XNs YOs, build_context' ce mde gamma gamma' ->
    GJ_build_context build_context' (XNs, ce) (YOs, mde) gamma (update_Tlist gamma' (XNs ++ YOs)).

Definition GJ_Meth_WF_Ext {cld_def_ext md_def_ext : Set} (Meth_WF_Ext' : Context -> cld_def_ext -> md_def_ext -> Prop)
  (gamma : Context)  (ce : @cld_ext cld_def_ext) (mde : @MD_ext md_def_ext) : Prop :=
  match ce, mde with 
    (XNs, ce'), (YOs, mde') => List_P1 (fun yo : (GTy * N) => WF_Type gamma (snd yo)) YOs /\ 
    distinct (Extract_TyVar XNs ++ Extract_TyVar YOs) /\
    Meth_WF_Ext' gamma ce' mde'
  end.

Definition Extract_TyVar' (typs : TyP_List) : list Ty := 
  map (fun x => (Ty_Wrap (@fst GTy N x))) typs.

Definition Ty_replace (Xs Ys : list TX) (tys : list Ty) :=
  map (fun ty => Ty_trans ty Xs (map (fun Y => Ty_Wrap (TyVar Y)) Ys)) tys.
    
Inductive L_WF_Ext {cld_def_ext : Set} (L_WF_Ext' : Context -> cld_def_ext -> C -> Prop ) :
  Context -> @cld_ext cld_def_ext -> C -> Prop :=
  GJ_L_WF_Ext : forall gamma ce typs c 
    (distinct_Xs : distinct (map (@fst _ _) typs)), L_WF_Ext' gamma ce c ->
    List_P1 (fun typ => WF_Type gamma (N_Wrap (snd typ))) typs -> (*** All the bounds well-formed? ***)
    L_WF_Ext L_WF_Ext' gamma (typs, ce) c.

Inductive L_build_context {cld_def_ext : Set} 
  (L_build_context' : cld_def_ext -> Context -> Prop) : 
  @cld_ext cld_def_ext -> Context -> Prop :=
  GJ_L_build_context : forall ce gamma XNs, 
    L_build_context' ce gamma ->
    L_build_context L_build_context' (XNs, ce) (update_Tlist gamma XNs).


Section Preservation.

  Lemma length_Typs_Trans : forall YOs XNs Ts, length (Typs_Trans XNs Ts YOs) = length YOs.
    induction YOs; simpl; auto.
  Qed.

  Lemma length_Tys_Trans : forall XNs Ts Vs, length (Tys_Trans XNs Ts Vs) = length Vs.
    induction Vs; simpl; auto.
  Qed.

  Variable (app_context : Context -> Context -> Context)
    (TLookup_app : forall gamma delta X ty, TLookup gamma X ty -> TLookup (app_context gamma delta) X ty).
  
  Definition Weaken_Subtype_app_P := cFJ.Weaken_Subtype_app_P Ty Context subtype app_context.

  Coercion subtype_Wrap : GJ_subtype >-> subtype.

  Lemma GJ_Weaken_Subtype_app : forall gamma S T (sub_S_T : GJ_subtype gamma S T),
    Weaken_Subtype_app_P _ _ _ sub_S_T.
    cbv beta delta; intros; apply subtype_Wrap; inversion sub_S_T; subst.
    econstructor; eapply TLookup_app; eauto.
    Qed.

  Lemma fields_build_te_id : forall {ty_ext cld_def_ext : Set} 
    (fields_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (H1 : forall ce te te' te'' te''', fields_build_te' ce te te' te'' -> 
      fields_build_te' ce te te' te''' -> te'' = te''')
    (ce : @cld_ext cld_def_ext) (te te' te'' te''' : @GTy_ext ty_ext),
    fields_build_te fields_build_te' ce te te' te'' ->
    fields_build_te fields_build_te' ce te te' te''' -> 
    te'' = te'''.
    intros; inversion H; inversion H0; subst.
    injection H12; injection H11; injection H10; intros; subst.
    rewrite (H1 _ _ _ _ _ H8 H2); reflexivity.
  Qed.

  Lemma fields_build_tys_id : forall {ty_ext cld_def_ext : Set}
    (fields_build_tys' : ty_ext -> cld_def_ext -> list Ty -> list Ty -> Prop)
    (H1 : forall te ce tys tys' tys'',
      fields_build_tys' te ce tys tys' -> fields_build_tys' te ce tys tys'' -> tys' = tys'')
    (te : @GTy_ext ty_ext) (ce : @cld_ext cld_def_ext) (tys tys' tys'' : list Ty),
    fields_build_tys fields_build_tys' te ce tys tys' ->
    fields_build_tys fields_build_tys' te ce tys tys'' -> 
    tys' = tys''.
    intros; inversion H; inversion H0; subst.
    injection H9; injection H8; intros; subst.
    rewrite (H1 _ _ _ _ _ H7 H2); reflexivity.
  Qed.

  Lemma Fields_Build_tys_len : forall {ty_ext cld_def_ext : Set}
    (fields_build_tys' : ty_ext -> cld_def_ext -> list Ty -> list Ty -> Prop)
    (H1 : forall te ce tys tys', fields_build_tys' te ce tys tys' -> length tys = length tys')
    (te : @GTy_ext ty_ext) (ce : @cld_ext cld_def_ext) (tys tys' : list Ty),
    fields_build_tys fields_build_tys' te ce tys tys' -> length tys = length tys'.
    intros; inversion H; subst.
    rewrite (H1 _ _ _ _ H0); clear; rename tys'0 into tys; induction tys; simpl; congruence.
  Qed.

  Variables (Update : Context -> Var X -> Ty -> Context)
    (TLookup_Update : forall gamma Y X ty ty',  
      TLookup (Update gamma Y ty') X ty -> TLookup gamma X ty) 
    (TLookup_Update' : forall gamma Y X ty ty',  
      TLookup gamma X ty -> TLookup (Update gamma Y ty') X ty)
    (TLookup_Empty : forall X ty, ~ TLookup Empty X ty).

  Definition update_list := cFJ.update_list X Ty Context Update.

  Lemma TLookup_Update_list : forall gamma X T vars, TLookup (update_list gamma vars) X T -> TLookup gamma X T.
    induction vars; simpl; intros; auto; destruct a; apply IHvars; eauto.
  Qed.
    
  Lemma TLookup_Update_list' : forall gamma X T vars, TLookup gamma X T -> TLookup (update_list gamma vars) X T.
    induction vars; simpl; intros; auto; destruct a; eauto.
  Qed.

  Definition GJ_Weaken_Subtype_update_list : forall gamma S T (sub_S_T : GJ_subtype gamma S T),
    Weaken_Subtype_update_list_P X _ _ subtype Empty Update _ _ _ sub_S_T.
    unfold Weaken_Subtype_update_list_P; unfold cFJ.Weaken_Subtype_update_list_P.
    intros; subst.
    inversion sub_S_T; subst; apply TLookup_Update_list in H.
    elimtype False; eapply TLookup_Empty; eauto.
  Qed.

  Lemma Weaken_WF_Object_Ext (ty_ext' : Set): 
    forall (gamma : Context) (vars : list (Var X * Ty)) (te : @GTy_ext ty_ext'),
      GJ_wf_object_ext (cFJ.update_list X Ty Context Update Empty vars) te ->
      GJ_wf_object_ext (cFJ.update_list X Ty Context Update gamma vars) te.
    intros; inversion H; subst; constructor.
  Qed.

  Variables (E md_def_ext cld_def_ext ty_def_ext : Set).

  Section wf_class_ext_recursion.
        
    Variables 
      (P : forall gamma ty, WF_Type gamma ty -> Prop)
      (Q' : forall gamma ce ty, 
        @GJ_wf_class_ext cld_def_ext ty_def_ext gamma ce ty -> Prop)
      (Q'_P1 : forall gamma tys, List_P1 (WF_Type gamma) tys -> Prop)
      (Q'_len : forall (typs : TyP_List) (tys : list Ty), length typs = length tys -> Prop)
      (Q'_P2 : forall tys tys' delta, List_P2 tys tys' (subtype delta) -> Prop).
    
    Hypothesis (H1 : forall gamma ce tys typs te P1 len P2, Q'_P1 gamma tys P1 -> 
      Q' _ _ _ (@GJ_definitions.wf_class_ext cld_def_ext ty_def_ext ce gamma typs tys te P1 len P2))
    (H2 : forall gamma, Q'_P1 gamma _ (Nil (WF_Type gamma)))
    (H3 : forall gamma ty tys P_ty P_tys, P _ _ P_ty -> Q'_P1 _ tys P_tys -> 
      Q'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys)).
    
    Definition wf_class_ext_rect (WF_type_rect : forall gamma ty wf_ty, P gamma ty wf_ty) 
      gamma cld te (wf_te : GJ_wf_class_ext gamma cld te) : Q' _ _ _ wf_te :=
      match wf_te return  Q' _ _ _ wf_te with
        GJ_definitions.wf_class_ext ce gamma typs tys te P1 len P2 => 
        H1 gamma ce tys typs te P1 len P2 
        ((fix map (As : list Ty) (PAs : List_P1 (WF_Type gamma) As) : Q'_P1 _ _ PAs :=
          match PAs return Q'_P1 _ _ PAs with
            Nil => H2 gamma
            | Cons_a a As' Pa PAs' => H3 gamma a As' Pa PAs'
              (WF_type_rect _ a Pa) (map As' PAs')
          end) tys P1)
      end.
  
  End wf_class_ext_recursion.

  Definition Weaken_WF_Type_update_list_P := fun gamma ty (WF_ty : WF_Type gamma ty) => 
       forall vars gamma' (gamma'_eq : gamma = (update_list Empty vars)),
         WF_Type (update_list gamma' vars) ty.

  Definition Weaken_WF_Type_update_list_Q' := 
    Weaken_WF_Class_Ext_Q _ (@GTy_ext ty_def_ext) _ (@cld_ext cld_def_ext) _ GJ_wf_class_ext Empty Update.

  Definition Weaken_WF_Type_update_list_Q'_P1 := fun gamma tys (P1 : List_P1 (WF_Type gamma) tys)=> 
    forall vars gamma' (gamma'_eq : gamma = (update_list Empty vars)),
      List_P1 (WF_Type (update_list gamma' vars)) tys.

  Variable (Weaken_Subtype_update_list : forall gamma S T sub_S_T, 
    Weaken_Subtype_update_list_P X _ _ subtype Empty Update gamma S T sub_S_T).

  Lemma Weaken_WF_Type_update_list_H1 : forall gamma ce tys typs te P1 len P2, 
    Weaken_WF_Type_update_list_Q'_P1 gamma tys P1 -> 
    Weaken_WF_Type_update_list_Q' _ _ _ (@GJ_definitions.wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold Weaken_WF_Type_update_list_Q'; unfold Weaken_WF_Class_Ext_Q; intros.
    constructor; auto.
    destruct P2; split; intros; auto.
    destruct (H1 _ _ H3) as [b [fnd_b sub_a_b]].
    exists b; split; auto.
    eapply Weaken_Subtype_update_list; eauto.
  Qed.

  Lemma Weaken_WF_Type_update_list_H2 : forall gamma, 
    Weaken_WF_Type_update_list_Q'_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Weaken_WF_Type_update_list_Q'_P1; intros; constructor.
  Qed.
    
  Lemma Weaken_WF_Type_update_list_H3 : forall gamma ty tys P_ty P_tys, 
    Weaken_WF_Type_update_list_P _ _ P_ty -> Weaken_WF_Type_update_list_Q'_P1 _ tys P_tys -> 
    Weaken_WF_Type_update_list_Q'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Weaken_WF_Type_update_list_Q'_P1; intros; constructor; auto.
  Qed.

  Definition Weaken_WF_Type_update_list_ext := 
    wf_class_ext_rect _ _ _ Weaken_WF_Type_update_list_H1 Weaken_WF_Type_update_list_H2 Weaken_WF_Type_update_list_H3.

  Lemma GJ_Weaken_WF_Type_update_list : 
    forall gamma ty wf_ty, Weaken_WF_Type_update_list_P gamma ty (GJ_WF_Type_Wrap gamma ty wf_ty).
    unfold Weaken_WF_Type_update_list_P; intros; destruct wf_ty; subst.
    elimtype False; eapply (TLookup_Empty tx ty); generalize H TLookup_Update TLookup_Update';
      clear; induction vars; simpl; intros; eauto.
    destruct a; eapply IHvars; auto.
    eapply TLookup_Update; apply H.
  Qed.

  Variable (Bound : Context -> Ty -> N -> Prop)
    (GJ_Bound_Wrap : forall gamma ty ty', GJ_Bound gamma ty ty' -> Bound gamma ty ty')
    (GJ_Bound_invert : forall gamma x ty, Bound gamma (TyVar x) ty -> GJ_Bound gamma (TyVar x) ty)
    (Bound' : Context -> Ty -> Ty -> Prop)
    (GJ_Bound'_Wrap : forall gamma ty ty', GJ_Bound gamma ty ty' -> Bound' gamma ty ty')
    (N_Bound'_Wrap : forall gamma ty ty', N_Bound gamma ty ty' -> Bound' gamma ty ty').
  
Definition override {ty_ext m_call_ext md_def_ext mty_def_ext' : Set}
  (build_te : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
  (WF_mtype_Us_map : Context -> m_call_ext -> mty_def_ext' -> list Ty -> list Ty -> Prop)
  (WF_mtype_U_map : Context -> m_call_ext -> mty_def_ext' -> Ty -> Ty -> Prop)
  (WF_mtype_ext : Context -> m_call_ext -> mty_def_ext' -> Prop)
  (mtype_build_mtye' : cld_def_ext -> ty_ext -> Ty -> list VD -> md_def_ext -> mty_def_ext' -> Prop)
  L_build_context' mtype_build_tys'
  (build_context' : cld_def_ext -> md_def_ext -> Context -> Context -> Prop)
  (Meth_WF_Ext' : Context -> cld_def_ext -> md_def_ext -> Prop)
  (FJ_Ty_Wrap : cFJ.FJ_Ty C (@GTy_ext ty_ext) -> Ty)
  (mtype : Context -> M -> Ty -> cFJ.Mty Ty (@mty_ext mty_def_ext') -> Prop)
  (gamma1 : Context) (m : M) (ty : cFJ.FJ_Ty C (@GTy_ext ty_ext))
  (mde' : @MD_ext md_def_ext) (Ws : list Ty) (W : Ty) : Prop :=
  forall gamma gamma' (ce ce' : @cld_ext cld_def_ext)
    te te' te'' d T' mtye U U' Us Us' mce vars mtye' W' Ws'  vds,
    ty = (ty_def _ _  te'' d) -> 
    Bound' gamma (FJ_Ty_Wrap (ty_def _ _  te' d)) T' ->
    mtype Empty m T' (mty _ _ mtye Us U) ->
    GJ_WF_mtype_U_map _ _ WF_mtype_U_map gamma mce mtye U U' ->
    GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map gamma mce mtye Us Us' ->
    GJ_WF_mtype_ext _ _ WF_mtype_ext gamma mce mtye ->  
    GJ_build_te build_te ce te te'' te' ->
    L_build_context L_build_context' ce gamma' ->
    (GJ_wf_class_ext gamma' ce'  te'' \/ GJ_wf_object_ext gamma' te'') -> 
    GJ_build_context build_context' ce mde' (update_list Empty vars) gamma1 -> 
    WF_Type gamma1 W ->
    List_P1 (WF_Type gamma1) Ws -> 
    GJ_Meth_WF_Ext Meth_WF_Ext' gamma1 ce mde' ->
    mtype_build_mtye mtype_build_mtye' ce te W vds mde' mtye' ->
    mtype_build_tys mtype_build_tys' ce te W vds mde' Ws Ws' ->
    mtype_build_tys mtype_build_tys' ce te W vds mde' (W :: nil) (W' :: nil) ->
    exists V', GJ_WF_mtype_U_map _ _ WF_mtype_U_map gamma mce mtye' W' V' /\
      GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map gamma mce mtye' Ws' Us' /\
      subtype gamma V' U' /\ GJ_WF_mtype_ext _ _ WF_mtype_ext gamma mce mtye'.

  Lemma GJ_Weaken_WF_fields_map : forall (gamma : Context) ty ty', GJ_Bound gamma ty ty' ->
    forall gamma' vars, gamma = update_list Empty vars -> Bound' (update_list gamma' vars) ty ty'.
    intros; destruct H; subst.
    apply GJ_Bound'_Wrap.
    constructor.
    elimtype False; eapply (TLookup_Empty x ty); generalize H TLookup_Update TLookup_Update';
      clear; induction vars; simpl; intros; eauto.
    destruct a; eapply IHvars; auto.
    eapply TLookup_Update; apply H.
  Qed.

  Lemma FJ_Weaken_WF_fields_map : forall (gamma : Context) ty ty', N_Bound gamma ty ty' ->
    forall gamma' vars, gamma = update_list Empty vars -> Bound' (update_list gamma' vars) ty ty'.
    intros; destruct H; subst.
    apply N_Bound'_Wrap; constructor.
  Qed.
  
  Lemma Weaken_WF_mtype_Us_map (m_call_ext mty_def_ext' : Set) 
    (WF_mtype_Us_map' :  Context -> m_call_ext -> mty_def_ext' -> list Ty -> list Ty -> Prop) 
    (H1 : forall mce mtye tys tys' vars gamma, WF_mtype_Us_map' (update_list Empty vars) mce mtye tys tys' ->
      WF_mtype_Us_map' (update_list gamma vars) mce mtye tys tys') : 
    forall (gamma : Context) (vars : list (Var X * Ty)) 
      (mce : @MCall_ext m_call_ext) (Us Us' : list Ty) (mtye : mty_ext),
      GJ_WF_mtype_Us_map m_call_ext mty_def_ext' WF_mtype_Us_map' (update_list Empty vars) mce mtye Us Us' ->
      GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map' (update_list gamma vars) mce mtye Us Us'.
    intros.
    assert (exists gamma', gamma' = update_list Empty vars) as H0 by (eexists; reflexivity);
      destruct H0 as [gamma' H0]; rewrite <- H0 in H; destruct H.
    constructor; eauto.
    eapply H1; rewrite H0 in H; assumption.
  Qed.

  Lemma Weaken_WF_mtype_U_map (m_call_ext mty_def_ext' : Set) 
    (WF_mtype_U_map : Context -> m_call_ext -> mty_def_ext' -> Ty -> Ty -> Prop)
    (H1 : forall gamma vars mce U U' mtye, WF_mtype_U_map (update_list Empty vars) mce mtye U U' -> 
      WF_mtype_U_map (update_list gamma vars) mce mtye U U') : 
    forall (gamma : Context) (vars : list (Var X * Ty)) 
    (mce : @MCall_ext m_call_ext) (U U' : Ty) (mtye : mty_ext),
    GJ_WF_mtype_U_map m_call_ext mty_def_ext' WF_mtype_U_map (update_list Empty vars) mce mtye U U' ->
    GJ_WF_mtype_U_map m_call_ext mty_def_ext' WF_mtype_U_map (update_list gamma vars) mce mtye U U'.
    intros.
    assert (exists gamma', gamma' = update_list Empty vars) as H0 by (eexists; reflexivity);
      destruct H0 as [gamma' H0]; rewrite <- H0 in H; destruct H.
    repeat constructor; rewrite H0 in H; auto.
  Qed.
  
  Variable (Weaken_WF_Type_update_list : forall (gamma : Context) (ty : Ty) (WF_ty : WF_Type gamma ty),
    FJ_Weaken_WF_Type_update_list_P X Ty Context WF_Type Empty Update gamma
    ty WF_ty).

  Lemma Weaken_WF_Type_List_P1 gamma' tys (P1 : List_P1 (WF_Type gamma') tys) :
    forall gamma vars, gamma' = update_list Empty vars -> 
      List_P1 (WF_Type (update_list gamma vars)) tys.
    intros until vars; induction P1; constructor.
    rewrite H0 in H; eauto.
    eapply Weaken_WF_Type_update_list; eauto.
    eauto.
  Qed.
    
  Lemma Weaken_WF_mtype_ext (m_call_ext mty_def_ext' : Set)
    (WF_mtype_ext' : Context -> m_call_ext -> mty_def_ext' -> Prop) 
    (H1 : forall gamma vars mce mtye, WF_mtype_ext' (update_list Empty vars) mce mtye ->
      WF_mtype_ext' (update_list gamma vars) mce mtye) : 
    forall (gamma : Context) (vars : list (Var X * Ty)) 
      (mce : @MCall_ext m_call_ext) (mtye : mty_ext),
      GJ_WF_mtype_ext m_call_ext mty_def_ext' WF_mtype_ext' (update_list Empty vars) mce mtye ->
      GJ_WF_mtype_ext m_call_ext mty_def_ext' WF_mtype_ext' (update_list gamma vars) mce mtye.
    unfold GJ_WF_mtype_ext; intros; destruct mce; destruct mtye.
    destruct H as [H [H0 H2]]; repeat split.
    eauto.
    eapply Weaken_WF_Type_List_P1; eauto.
    destruct H2; intros; destruct (H2 _ _ H4) as [b [fnd_b sub_a_b]].
    exists b; split; auto.
    eapply Weaken_Subtype_update_list; eauto.
    destruct H2; auto.
  Qed.

  Definition FJ_Ty_Wrap : cFJ.FJ_Ty C ty_ext -> Ty := fun ty => N_Wrap (FJ_N_Ty_Wrap ty).

  Variable (FJ_Ty_Wrap_inject : forall ty ty', FJ_Ty_Wrap ty = FJ_Ty_Wrap ty' -> ty = ty')
    (Ty_Wrap_discriminate : forall ty ty', FJ_Ty_Wrap ty <> Ty_Wrap ty').
  
  Lemma GJ_WF_fields_map_id' : forall gamma ty ty', GJ_Bound gamma ty ty' ->
    forall tye c, ty = (FJ_Ty_Wrap (ty_def _ _ tye c)) -> 
      exists tye', N_Wrap ty' = FJ_Ty_Wrap (ty_def _ _ tye' c).
    intros; subst; inversion H; apply sym_eq in H0; apply Ty_Wrap_discriminate in H0; contradiction.
  Qed.

  Lemma N_WF_fields_map_id' : forall gamma ty ty', N_Bound gamma ty ty' ->
    forall tye c, ty = (FJ_Ty_Wrap (ty_def _ _ tye c)) -> 
      exists tye', ty' = FJ_Ty_Wrap (ty_def _ _ tye' c).
    intros; subst; inversion H; apply sym_eq in H0; exists tye; apply H2.
  Qed.

  Lemma TLookup_Update_id : forall gamma vars x T, 
    TLookup (update_list gamma vars) x T -> TLookup gamma x T.
    induction vars; simpl; intros; auto.
    destruct a; eauto.
  Qed.

  Lemma GJ_Subtype_Update_list_id gamma S T (sub_S_T : GJ_subtype gamma S T) :
    forall delta vars, gamma = (update_list delta vars) -> subtype delta S T.
    intros; inversion sub_S_T; subst.
    apply subtype_Wrap; constructor.
    eapply TLookup_Update_id; eauto.
  Qed.

  Lemma GJ_Bound_Weaken_update_list : forall delta T T', GJ_Bound delta T T' -> 
    forall delta' Vars, delta = update_list delta' Vars -> Bound' delta' T T'.
    intros; inversion H; subst; eapply GJ_Bound'_Wrap; constructor.
    eapply TLookup_Update_id; eassumption.
  Qed.

  Lemma N_Bound_Weaken_update_list : forall delta T T', N_Bound delta T T' -> 
    forall delta' Vars, delta = update_list delta' Vars -> Bound' delta' T T'.
    intros; inversion H; subst; eapply N_Bound'_Wrap; constructor.
  Qed.

  Lemma GJ_WF_mtype_U_map_Weaken_update_list (m_call_ext mty_def_ext' : Set) 
    (WF_mtype_U_map : Context -> m_call_ext -> mty_def_ext' -> Ty -> Ty -> Prop)
    (H1 : forall gamma vars mce U U' mtye, 
      WF_mtype_U_map (update_list gamma vars) mce mtye U U' -> 
      WF_mtype_U_map gamma mce mtye U U') : 
    forall (gamma : Context) (vars : list (Var X * Ty)) 
      (mce : @MCall_ext m_call_ext) (U U' : Ty) (mtye : mty_ext),
      GJ_WF_mtype_U_map _ _ WF_mtype_U_map (update_list gamma vars) mce mtye U U' -> 
      GJ_WF_mtype_U_map _ _ WF_mtype_U_map gamma mce mtye U U'.
    intros; inversion H; subst; constructor.
    eauto.
  Qed.
  
  Lemma GJ_WF_mtype_Us_map_Weaken_update_list (m_call_ext mty_def_ext' : Set) 
    (WF_mtype_Us_map' :  Context -> m_call_ext -> mty_def_ext' -> list Ty -> list Ty -> Prop) 
    (H1 : forall mce mtye tys tys' vars gamma, 
      WF_mtype_Us_map' (update_list gamma vars) mce mtye tys tys' ->
      WF_mtype_Us_map' gamma mce mtye tys tys') : 
    forall (gamma : Context) (vars : list (Var X * Ty)) 
      (mce : @MCall_ext m_call_ext) (Us Us' : list Ty) (mtye : mty_ext),
      GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map' 
      (update_list gamma vars) mce mtye Us Us' ->
      GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map' gamma mce mtye Us Us'.
    intros.
    assert (exists gamma', gamma' = update_list gamma vars) as H0 by (eexists; reflexivity);
      destruct H0 as [gamma' H0]; rewrite <- H0 in H; destruct H.
    constructor; eauto.
    eapply H1; rewrite H0 in H; eassumption.
  Qed.
  
  Definition Bound_total_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall T', Bound' gamma T T' -> exists S' , Bound' gamma S S'.
  
  Lemma GJ_Bound_total : forall gamma S T (sub_S_T : GJ_subtype gamma S T), Bound_total_P _ _ _ sub_S_T.
    intros; inversion sub_S_T; subst.
    exists ty; apply GJ_Bound'_Wrap; constructor; assumption.
  Qed.

  Lemma GJ_WF_Object_ext_Update_Vars_id (ty_ext' : Set): 
    forall (gamma : Context) (vars : list (Var X * Ty)) (te : @GTy_ext ty_ext'),
      GJ_wf_object_ext (cFJ.update_list X Ty Context Update gamma vars) te ->
      GJ_wf_object_ext gamma te.
    intros; inversion H; subst; constructor.
  Qed.

  Definition WF_Type_update_list_id_P :=
    WF_Type_update_list_id_P X _ _ WF_Type Update.

  Definition WF_Type_update_list_id_Q' := 
    WF_Class_ext_Update_Vars_id_Q  _ (@GTy_ext ty_def_ext) _ (@cld_ext cld_def_ext) 
    _ GJ_wf_class_ext Update.

  Definition WF_Type_update_list_id_Q'_P1 := fun gamma tys (P1 : List_P1 (WF_Type gamma) tys)=> 
    forall vars gamma' (gamma'_eq : gamma = (update_list gamma' vars)),
      List_P1 (WF_Type gamma') tys.

  Variable (Subtype_Update_list_id : forall gamma S T sub_S_T, 
    Subtype_Update_list_id_P X _ _ subtype Update gamma S T sub_S_T).

  Lemma WF_Type_update_list_id_H1 : forall gamma ce tys typs te P1 len P2, 
    WF_Type_update_list_id_Q'_P1 gamma tys P1 -> 
    WF_Type_update_list_id_Q' _ _ _ (@GJ_definitions.wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold WF_Type_update_list_id_Q'; unfold WF_Class_ext_Update_Vars_id_Q; 
      unfold WF_Type_update_list_id_Q'_P1; intros.
    constructor; auto.
    eapply H; eapply H0.
    destruct P2; split; intros; auto.
    destruct (H1 _ _ H3) as [b [fnd_b sub_a_b]].
    exists b; split; auto.
    rewrite H0 in sub_a_b; eapply Subtype_Update_list_id.
    apply sub_a_b.
    reflexivity.
  Qed.

  Lemma WF_Type_update_list_id_H2 : forall gamma, 
    WF_Type_update_list_id_Q'_P1 gamma _ (Nil (WF_Type gamma)).
    unfold WF_Type_update_list_id_Q'_P1; intros; constructor.
  Qed.
    
  Lemma WF_Type_update_list_id_H3 : forall gamma ty tys P_ty P_tys, 
    WF_Type_update_list_id_P _ _ P_ty -> WF_Type_update_list_id_Q'_P1 _ tys P_tys -> 
    WF_Type_update_list_id_Q'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold WF_Type_update_list_id_Q'_P1; intros; constructor; auto.
    cbv in H.
    eapply H.
    rewrite gamma'_eq; reflexivity.
    eapply H0; eauto.
  Qed.

  Definition WF_Type_update_list_id_ext := 
    wf_class_ext_rect _ _ _ WF_Type_update_list_id_H1 WF_Type_update_list_id_H2 WF_Type_update_list_id_H3.

  Lemma GJ_WF_Type_update_list_id : forall gamma' ty' (wf_ty' : GJ_WF_Type gamma' ty'), 
    WF_Type_update_list_id_P _ _ (GJ_WF_Type_Wrap _ _ wf_ty').
    unfold WF_Type_update_list_id_P; unfold cFJ.WF_Type_update_list_id_P; intros.
    inversion wf_ty'; subst.
    eapply GJ_WF_Type_Wrap; econstructor; eapply TLookup_Update_id; eauto.
  Qed.
  
  Lemma GJ_fields_build_tys_tot : forall {cld_def_ext ty_def_ext : Set}
    (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
    (fields_build_tys' : ty_def_ext -> cld_def_ext -> list Ty -> list Ty -> Prop)
    (H1 : forall te ce tys te' te'',  build_te' ce te te' te'' -> 
      exists tys' , fields_build_tys' te ce tys tys') te ce tys te' te'',
    GJ_build_te build_te' ce te te' te'' ->
    exists tys', fields_build_tys fields_build_tys' te ce tys tys'.
    intros; inversion H; subst.
    destruct (H1 _ _ tys _ _ H0) as [tys'' build_tys'']; eexists; constructor; eauto.
  Qed.

  Variables (md_ext cld_ext : Set)
  (CT : C -> option (L C F M X ty_ext Ty E md_ext cld_ext))
  (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop).
  
  Definition FJ_subtype := cFJ.FJ_subtype C F M X ty_ext Ty FJ_Ty_Wrap
    E md_ext cld_ext CT Context subtype build_te.

  Variable 
    (FJ_subtype_Wrap : forall {gamma : Context} {ty ty' : Ty}, FJ_subtype gamma ty ty' -> subtype gamma ty ty').

  Lemma FJ_Bound_total (Bound_total_rect : forall gamma S T sub_S_T, Bound_total_P gamma S T sub_S_T)
    gamma S T (sub_S_T : FJ_subtype gamma S T) :
    Bound_total_P gamma S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect with (P := Bound_total_P);
      unfold Bound_total_P; intros.
    eexists; eassumption.
    destruct (H0 _ H1) as [S' Bound_d]; destruct (H _ Bound_d); eexists; eassumption.
    eexists; apply N_Bound'_Wrap; constructor.
    eapply Bound_total_rect; eauto.
  Defined.
  
  Definition Weakening_2_1_1_P delta S T (sub_S_T : subtype delta S T) :=
    forall gamma, subtype (app_context delta gamma) S T.
  
  Lemma Weakening_2_1_1_FJ (Weakening_rect : forall delta S T sub_S_T, Weakening_2_1_1_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Weakening_2_1_1_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Weakening_2_1_1_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    intros; apply Weakening_rect; auto.
  Defined.
    
  Lemma Weakening_2_1_1_GJ : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Weakening_2_1_1_P _ _ _ sub_S_T.
    unfold Weakening_2_1_1_P; intros; apply subtype_Wrap;
      inversion sub_S_T; subst; constructor; auto.
  Qed.
    
  Variable (Weakening_2_1_1 : forall delta S T sub_S_T, Weakening_2_1_1_P delta S T sub_S_T).

  Definition Weakening_2_1_2_P delta S (WF_S : WF_Type delta S) :=
    forall gamma, WF_Type (app_context delta gamma) S.

  Definition Weakening_2_1_2_Q delta cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext delta cld te) :=
    forall gamma, GJ_wf_class_ext (app_context delta gamma) cld te.
  
  Definition Weakening_2_1_2_P1 delta Ss (WF_Ss : List_P1 (WF_Type delta) Ss) :=
    forall gamma, List_P1 (WF_Type (app_context delta gamma)) Ss.

  Lemma Weakening_2_1_2_ext_H1 : forall gamma ce tys typs te P1 len P2, 
    Weakening_2_1_2_P1 gamma tys P1 -> 
    Weakening_2_1_2_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold Weakening_2_1_2_P1; unfold Weakening_2_1_2_Q; intros.
    constructor; auto.
    assert (exists tys', tys' = (map (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys) typs)) 
      as tys'_eq by (eexists; reflexivity); destruct tys'_eq as [tys' tys'_eq]; rewrite <- tys'_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in P2; generalize tys' Weakening_2_1_1 P2; clear; induction tys; intros;
      inversion P2; subst; constructor.
    apply Weakening_2_1_1; auto.
    inversion P2; subst; eauto.
  Qed.    

  Lemma Weakening_2_1_2_ext_H2 : forall gamma, 
    Weakening_2_1_2_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Weakening_2_1_2_P1; intros; constructor.
  Qed.
    
  Lemma Weakening_2_1_2_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Weakening_2_1_2_P _ _ P_ty -> Weakening_2_1_2_P1 _ tys P_tys -> 
    Weakening_2_1_2_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Weakening_2_1_2_P; unfold Weakening_2_1_2_P1; intros;
      constructor; eauto.
  Qed.

  Definition Weakening_2_1_2_ext := 
    wf_class_ext_rect Weakening_2_1_2_P Weakening_2_1_2_Q Weakening_2_1_2_P1
    Weakening_2_1_2_ext_H1 Weakening_2_1_2_ext_H2 Weakening_2_1_2_ext_H3.

  Variables (wf_class_ext' : Context -> cld_ext -> ty_ext -> Prop)
    (wf_object_ext' : Context -> ty_ext -> Prop)
    (wf_class_ext'_Q : forall delta cld te (wf_cld : wf_class_ext' delta cld te), 
      forall gamma, wf_class_ext' (app_context delta gamma) cld te)
    (wf_obj_ext'_Q : forall delta te (wf_cld : wf_object_ext' delta te), 
      forall gamma, wf_object_ext' (app_context delta gamma) te).

  Definition FJ_WF_Type  := FJ_WF_Type _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT _ 
    wf_class_ext' wf_object_ext'.
  
  Lemma Weakening_2_1_2_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext),
    GJ_wf_object_ext delta te ->
    forall gamma : Context, GJ_wf_object_ext (app_context delta gamma) te.
    intros; inversion H; subst; constructor.
  Qed.
    
  Variable (FJ_WF_Type_Wrap : forall delta S, FJ_WF_Type delta S -> WF_Type delta S).
  
  Lemma FJ_Weakening_2_1_2_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Weakening_2_1_2_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Weakening_2_1_2_P; intros.
    apply FJ_WF_Type_Wrap; econstructor 1; eauto.
  Qed.
    
  Definition cld_ce (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext) := cld_ce _ _ _ _ _ _ _ _ _ cld.

  Lemma FJ_Weakening_2_1_2_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    (forall delta, wf_class_ext' (app_context gamma delta) (cld_ce cld) te) ->
    Weakening_2_1_2_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Weakening_2_1_2_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
    
  Lemma FJ_Weakening_2_1_2 : forall delta S (WF_S : FJ_WF_Type delta S),
    Weakening_2_1_2_P delta S (FJ_WF_Type_Wrap _ _ WF_S).
    intros; apply FJ_WF_Type_rect' with 
      (Q:= fun delta cld te wf_cld => forall gamma, wf_class_ext' (app_context delta gamma) cld te);
      unfold Weakening_2_1_2_P; intros; eauto; apply FJ_WF_Type_Wrap; econstructor; eauto.
  Defined.
    
  Lemma GJ_Weakening_2_1_2 : forall delta S (WF_S : GJ_WF_Type delta S), 
    Weakening_2_1_2_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Weakening_2_1_2_P; intros; apply GJ_WF_Type_Wrap;
      inversion WF_S; subst; econstructor; eauto.
  Qed.
           
  Variable (Weakening_2_1_2 : forall gamma S WF_S, Weakening_2_1_2_P gamma S WF_S).

  Lemma split_TyP_List : forall (XNs : TyP_List),
    exists X, exists N, zip X N (@pair _ _) = Some XNs.
    clear; induction XNs.
    repeat (exists nil); simpl; reflexivity.
    destruct a as [X' N0']; destruct IHXNs as [X [N0 zip_eq]]; 
      exists (X' :: X); exists (N0' :: N0);
      simpl; rewrite zip_eq; reflexivity.
  Qed.

  Variables (m_call_ext : Set)
    (FJ_E_Wrap : FJ_E C F M X ty_ext E m_call_ext -> E)
    (E_WF : Context -> E -> Ty -> Prop)
    (lookup : Context -> Var X -> Ty -> Prop)
    (WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_def_ext -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_def_ext -> Ty -> Ty -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_def_ext -> Prop)
    (WF_fields_map : Context -> Ty -> Ty -> Prop) 
    (Lookup_dec : forall gamma x ty, lookup gamma x ty \/ ~ lookup gamma x ty)
    (Lookup_app : forall gamma delta x ty, lookup gamma x ty -> lookup (app_context gamma delta) x ty)
    (Lookup_app' : forall gamma delta x ty, (forall ty', ~ lookup gamma x ty') -> lookup delta x ty -> 
      lookup (app_context gamma delta) x ty).
    
  Definition FJ_E_WF := cFJ.FJ_E_WF C F M X _ Ty FJ_Ty_Wrap E m_call_ext FJ_E_Wrap _ _ subtype
    WF_Type fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map
    WF_mtype_U_map WF_mtype_ext Empty.

  Variable FJ_E_WF_Wrap : forall delta e T, FJ_E_WF delta e T -> E_WF delta e T.

  Definition Weakening_2_1_3_1_P delta e T (WF_e : E_WF delta e T):=
    forall gamma, E_WF (app_context delta gamma) e T.

  Definition Weakening_2_1_3_1_Q delta es Ts (WF_es : List_P2' (E_WF delta) es Ts):=
    forall gamma, List_P2' (E_WF (app_context delta gamma)) es Ts.

  Variable (WF_fields_map_app_Weaken : forall gamma gamma' ty ty', WF_fields_map gamma ty ty' ->
    WF_fields_map (app_context gamma gamma') ty ty')
  (WF_mtype_ty_0_Weaken : forall gamma gamma' ty ty', WF_mtype_ty_0_map gamma ty ty' ->
    WF_mtype_ty_0_map (app_context gamma gamma') ty ty')
  (WF_mtype_Us_map_app_Weaken : forall gamma gamma' mce mde tys tys', WF_mtype_Us_map gamma mce mde tys tys' ->
    WF_mtype_Us_map (app_context gamma gamma') mce mde tys tys')
  (WF_mtype_U_map_app_Weaken : forall gamma gamma' mce mde ty ty', WF_mtype_U_map gamma mce mde ty ty' ->
    WF_mtype_U_map (app_context gamma gamma') mce mde ty ty')
  (WF_mtype_ext_app_Weaken : forall gamma gamma' mce mde, WF_mtype_ext gamma mce mde ->
    WF_mtype_ext (app_context gamma gamma') mce mde).

  Lemma GJ_WF_Bound_app_Weaken : forall gamma gamma' ty ty', GJ_Bound gamma ty ty' ->
    GJ_Bound (app_context gamma gamma') ty ty'.
    intros; inversion H; subst; constructor; auto.
  Qed.
    
  Lemma GJ_WF_mtype_Us_map_app_Weaken : forall gamma gamma' mce mde tys tys', 
    GJ_WF_mtype_Us_map m_call_ext mty_def_ext WF_mtype_Us_map gamma mce mde tys tys' ->
    GJ_WF_mtype_Us_map m_call_ext mty_def_ext WF_mtype_Us_map (app_context gamma gamma') mce mde tys tys'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma GJ_WF_mtype_U_map_app_Weaken : forall gamma gamma' mce mde ty ty', 
    GJ_WF_mtype_U_map m_call_ext mty_def_ext WF_mtype_U_map gamma mce mde ty ty' ->
    GJ_WF_mtype_U_map m_call_ext mty_def_ext WF_mtype_U_map (app_context gamma gamma') mce mde ty ty'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma GJ_WF_mtype_ext_app_Weaken : forall gamma gamma' mce mde, 
    GJ_WF_mtype_ext m_call_ext mty_def_ext WF_mtype_ext gamma mce mde ->
    GJ_WF_mtype_ext m_call_ext mty_def_ext WF_mtype_ext (app_context gamma gamma') mce mde.
    unfold GJ_WF_mtype_ext; intros; destruct mce; destruct mde; destruct H as [H1 [H2 H3]]; split; try split; auto.
    generalize Weakening_2_1_2 H2; clear; induction l; intros; constructor; inversion H2; subst; auto;
      eapply Weakening_2_1_2; assumption.
    assert (exists tys, tys = (Tys_Trans t l (map (fun yo : GTy * N => N_Wrap (snd yo)) t))) as tys_eq by 
      (eexists; reflexivity); destruct tys_eq as [tys tys_eq]; rewrite <- tys_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in H3.
    generalize l Weakening_2_1_1 H3; clear; induction tys; intros; inversion H3; subst; constructor.
    eapply Weakening_2_1_1; assumption.
    auto.
  Qed.

  Lemma FJ_WF_mtype_Us_map_app_Weaken : forall gamma gamma' mce mde tys tys', 
    FJ_WF_mtype_Us_map Ty Context gamma mce mde tys tys' ->
    FJ_WF_mtype_Us_map _ _ (app_context gamma gamma') mce mde tys tys'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma FJ_WF_mtype_U_map_app_Weaken : forall gamma gamma' mce mde ty ty', 
    FJ_WF_mtype_U_map Ty Context gamma mce mde ty ty' ->
    FJ_WF_mtype_U_map _ _ (app_context gamma gamma') mce mde ty ty'.
    intros; inversion H; subst; constructor; auto.
  Qed.
  
  Lemma FJ_WF_mtype_ext_app_Weaken : forall gamma gamma' mce mde, 
    FJ_WF_mtype_ext Context gamma mce mde ->
    FJ_WF_mtype_ext _ (app_context gamma gamma') mce mde.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma Weakening_2_1_3_1 (Weakening_2_1_3_1_rect : forall delta e T (WF_e : E_WF delta e T),
    Weakening_2_1_3_1_P _ _ _ WF_e) : forall delta e T (WF_e : FJ_E_WF delta e T),
    Weakening_2_1_3_1_P _ _ _ (FJ_E_WF_Wrap _ _ _ WF_e).
    intros; eapply FJ_FJ_E_WF_rect' with (P := Weakening_2_1_3_1_P) (Q := Weakening_2_1_3_1_Q);
      unfold Weakening_2_1_3_1_P; unfold Weakening_2_1_3_1_Q; intros; 
        try (eapply FJ_E_WF_Wrap; econstructor); eauto.
    generalize Weakening_2_1_1 Us' sub_Ss_Us'; clear; induction Ss; intros; inversion sub_Ss_Us'; subst;
      constructor; eauto; eapply Weakening_2_1_1; auto.
    eapply Weakening_2_1_2; assumption.
    generalize Weakening_2_1_1 fds sub_fds; clear; induction Ss; intros; inversion sub_fds; subst;
      constructor; eauto; destruct b; eapply Weakening_2_1_1; auto.
    constructor.
    constructor; eauto.
    eapply Weakening_2_1_3_1_rect; assumption.
  Defined.

  Variables (Free_Vars : Ty -> list TX -> Prop)
    (TE_Free_Vars : ty_ext -> list TX -> Prop).

  Inductive GJ_Free_Vars : Ty -> list TX -> Prop :=
    FV_Var : forall X, GJ_Free_Vars (TyVar X) (X :: nil).

  Inductive FJ_Free_Vars : Ty -> list TX -> Prop :=
    FV_Ty_def : forall cl te txs, TE_Free_Vars te txs ->
      FJ_Free_Vars (FJ_Ty_Wrap (ty_def C ty_ext te cl)) txs.

  Inductive GJ_TE_Free_Vars : @GTy_ext ty_def_ext -> list TX -> Prop :=
    TE_FV_GTy_ext : forall tys te txs, List_P2 tys txs Free_Vars -> 
      GJ_TE_Free_Vars (tys, te) (fold_right (@app _) nil txs).
      
  Variable (GTy_ext_Wrap : @GTy_ext ty_def_ext -> ty_ext)
    (GJ_Free_Vars_Wrap : forall ty txs, GJ_Free_Vars ty txs -> Free_Vars ty txs)
    (FJ_Free_Vars_Wrap : forall ty txs, FJ_Free_Vars ty txs -> Free_Vars ty txs)
    (GJ_TE_Free_Vars_Wrap : forall te txs, GJ_TE_Free_Vars te txs -> TE_Free_Vars (GTy_ext_Wrap te) txs)
    (GJ_Free_Vars_invert : forall ty txs, Free_Vars (Ty_Wrap ty) txs -> GJ_Free_Vars (Ty_Wrap ty) txs)
    (FJ_Free_Vars_invert : forall ty txs, Free_Vars (FJ_Ty_Wrap ty) txs -> FJ_Free_Vars (FJ_Ty_Wrap ty) txs)
    (GJ_TE_Free_Vars_invert : forall te txs, TE_Free_Vars (GTy_ext_Wrap te) txs -> GJ_TE_Free_Vars te txs)
    (TE_trans : ty_ext -> list TX -> list Ty -> ty_ext)
    (GJ_Ty_Wrap_inject : forall ty ty', Ty_Wrap ty = Ty_Wrap ty' -> ty = ty')
    (GTy_ext_Wrap_inject : forall te te', GTy_ext_Wrap te = GTy_ext_Wrap te' -> te = te').

  Definition FJ_Ty_Trans (ty : FJ_Ty C ty_ext) txs tys : Ty :=
    match ty with 
      ty_def te c => (FJ_Ty_Wrap (@ty_def _ _ (TE_trans te txs tys) c))
    end.

  Definition GJ_TE_Trans (te : @GTy_ext ty_def_ext) txs tys : @GTy_ext ty_def_ext :=
    (map (fun ty => Ty_trans ty txs tys) (fst te), snd te).

  Definition Ty_trans_nil_P ty := forall Us, Ty_trans ty nil Us = ty.
  Definition Ty_trans_nil'_P ty := forall Ys, Ty_trans ty Ys nil = ty.
  Definition TE_trans_nil_P te := forall Us, TE_trans te nil Us = te.
  Definition TE_trans_nil'_P te := forall Ys, TE_trans te Ys nil = te.

  Variable (FJ_Ty_trans_invert : forall ty txs tys, Ty_trans (FJ_Ty_Wrap ty) txs tys = FJ_Ty_Trans ty txs tys)
    (GJ_Ty_trans_invert : forall ty Xs Us, Ty_trans (Ty_Wrap ty) Xs Us= GTy_trans ty Xs Us)
    (GJ_TE_Trans_invert : forall te Ys Us, TE_trans (GTy_ext_Wrap te) Ys Us = GTy_ext_Wrap (GJ_TE_Trans te Ys Us)).

  Lemma FJ_Ty_trans_nil : forall te c, TE_trans_nil_P te -> Ty_trans_nil_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_nil_P; intros; rewrite FJ_Ty_trans_invert; simpl.
    simpl; congruence.
  Defined.

  Lemma GJ_Ty_trans_nil : forall X, Ty_trans_nil_P (TyVar X).
    unfold Ty_trans_nil_P; intros; rewrite GJ_Ty_trans_invert; simpl.
    simpl; congruence.
  Defined.

  Lemma FJ_Ty_trans_nil' : forall te c, TE_trans_nil'_P te -> Ty_trans_nil'_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_nil'_P; intros; rewrite FJ_Ty_trans_invert; simpl.
    simpl; congruence.
  Defined.

  Lemma GJ_Ty_trans_nil' : forall X, Ty_trans_nil'_P (TyVar X).
    unfold Ty_trans_nil'_P; intros; rewrite GJ_Ty_trans_invert; simpl.
    destruct Ys; simpl; reflexivity.
  Defined.

  Lemma TE_trans_nil_H1 : forall te, TE_trans_nil_P (GTy_ext_Wrap (nil, te)).
    unfold TE_trans_nil_P; intros; rewrite GJ_TE_Trans_invert; reflexivity.
  Qed.

  Lemma TE_trans_nil_H2 : forall ty tys' te, TE_trans_nil_P (GTy_ext_Wrap (tys', te)) ->
    Ty_trans_nil_P ty -> 
    TE_trans_nil_P (GTy_ext_Wrap (ty :: tys', te)).
    unfold TE_trans_nil_P; unfold Ty_trans_nil_P; intros; rewrite GJ_TE_Trans_invert; simpl.
    generalize (H Us); rewrite GJ_TE_Trans_invert; intros.
    apply GTy_ext_Wrap_inject in H1; injection H1; intros.
    unfold GJ_TE_Trans; simpl; rewrite H2; rewrite H0; reflexivity.
  Qed.
  
  Lemma TE_trans_nil'_H1 : forall te, TE_trans_nil'_P (GTy_ext_Wrap (nil, te)).
    unfold TE_trans_nil'_P; intros; rewrite GJ_TE_Trans_invert; reflexivity.
  Qed.

  Lemma TE_trans_nil'_H2 : forall ty tys' te, TE_trans_nil'_P (GTy_ext_Wrap (tys', te)) ->
    Ty_trans_nil'_P ty -> 
    TE_trans_nil'_P (GTy_ext_Wrap (ty :: tys', te)).
    unfold TE_trans_nil'_P; unfold Ty_trans_nil'_P; intros; rewrite GJ_TE_Trans_invert; simpl.
    generalize (H Ys); rewrite GJ_TE_Trans_invert; intros.
    apply GTy_ext_Wrap_inject in H1; injection H1; intros.
    unfold GJ_TE_Trans; simpl; rewrite H2; rewrite H0; reflexivity.
  Qed.

  Variables (Ty_trans_nil : forall ty, Ty_trans_nil_P ty)
    (Ty_trans_nil' : forall ty, Ty_trans_nil'_P ty)
    (TE_trans_nil : forall te, TE_trans_nil_P te)
    (TE_trans_nil' : forall te, TE_trans_nil'_P te).
  
  Definition Free_Vars_Subst_P (ty : Ty) := 
    forall (Xs Ys : list TX) (Us : list Ty),
    (forall X, In X Xs -> ~ In X Ys) -> Free_Vars ty Xs -> Ty_trans ty Ys Us = ty.
  
  Definition Free_Vars_Subst_Q (te : ty_ext) :=
    forall Ys Us Xs, 
      (forall X : TX, In X Xs -> ~ In X Ys) -> TE_Free_Vars te Xs -> TE_trans te Ys Us = te.

  Lemma Free_Vars_Subst_H1 : forall X (Xs Ys : list TX) (Us : list Ty),
    (forall X, In X Xs -> ~ In X Ys) -> Free_Vars (TyVar X) Xs -> GTy_trans (TyVar X) Ys Us = TyVar X.
    intros; apply GJ_Free_Vars_invert in H0; inversion H0; subst; simpl.
    apply GJ_Ty_Wrap_inject in H2; injection H2; subst.
    assert (~ In X1 Ys) as H1 by (eapply H; simpl; left; congruence); generalize Us H1; clear; 
      induction Ys; simpl; intros; subst; auto.
    destruct Us; auto.
    destruct (TX_eq_dec a X0); subst; simpl.
    elimtype False; tauto.
    eapply IHYs; auto.
  Qed.

  Lemma Free_Vars_Subst_H2 : forall te cl, Free_Vars_Subst_Q te -> 
    forall (Xs Ys : list TX) (Us : list Ty),
    (forall X, In X Xs -> ~ In X Ys) -> Free_Vars (FJ_Ty_Wrap (ty_def _ _ te cl)) Xs -> 
    FJ_Ty_Trans (ty_def _ _ te cl) Ys Us = FJ_Ty_Wrap (ty_def _ _ te cl).
    simpl; intros; erewrite H.
    reflexivity.
    eapply H0.
    apply FJ_Free_Vars_invert in H1; inversion H1; subst.
    apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst; assumption.
  Qed.
  
  Lemma Free_Vars_Subst_H3 : forall te Ys Us Xs, 
    (forall X : TX, In X Xs -> ~ In X Ys) -> TE_Free_Vars (GTy_ext_Wrap (nil, te)) Xs -> GJ_TE_Trans (nil, te) Ys Us = (nil, te).
    unfold GJ_TE_Trans; simpl; reflexivity.
  Qed.
  
  Lemma Free_Vars_Subst_H4 : forall ty tys te,  
    Free_Vars_Subst_Q (GTy_ext_Wrap (tys, te)) -> Free_Vars_Subst_P ty ->
    forall Ys Us Xs, (forall X : TX, In X Xs -> ~ In X Ys) -> TE_Free_Vars (GTy_ext_Wrap (ty :: tys, te)) Xs -> 
      GJ_TE_Trans (ty :: tys, te) Ys Us = (ty :: tys, te).
    unfold Free_Vars_Subst_P; unfold Free_Vars_Subst_Q; unfold GJ_TE_Trans; intros; simpl.
    apply GJ_TE_Free_Vars_invert in H2; inversion H2; subst.
    apply P2_if_P2' in H6; inversion H6; subst.
    assert (forall X : TX, In X (fold_right (@app _) nil Bs) -> ~ In X Ys) as H1' by
      (intros; apply H1; simpl; apply in_or_app; right; assumption).
    assert (TE_Free_Vars (GTy_ext_Wrap (tys, te)) (fold_right (@app _) nil Bs)) as H8' by
      (apply GJ_TE_Free_Vars_Wrap; econstructor; apply P2'_if_P2; simpl in H8; auto).
    generalize (H Ys Us _ H1' H8'); simpl; intros.
    rewrite GJ_TE_Trans_invert in H3; simpl in H3.
    apply GTy_ext_Wrap_inject in H3; injection H3; intros.
    rewrite H4; erewrite H0.
    reflexivity.
    intros; apply H1.
    simpl; apply in_or_app; left.
    apply H7.
    assumption.
  Qed.

 Definition map_Ty_trans_P ty := 
    forall (Xs Ys : list TX) (Us tys : list Ty) (typs : TyP_List),
      Free_Vars ty Ys ->
      (forall X : TX, In X Ys -> ~ In X Xs) ->
      Ty_trans (Ty_trans ty (Extract_TyVar typs) tys) Xs Us =
      Ty_trans ty (Extract_TyVar typs)
      (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
  
  Definition map_Ty_trans_Q te := forall Xs Ys Us tys typs,
    TE_Free_Vars te Ys -> 
    (forall X : TX, In X Ys -> ~ In X Xs) ->
    TE_trans (TE_trans te (Extract_TyVar typs) tys) Xs Us =
    TE_trans te (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).


  Variable (NIn_Ty_trans : forall X Xs Us, ~In X Xs -> Ty_trans (TyVar X) Xs Us = TyVar X)
    (Ty_trans_FJ : forall ty Xs Us, Ty_trans (FJ_Ty_Wrap ty) Xs Us = FJ_Ty_Trans ty Xs Us).

  Lemma GNIn_Ty_trans : forall X Xs Us, ~In X Xs -> GTy_trans (TyVar X) Xs Us = TyVar X.
    induction Xs; simpl; intros; auto;
      destruct Us; auto; destruct (TX_eq_dec a X0); intros;
        first [elimtype False; tauto | eapply IHXs; unfold not; intros; apply H; auto].
  Qed.

  Lemma map_Ty_trans_H1 : forall X (Xs Ys : list TX) (Us tys : list Ty) (typs : TyP_List),
    Free_Vars (TyVar X) Ys ->
    (forall X : TX, In X Ys -> ~ In X Xs) ->
    Ty_trans (GTy_trans (TyVar X) (Extract_TyVar typs) tys) Xs Us =
    GTy_trans (TyVar X) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    intros; apply GJ_Free_Vars_invert in H; inversion H; subst; simpl.
    apply GJ_Ty_Wrap_inject in H2; injection H2; subst.
    assert (~ In X1 Xs) as H1 by (eapply H0; simpl; left; congruence); generalize tys Us H1 NIn_Ty_trans; clear; 
      induction (Extract_TyVar typs); simpl; intros; subst; auto.
    destruct tys; simpl; auto.
    destruct (TX_eq_dec a X0); subst; auto.
  Qed.

  Lemma map_Ty_trans_H2 : forall te cl, map_Ty_trans_Q te -> 
    forall (Xs Ys : list TX) (Us tys : list Ty) (typs : TyP_List),
    Free_Vars (FJ_Ty_Wrap (ty_def _ _ te cl)) Ys ->
    (forall X : TX, In X Ys -> ~ In X Xs) ->
    Ty_trans (FJ_Ty_Trans (ty_def _ _ te cl) (Extract_TyVar typs) tys) Xs Us =
    FJ_Ty_Trans (ty_def _ _ te cl) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    simpl; intros; unfold map_Ty_trans_Q in H.
    rewrite Ty_trans_FJ; simpl.
    apply FJ_Free_Vars_invert in H0; inversion H0; subst.
    apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst.
    erewrite H.
    reflexivity.
    apply H3.
    exact H1.
  Qed.
  
  Lemma map_Ty_trans_H3 : forall te Xs Ys Us tys typs,
    TE_Free_Vars (GTy_ext_Wrap (nil, te)) Ys -> 
    (forall X : TX, In X Ys -> ~ In X Xs) ->
    GJ_TE_Trans (GJ_TE_Trans (nil, te) (Extract_TyVar typs) tys) Xs Us =
    GJ_TE_Trans (nil, te) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys). 
    unfold GJ_TE_Trans; simpl; reflexivity.
  Qed.
  
  Lemma map_Ty_trans_H4 : forall ty tys' te, 
    map_Ty_trans_Q (GTy_ext_Wrap (tys', te)) -> 
    map_Ty_trans_P ty -> 
    forall Xs Ys Us tys typs,
    TE_Free_Vars (GTy_ext_Wrap (ty :: tys', te)) Ys -> 
    (forall X : TX, In X Ys -> ~ In X Xs) ->
    GJ_TE_Trans (GJ_TE_Trans (ty :: tys', te) (Extract_TyVar typs) tys) Xs Us =
    GJ_TE_Trans (ty :: tys', te) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys). 
    unfold map_Ty_trans_P; unfold map_Ty_trans_Q; unfold GJ_TE_Trans; intros; simpl.
    apply GJ_TE_Free_Vars_invert in H1; inversion H1; subst.
    apply P2_if_P2' in H6; inversion H6; subst.
    assert (forall X : TX, In X (fold_right (@app _) nil Bs) -> ~ In X Xs) as H1' by
      (intros; apply H2; simpl; apply in_or_app; right; assumption).
    assert (TE_Free_Vars (GTy_ext_Wrap (tys', te)) (fold_right (@app _) nil Bs)) as H8' by
      (apply GJ_TE_Free_Vars_Wrap; econstructor; apply P2'_if_P2; simpl in H8; auto).
    generalize (H Xs _ Us tys typs H8' H1'); simpl; intros.
    repeat (rewrite GJ_TE_Trans_invert in H3; simpl in H3).
    apply GTy_ext_Wrap_inject in H3; injection H3; intros.
    rewrite H4; erewrite H0.
    reflexivity.
    apply H5.
    intros; apply H2.
    simpl; apply in_or_app; left.
    apply H7.
  Qed.

  Definition map_Ty_trans_P' ty := 
    forall (Xs Ys : list _) (Us tys : list Ty) (typs : TyP_List),
      Free_Vars ty Ys -> length typs = length tys -> 
      (forall X : _, In X Ys -> In X (Extract_TyVar typs)) ->
      Ty_trans (Ty_trans ty (Extract_TyVar typs) tys) Xs Us =
      Ty_trans ty (Extract_TyVar typs)
      (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
  
  Definition map_Ty_trans_Q' te := forall Xs Ys Us tys typs,
    TE_Free_Vars te Ys -> length typs = length tys -> 
    (forall X : TX, In X Ys -> In X (Extract_TyVar typs)) ->
    TE_trans (TE_trans te (Extract_TyVar typs) tys) Xs Us =
    TE_trans te (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).

  Lemma map_Ty_trans'_H1 : forall X (Xs Ys : list TX) (Us tys : list Ty) (typs : TyP_List),
    Free_Vars (TyVar X) Ys -> length typs = length tys -> 
    (forall X : TX, In X Ys -> In X (Extract_TyVar typs)) ->
    Ty_trans (GTy_trans (TyVar X) (Extract_TyVar typs) tys) Xs Us =
    GTy_trans (TyVar X) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    intros; apply GJ_Free_Vars_invert in H; inversion H; subst; simpl.
    apply GJ_Ty_Wrap_inject in H3; injection H3; intros; subst.
    assert (In X0 (Extract_TyVar typs)) as H2 by (eapply H1; simpl; left; congruence); generalize tys Us H2 H0; clear; 
      induction typs; simpl; intros; subst; auto.
    contradiction.
    destruct tys; simpl; auto; try discriminate.
    destruct a; destruct g; simpl in *|-*.
    destruct (TX_eq_dec t0 X0); subst; auto.
    destruct H2.
    elimtype False; auto.
    eapply IHtyps; eauto.
  Qed.

  Lemma map_Ty_trans'_H2 : forall te cl, map_Ty_trans_Q' te -> 
    forall (Xs Ys : list TX) (Us tys : list Ty) (typs : TyP_List),
    Free_Vars (FJ_Ty_Wrap (ty_def _ _ te cl)) Ys ->
    length typs = length tys -> 
    (forall X : TX, In X Ys -> In X (Extract_TyVar typs)) ->
    Ty_trans (FJ_Ty_Trans (ty_def _ _ te cl) (Extract_TyVar typs) tys) Xs Us =
    FJ_Ty_Trans (ty_def _ _ te cl) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    simpl; intros; unfold map_Ty_trans_Q in H.
    rewrite Ty_trans_FJ; simpl.
    apply FJ_Free_Vars_invert in H0; inversion H0; subst.
    apply FJ_Ty_Wrap_inject in H3; injection H3; intros; subst.
    erewrite H.
    reflexivity.
    apply H4.
    assumption.
    exact H2.
  Qed.
  
  Lemma map_Ty_trans'_H3 : forall te Xs Ys Us tys typs,
    TE_Free_Vars (GTy_ext_Wrap (nil, te)) Ys -> length typs = length tys -> 
    (forall X : TX, In X Ys -> In X (Extract_TyVar typs)) ->
    GJ_TE_Trans (GJ_TE_Trans (nil, te) (Extract_TyVar typs) tys) Xs Us =
    GJ_TE_Trans (nil, te) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    unfold GJ_TE_Trans; simpl; reflexivity.
  Qed.
  
  Lemma map_Ty_trans'_H4 : forall ty tys te, 
    map_Ty_trans_Q' (GTy_ext_Wrap (tys, te)) -> 
    map_Ty_trans_P' ty -> 
    forall Xs Ys Us tys' typs,
    TE_Free_Vars (GTy_ext_Wrap (ty :: tys, te)) Ys -> 
    length typs = length tys' -> 
    (forall X : TX, In X Ys -> In X (Extract_TyVar typs)) ->
    GJ_TE_Trans (GJ_TE_Trans (ty :: tys, te) (Extract_TyVar typs) tys') Xs Us =
    GJ_TE_Trans (ty :: tys, te) (Extract_TyVar typs)
    (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys'). 
    unfold map_Ty_trans_P'; unfold map_Ty_trans_Q'; unfold GJ_TE_Trans; intros; simpl.
    apply GJ_TE_Free_Vars_invert in H1; inversion H1; subst.
    apply P2_if_P2' in H7; inversion H7; subst.
    assert (forall X : TX, In X (fold_right (@app _) nil Bs) -> In X (Extract_TyVar typs)) as H1' by
      (intros; apply H3; simpl; apply in_or_app; right; assumption).
    assert (TE_Free_Vars (GTy_ext_Wrap (tys, te)) (fold_right (@app _) nil Bs)) as H8' by
      (apply GJ_TE_Free_Vars_Wrap; econstructor; apply P2'_if_P2; simpl in H9; auto).
    generalize (H Xs _ Us tys' typs H8' H2 H1'); simpl; intros.
    repeat (rewrite GJ_TE_Trans_invert in H4; simpl in H4).
    apply GTy_ext_Wrap_inject in H4; injection H4; intros.
    rewrite H5; erewrite H0; eauto.
    intros; apply H3; simpl; apply in_or_app; left; assumption.
  Qed.

  Definition exists_Free_Vars_P ty := exists Xs, Free_Vars ty Xs.

  Definition exists_Free_Vars_Q te := exists Xs, TE_Free_Vars te Xs.

  Lemma exists_Free_Vars_H1 : forall X, exists_Free_Vars_P (TyVar X).
    unfold exists_Free_Vars_P; intros.
    exists (X0 :: nil); apply GJ_Free_Vars_Wrap; constructor.
  Qed.

  Lemma exists_Free_Vars_H2 : forall te cl, exists_Free_Vars_Q te -> 
    exists_Free_Vars_P (FJ_Ty_Wrap (ty_def _ _ te cl)).
    unfold exists_Free_Vars_P; unfold exists_Free_Vars_Q; intros.
    destruct H as [Xs ex_Xs]; exists Xs; apply FJ_Free_Vars_Wrap; constructor; assumption.
  Qed.
  
  Lemma exists_Free_Vars_H3 : forall te, exists_Free_Vars_Q (GTy_ext_Wrap (nil, te)).
    unfold exists_Free_Vars_Q; simpl;intros; exists nil; apply GJ_TE_Free_Vars_Wrap.
    apply (TE_FV_GTy_ext nil te nil).
    apply P2'_if_P2; constructor.
  Qed.
  
  Lemma exists_Free_Vars_H4 : forall ty tys te, 
    exists_Free_Vars_Q (GTy_ext_Wrap (tys, te)) -> 
    exists_Free_Vars_P ty -> 
    exists_Free_Vars_Q (GTy_ext_Wrap (ty :: tys, te)).
    unfold exists_Free_Vars_Q; unfold exists_Free_Vars_P; intros.
    destruct H0 as [Xs ex_Xs]; destruct H as [Xs' ex_Xs']; exists (app Xs Xs');
      apply GJ_TE_Free_Vars_Wrap.
    apply GJ_TE_Free_Vars_invert in ex_Xs'; inversion ex_Xs'; subst.
    apply (TE_FV_GTy_ext (ty :: tys) te (Xs :: _)).
    apply P2'_if_P2; apply P2_if_P2' in H2; constructor; auto.
  Qed.

  Variable (exists_Free_Vars : forall ty, exists_Free_Vars_P ty).

  Lemma exists_Free_Vars' : forall tys, exists Xs, List_P2 tys Xs Free_Vars.
    induction tys; intros.
    exists nil; apply P2'_if_P2; constructor.
    destruct IHtys as [Xs ex_Xs].
    destruct (exists_Free_Vars a).
    exists (x :: Xs); apply P2'_if_P2; apply P2_if_P2' in ex_Xs; constructor; auto.
  Qed.

  Definition wf_free_vars_P gamma ty (WF_ty : WF_Type gamma ty) := 
    forall XNs Xs, gamma = (update_Tlist Empty XNs) -> Free_Vars ty Xs -> 
      forall X, In X Xs -> In X (Extract_TyVar XNs).

  Definition wf_free_vars_Q gamma cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext gamma cld te) :=
    forall XNs Xs, gamma = (update_Tlist Empty XNs) -> TE_Free_Vars (GTy_ext_Wrap te) Xs ->
      forall X, In X Xs -> In X (Extract_TyVar XNs). 

  Definition wf_free_vars_Q_P1 gamma tys (P1 : List_P1 (WF_Type gamma) tys) :=
    forall XNs Xs, gamma = (update_Tlist Empty XNs) -> List_P2 tys Xs Free_Vars ->
      forall X, In X (fold_right (@app _) nil Xs) -> In X (Extract_TyVar XNs).

  Lemma wf_free_vars_ext_H1 : forall gamma ce tys typs te P1 len P2,
    wf_free_vars_Q_P1 gamma tys P1 -> 
    wf_free_vars_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext ce gamma typs tys te P1 len P2).
    unfold wf_free_vars_Q; unfold wf_free_vars_Q_P1; intros.
    apply GJ_TE_Free_Vars_invert in H1; inversion H1; subst.
    eauto.
  Qed.

  Lemma wf_free_vars_ext_H2 : forall gamma, 
    wf_free_vars_Q_P1 gamma _ (Nil (WF_Type gamma)).
    unfold wf_free_vars_Q_P1; intros; subst.
    destruct Xs; simpl in H1.
    contradiction.
    elimtype False; eapply List_P2_nil'; eassumption.
  Qed.
    
  Lemma wf_free_vars_ext_H3 : forall gamma ty tys P_ty P_tys, 
    wf_free_vars_P _ _ P_ty -> wf_free_vars_Q_P1 _ tys P_tys -> 
    wf_free_vars_Q_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold wf_free_vars_Q_P1; unfold wf_free_vars_P; intros; destruct Xs; subst.
    elimtype False; eapply List_P2_nil; eassumption.
    apply P2_if_P2' in H2; inversion H2; subst.
    simpl in H3; apply in_app_or in H3; destruct H3; eauto.
    eapply H0; auto.
    apply P2'_if_P2; eauto.
    eauto.
  Qed.

  Definition wf_free_vars_ext := 
    wf_class_ext_rect _ _ _ wf_free_vars_ext_H1 wf_free_vars_ext_H2 wf_free_vars_ext_H3.

  Section map_mbody_tot_Section. 

    Variable m_call_ext' : Set.
    Variable mbody_m_call_map : TyP_List -> list Ty  -> m_call_ext -> m_call_ext -> Prop.
    Variable mbody_new_map : TyP_List -> list Ty -> ty_ext -> ty_ext -> Prop.
    Variable E_Ty_trans' : TyP_List -> list Ty -> E -> E -> Prop. 
    Variable map_e_invert : forall XNs Us e e', 
      E_Ty_trans' XNs Us (FJ_E_Wrap e) e' -> 
      E_Ty_Trans _ _ FJ_E_Wrap mbody_m_call_map mbody_new_map E_Ty_trans' XNs Us (FJ_E_Wrap e) e'.
    Variable FJ_E_Wrap_inject : forall e e', FJ_E_Wrap e = FJ_E_Wrap e' -> e = e'.
    Variable E_Ty_trans'_Wrap : forall XNs Us e e', 
      E_Ty_Trans _ _ FJ_E_Wrap mbody_m_call_map mbody_new_map E_Ty_trans' XNs Us e e' -> 
      E_Ty_trans' XNs Us e e'.
    Variable mbody_m_call_map_tot : forall XNs Us mce, 
      exists mce', mbody_m_call_map XNs Us mce mce'.
    Variable mbody_new_map_tot : forall XNs Us te, 
      exists te', mbody_new_map XNs Us te te'.
    
    Definition E_Ty_Trans_tot_P e := forall XNs Ts, 
      exists e' : E, E_Ty_trans' XNs Ts e e'.
    Definition E_Ty_Trans_tot_Q es := forall XNs Ts, 
      exists es', List_P2' (E_Ty_trans' XNs Ts) es es'.
    
    Lemma FJ_E_Ty_Trans_tot (FJ_E_Ty_Trans_tot_rect : forall e, E_Ty_Trans_tot_P e) :
      forall e, E_Ty_Trans_tot_P (FJ_E_Wrap e).
      intros ; apply e_rect with (P := E_Ty_Trans_tot_P) (Q := E_Ty_Trans_tot_Q);
        unfold E_Ty_Trans_tot_P; unfold E_Ty_Trans_tot_Q; intros;
          try (eexists; eapply E_Ty_trans'_Wrap; econstructor; fail).
      clear FJ_E_Ty_Trans_tot_rect.
      destruct (H XNs Ts) as [e' trans_e0].
      eexists; eapply E_Ty_trans'_Wrap; econstructor; eassumption.
      destruct (H XNs Ts) as [e' trans_e0]; destruct (H0 XNs Ts) as [es' trans_l];
        destruct (mbody_m_call_map_tot XNs Ts mce) as [mce' map_mce].
      eexists; eapply E_Ty_trans'_Wrap; econstructor; try eassumption.
      destruct cl'; destruct (H XNs Ts) as [e' trans_e0]; 
        destruct (mbody_new_map_tot XNs Ts t) as [te' map_t].
      eexists; eapply E_Ty_trans'_Wrap; econstructor; try eassumption.
      eexists; econstructor.
      destruct (H XNs Ts) as [e' trans_e0]; destruct (H0 XNs Ts) as [es' map_l].
      eexists (_ :: _); econstructor; eassumption.
      apply FJ_E_Ty_Trans_tot_rect; assumption.
    Defined.
    
    Lemma GJ_mbody_m_call_map_tot : forall XNs Us mce, 
      exists mce', GJ_mbody_m_call_map m_call_ext' XNs Us mce mce'.
      intros; destruct mce; eexists _; econstructor.
    Qed.
    
    Lemma GJ_mbody_new_map_tot : forall XNs Us te, 
      exists te', GJ_mbody_new_map ty_def_ext XNs Us te te'.
      intros; destruct te; eexists _; econstructor.
    Qed.

    Variable ty_ext' : Set.
    Variable md_ext' : Set.
    Variable mtype_build_tys' : cld_def_ext -> ty_ext' -> Ty -> list VD -> md_ext' -> list Ty -> list Ty -> Prop.
    Variable E_Ty_Trans_tot : forall e, E_Ty_Trans_tot_P e.

    Lemma map_mbody_tot : forall ce te mce me ty vds tys tys' e,
      mtype_build_tys mtype_build_tys' ce te ty vds me tys tys' -> 
      exists e' : E, map_mbody m_call_ext' _ _ _ _ E_Ty_trans' ce te mce me e e'.
      intros; inversion H; destruct mce.
      destruct (E_Ty_Trans_tot e (typs ++ typs') (tys0 ++ l)).
      exists x; constructor; assumption.
    Qed.

  End map_mbody_tot_Section.

  Lemma build_cte_Free_Vars (ce_build_cte' : cld_def_ext -> ty_def_ext -> Prop) : forall ce te',
    GJ_ce_build_cte ce_build_cte' ce te' -> forall (Y : _) (Zs : list _), GJ_TE_Free_Vars te' Zs ->
      In Y Zs -> In Y (Extract_TyVar (fst ce)).
    intros; inversion H; inversion H0; subst; simpl in *|-*.
    injection H6; intros; subst; clear H6.
    apply P2_if_P2' in H5; generalize typs H5 H1 GJ_Free_Vars_invert GJ_Ty_Wrap_inject; 
      clear; induction txs; simpl; intros.
    elimtype False; assumption.
    apply in_app_or in H1; destruct H1; inversion H5; subst;
      destruct typs; simpl in H0; try discriminate; injection H0; intros; 
        subst; clear H0; destruct p; destruct g; simpl in *|-*.
    apply GJ_Free_Vars_invert in H3; inversion H3; subst.
    apply GJ_Ty_Wrap_inject in H1; injection H1; intros; subst; simpl in H; destruct H; tauto.
    right; eapply IHtxs; try eassumption.
  Qed.

  Variable (TLookup_TUpdate_eq : forall gamma X ty, TLookup (TUpdate gamma X ty) X ty) 
     (TLookup_TUpdate_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
       TLookup (TUpdate gamma Y ty') X ty)
     (TLookup_TUpdate_neq' : forall gamma Y X ty ty', TLookup (TUpdate gamma Y ty') X ty -> X <> Y -> 
       TLookup gamma X ty)
     (TLookup_id : forall gamma X ty ty', TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty')
     (N_Wrap_inject : forall n n', N_Wrap n = N_Wrap n' -> n = n').

  Lemma GJ_wf_free_vars : 
    forall gamma ty wf_ty, wf_free_vars_P gamma ty (GJ_WF_Type_Wrap gamma ty wf_ty).
    unfold wf_free_vars_P; intros until XNs; revert gamma ty wf_ty; induction XNs; 
      intros; destruct wf_ty; subst.
    simpl in H2; elimtype False; eapply (TLookup_Empty tx ty); auto. 
    destruct a; destruct g; simpl in H2.
    destruct (TX_eq_dec t tx); subst.
    generalize (TLookup_id _ _ _ _ H2 (TLookup_TUpdate_eq _ _ _)); intros.
    apply GJ_Free_Vars_invert in H0; inversion H0; subst.
    simpl in H1; destruct H1; subst.
    simpl; left; generalize (GJ_Ty_Wrap_inject _ _ H4); intros; injection H; intros;
      subst; reflexivity.
    contradiction.
    simpl; right; eapply IHXNs.
    econstructor.
    eapply TLookup_TUpdate_neq'; eauto.
    reflexivity.
    eassumption.
    assumption.
  Qed.
      
  Variable (TE_Free_Vars_obj : forall gamma te Xs, wf_object_ext' gamma te -> TE_Free_Vars te Xs -> Xs = nil).

  Definition wf_free_vars_cld_ext_Q gamma ce te (_ : wf_class_ext' gamma ce te) :=
    forall XNs Xs, gamma = (update_Tlist Empty XNs) -> TE_Free_Vars te Xs ->
      forall X, In X Xs -> In X (Extract_TyVar XNs).

  Lemma GJ_TE_Free_Vars_obj : forall gamma te Xs, GJ_wf_object_ext gamma te -> 
    GJ_TE_Free_Vars te Xs -> Xs = nil.
    intros; inversion H; inversion H0; subst.
    injection H4; intros; subst.
    destruct txs; try reflexivity.
    elimtype False; P2_nil H3.
  Qed.

  Lemma FJ_wf_free_vars_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    wf_free_vars_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold wf_free_vars_P; intros.
    apply FJ_Free_Vars_invert in H0; inversion H0; subst.
    apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst; clear H2.
    rewrite (TE_Free_Vars_obj _ _ _ wf_obj H3) in H1; simpl in H1; contradiction.
  Qed.
    
  Lemma FJ_wf_free_vars_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    (wf_free_vars_cld_ext_Q gamma (cld_ce cld) te wf_cld_ext) -> 
    wf_free_vars_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold wf_free_vars_P; intros.
    eapply H; eauto.
    apply FJ_Free_Vars_invert in H1; inversion H1; subst; apply FJ_Ty_Wrap_inject in H3;
      injection H3; intros; subst; assumption.
  Qed.
    
  Definition NTy_trans n Xs Us := Ty_trans (N_Wrap n) Xs Us.

  Variable (NTy_trans : N -> list TX -> list Ty -> N)
    (wf_free_vars : forall gamma ty wf_ty, wf_free_vars_P gamma ty wf_ty)
    (subst_context : Context -> list TX -> list Ty -> Context)
    (subst_context_nil : forall delta Us, subst_context delta nil Us = delta)
    (subst_context_nil' : forall delta Xs, subst_context delta Xs nil = delta)
    (TLookup_subst : forall gamma X ty Xs Us, TLookup gamma X ty -> 
      TLookup (subst_context gamma Xs Us) X (NTy_trans ty Xs Us)).

  Definition Type_Subst_Sub_2_5_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall (delta_1 delta_2 : Context) (Xs : list _)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us -> 
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
      ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
    subtype (app_context delta_1 (subst_context delta_2 Xs Us)) 
    (Ty_trans S Xs Us) (Ty_trans T Xs Us).

  Variable (ce_build_cte : cld_ext -> ty_ext -> Prop)
    (Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop)
    (Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop)
    (L_WF_Ext : Context -> cld_ext -> C -> Prop)
    (L_build_context : cld_ext -> Context -> Prop)
    (override : Context -> M -> FJ_Ty C ty_ext -> md_ext -> list Ty -> Ty -> Prop)
    (map_Ty_trans' : forall ty, map_Ty_trans_P' ty)
    (map_Ty_trans : forall ty, map_Ty_trans_P ty)
    (FJ_Ty_unwrap : FJ_Ty C ty_ext -> FJ_Ty C (@GTy_ext ty_def_ext))
    (L_build_context' : cld_def_ext -> Context -> Prop)
    (L_build_context'_Empty_1 : forall ce gamma XNs T, L_build_context' ce gamma -> 
      WF_Type (update_Tlist gamma XNs) T -> WF_Type (update_Tlist Empty XNs) T)
    (L_build_context'_Empty_2 : forall ce gamma XNs S T, L_build_context' ce gamma -> 
      subtype (update_Tlist gamma XNs) S T -> subtype (update_Tlist Empty XNs) S T)
    (FJ_WF_Type_Wrap_invert : forall delta S, WF_Type delta (FJ_Ty_Wrap S) -> 
      FJ_WF_Type delta (FJ_Ty_Wrap S)).

  Lemma WF_Obj_ext_Lem mtype_build_te' : forall (gamma gamma0 : Context) (te0 te' te'' : @GTy_ext ty_def_ext) ce,
    GJ_wf_object_ext gamma0 te' ->
    @mtype_build_te cld_def_ext ty_def_ext mtype_build_te' ce te0 te' te'' ->
    GJ_wf_object_ext gamma te''.
    intros; inversion H; inversion H0; subst.
    injection H7; intros; subst; econstructor.
  Qed.

  Lemma GJ_WF_Bound_app_Weaken' : forall (gamma : Context) ty ty',
    GJ_Bound gamma ty ty' -> forall gamma', Bound' (app_context gamma gamma') ty ty'.
    intros; inversion H; subst.
    apply GJ_Bound'_Wrap; eapply GJ_WF_Bound_app_Weaken; assumption.
  Qed.

  Lemma N_WF_Bound_app_Weaken' : forall (gamma : Context) ty ty',
    N_Bound gamma ty ty' -> forall gamma', Bound' (app_context gamma gamma') ty ty'.
    intros; inversion H; subst.
    apply N_Bound'_Wrap; constructor.
  Qed.

  Definition Type_Subst_Sub_2_5_TE_P 
    (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) ce te te' te'' :=
    build_te ce te te' te'' ->
    forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
    (Us : list Ty) (XNs : TyP_List) ce', 
    (L_build_context ce gamma') ->
    wf_class_ext' gamma' ce' te' ->
    length Xs = length Us ->
    zip Xs Ns (fun x : TX => pair (TyVar x)) = Some XNs ->
    List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (NTy_trans N Xs Us)) ->
    List_P1 (WF_Type delta_1) Us ->
    build_te ce (TE_trans te Xs Us) te' (TE_trans te'' Xs Us).  

  Definition Type_Subst_Sub_2_5_TE_P' 
    (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) ce te te' te'' :=
    build_te ce te te' te'' ->
    forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
    (Us : list Ty) (XNs : TyP_List), 
    (L_build_context ce gamma') ->
    wf_object_ext' gamma' te' ->
    length Xs = length Us ->
    zip Xs Ns (fun x : TX => pair (TyVar x)) = Some XNs ->
    List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (NTy_trans N Xs Us)) ->
    List_P1 (WF_Type delta_1) Us ->
    build_te ce (TE_trans te Xs Us) te' (TE_trans te'' Xs Us).  

  Lemma GJ_Type_Subst_Sub_2_5_TE {build_te'} :
    forall ce te te' te'',
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te'' ->
      forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
        (Us : list Ty) (XNs : TyP_List) ce', 
        (GJ_definitions.L_build_context L_build_context' ce gamma') ->
        @GJ_wf_class_ext cld_def_ext ty_def_ext gamma' ce' te' ->
        length Xs = length Us ->
        zip Xs Ns (fun x : TX => pair (TyVar x)) = Some XNs ->
        List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (NTy_trans N Xs Us)) ->
        List_P1 (WF_Type delta_1) Us ->
        GJ_build_te build_te' ce (GJ_TE_Trans te Xs Us) te' (GJ_TE_Trans te'' Xs Us).
    intros; inversion H; subst.
    unfold GJ_TE_Trans; simpl.
    unfold Tys_Trans.
    assert (map (fun ty : Ty => Ty_trans ty Xs Us)
      (map (fun ty' : Ty => Ty_trans ty' (Extract_TyVar typs) tys) tys') =
      map (fun ty : Ty => Ty_trans ty (Extract_TyVar typs)
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
    rewrite H8.
    econstructor; auto.
    generalize typs H7; clear; induction tys; simpl; intros; auto;
      destruct typs; simpl in H7; first [discriminate | injection H7; intros; subst];
        simpl; rewrite IHtys; auto.
  Qed.
  
  Lemma GJ_Type_Subst_Sub_2_5_TE' {build_te'} :
    forall ce te te' te'',
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te'' ->
      forall (gamma' delta_1 delta_2 : Context) (Xs : list TX) (Ns : list N)
        (Us : list Ty) (XNs : TyP_List),
        (GJ_definitions.L_build_context L_build_context' ce gamma') ->
        GJ_wf_object_ext gamma' te' ->
        length Xs = length Us ->
        zip Xs Ns (fun x : TX => pair (TyVar x)) = Some XNs ->
        List_P2 Us Ns (fun (U : Ty) (N : N) => subtype delta_1 U (NTy_trans N Xs Us)) ->
        List_P1 (WF_Type delta_1) Us ->
        GJ_build_te build_te' ce (GJ_TE_Trans te Xs Us) te' (GJ_TE_Trans te'' Xs Us).
    intros; inversion H; subst.
    unfold GJ_TE_Trans; simpl.
    unfold Tys_Trans.
    assert (map (fun ty : Ty => Ty_trans ty Xs Us)
      (map (fun ty' : Ty => Ty_trans ty' (Extract_TyVar typs) tys) tys') =
      map (fun ty : Ty => Ty_trans ty (Extract_TyVar typs)
      (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys)) tys').
    inversion H1; subst; simpl; reflexivity.
    rewrite H8.
    econstructor; auto.
    generalize typs H7; clear; induction tys; simpl; intros; auto;
      destruct typs; simpl in H7; first [discriminate | injection H7; intros; subst];
        simpl; rewrite IHtys; auto.
  Qed.

  Definition L_WF :=
    L_WF _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ CT _ subtype
    WF_Type fields E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext
    override L_WF_Ext L_build_context.

  Variable (WF_CT : forall (c : C) cld, CT c = Some cld -> L_WF cld)
    (Type_Subst_Sub_2_5_TE : forall ce te te' te'', Type_Subst_Sub_2_5_TE_P build_te ce te te' te'')
    (Type_Subst_Sub_2_5_TE' : forall ce te te' te'', Type_Subst_Sub_2_5_TE_P' build_te ce te te' te'').

  Lemma Type_Subst_Sub_2_5_FJ 
    (Type_Subst_Sub_2_5_rect : forall delta S T sub_S_T, Type_Subst_Sub_2_5_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Type_Subst_Sub_2_5_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Type_Subst_Sub_2_5_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; repeat rewrite FJ_Ty_trans_invert; simpl.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    destruct (exists_Free_Vars (FJ_Ty_Wrap (ty_def C ty_ext te'' d))).
    generalize (WF_CT _ _ CT_c) as WF_d; intros.
    inversion WF_d; subst.
    apply FJ_WF_Type_Wrap_invert in H20; inversion H20; subst;
      apply FJ_Ty_Wrap_inject in H1; injection H1; intros; subst.
    eapply Type_Subst_Sub_2_5_TE'; eauto.
    eapply (Type_Subst_Sub_2_5_TE ce); try eassumption.
    apply Type_Subst_Sub_2_5_rect.
  Defined.
    
  Variable (TLookup_dec : forall gamma X, (exists ty, TLookup gamma X ty) \/ (forall ty, ~TLookup gamma X ty))
    (TLookup_unique : forall gamma X ty ty', TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty')
    (TLookup_app' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') -> TLookup delta X ty -> 
      TLookup (app_context gamma delta) X ty)
    (TLookup_app'' : forall gamma delta X ty, (forall ty', ~ TLookup gamma X ty') ->  
      TLookup (app_context gamma delta) X ty -> TLookup delta X ty)
    (TLookup_update_eq : forall gamma X ty, TLookup (TUpdate gamma X ty) X ty) 
    (TLookup_update_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty) 
    (TLookup_update_neq' : forall gamma Y X ty ty', X <> Y -> 
      TLookup (TUpdate gamma Y ty') X ty -> TLookup gamma X ty)
    (Free_Vars_Subst : forall ty, Free_Vars_Subst_P ty)
    (Ty_trans_eq_NTy_trans : forall N Xs Us, N_Wrap (NTy_trans N Xs Us) = Ty_trans N Xs Us).

  Lemma NIn_FV_Trans : forall (Xs Ys : list _) (Us : list Ty) (ty : N),
    Free_Vars ty Ys -> (forall y : _, In y Ys -> ~ In y Xs) -> 
    NTy_trans ty Xs Us = ty.
    intros.
    generalize Ty_trans_eq_NTy_trans Ty_trans_nil N_Wrap_inject (map_Ty_trans ty _ _ Us nil nil H H0); 
      clear; intros.
    simpl in H; rewrite Ty_trans_nil in H; rewrite <- Ty_trans_eq_NTy_trans in H; eauto.
  Qed.

  Lemma Type_Subst_Sub_2_5_GJ : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Type_Subst_Sub_2_5_P _ _ _ sub_S_T.
    unfold Type_Subst_Sub_2_5_P; intros.
    destruct sub_S_T; subst.
    destruct (TLookup_dec delta_1 x) as [[ty' In_x] | NIn_ty'].
    rename H4 into dist_Xs.
    destruct (dist_Xs _ _ In_x) as [NIn_x NIn_x'].
    rewrite NIn_Ty_trans; auto.
    rewrite <- Ty_trans_eq_NTy_trans.
    apply subtype_Wrap; constructor.
    rewrite (TLookup_unique _ _ _ _ (TLookup_app _ _ _ _ In_x) H5) in NIn_x', In_x. 
    destruct (exists_Free_Vars ty).
    erewrite NIn_FV_Trans with (Ys := x0); auto.
    apply NIn_x'; auto.
    clear H4; apply TLookup_app'' in H5.
    assert ((exists n, nth_error Xs n = Some x /\ forall m, nth_error Xs m = Some x -> n <= m)
      \/ ~ exists n, nth_error Xs n = Some x).
    generalize TX_eq_dec; clear; induction Xs.
    right; unfold not; intros; destruct H; destruct x0; simpl in H; discriminate.
    intro; destruct (TX_eq_dec x a); subst.
    left; exists 0; split; intros; auto with arith.
    destruct IHXs; auto.
    left; destruct H as [n' [H0 H1]]; exists (S n'); split; intros; auto.
    destruct m; simpl in H.
    inversion H; congruence.
    auto with arith.
    right; unfold not; intros; apply H.
    destruct H0 as [n' H1]; destruct n'.
    simpl in H1; elimtype False; apply n; injection H1; congruence.
    simpl in H1; exists n'; assumption.
    destruct H1 as [In_n | NIn_n].
    destruct In_n as [n [In_n Max_n]].
    assert (exists U, nth_error Us n = Some U /\ Ty_trans (TyVar x) Xs Us = U).
    generalize Us Xs Max_n H In_n GJ_Ty_trans_invert; clear; induction n; intros; destruct Xs; simpl in In_n;
      try discriminate; destruct Us; simpl in H; try discriminate.
    injection In_n; intros; exists t0; split; eauto.
    rewrite GJ_Ty_trans_invert; unfold GTy_trans; destruct (TX_eq_dec t x); intros; congruence.
    simpl; rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec t x); subst.
    elimtype False; generalize (Max_n 0 (refl_equal _)); intros H0; inversion H0.
    rewrite <- GJ_Ty_trans_invert; eapply IHn; auto.
    intros; generalize (Max_n (S m) H0); auto with arith.
    destruct H1 as [U [In_U Trans_U]]; rewrite Trans_U.
    destruct H2 as [fnd not_fnd].
    destruct (fnd _ _ In_U) as [N' [In_N' sub_U]].
    assert (ty = N').
    rename H0 into zip_XNs.
    generalize Ns XNs x ty n zip_XNs In_n In_N' H5 Max_n TX_eq_dec 
      TLookup_update_eq TLookup_unique TLookup_update_neq' ; clear; induction Xs; intros.
    rewrite nth_error_nil in In_n; discriminate.
    destruct Ns; simpl in zip_XNs; try discriminate.
    caseEq (zip Xs Ns (fun x : _ => pair (TyVar x))); rename H into zip_sub; 
      rewrite zip_sub in zip_XNs; inversion zip_XNs; subst.
    destruct n; simpl in In_n.
    injection In_n; intros; subst.
    eapply TLookup_unique.
    eapply H5.
    simpl in In_N'; injection In_N'; intros; subst.
    eapply TLookup_update_eq.
    eapply IHXs; eauto.
    destruct (TX_eq_dec x a); subst.
    generalize (Max_n 0 (refl_equal _)); intro Error; inversion Error.
    simpl in H5; eapply TLookup_update_neq'; eauto.
    intros m In_m; generalize (Max_n (S m) In_m); auto with arith.
    subst.
    eapply Weakening_2_1_1; rewrite <- Ty_trans_eq_NTy_trans; apply sub_U.
    erewrite Free_Vars_Subst with (Xs := (x :: nil)).
    rewrite <- Ty_trans_eq_NTy_trans; apply subtype_Wrap; constructor; eapply TLookup_app'; auto.
    eapply TLookup_subst.
    rename H0 into zip_XNs.
    generalize XNs Ns zip_XNs H5 NIn_n TLookup_update_neq'; clear; induction Xs; intros;
      destruct Ns; simpl in zip_XNs; try discriminate.
    injection zip_XNs; intros; subst.
    simpl in H5; auto.
    caseEq (zip Xs Ns (fun x : _ => pair (TyVar x))); rewrite H in zip_XNs;
      try discriminate.
    eapply IHXs; eauto.
    injection zip_XNs; intros; subst; simpl in H5; eapply TLookup_update_neq' with (Y := a); eauto.
    unfold not; intros; apply NIn_n; exists 0; simpl; rewrite H0; reflexivity.
    unfold not; intros; eapply NIn_n; destruct H0; eexists (S _); simpl; eauto.
    unfold not; intros; apply NIn_n; simpl in H1; destruct H1; subst.
    generalize H4; clear; induction Xs; simpl; intros.
    contradiction.
    destruct H4; subst.
    exists 0; reflexivity.
    destruct (IHXs H) as [n nth_n]; exists (S n); assumption.
    contradiction.
    apply GJ_Free_Vars_Wrap; constructor.
    assumption.
  Qed.

  Variable (Type_Subst_Sub_2_5 : forall delta S T sub_S_T, Type_Subst_Sub_2_5_P delta S T sub_S_T).

  Lemma Type_Subst_Sub_2_5_P2 : forall gamma Ss Ts (sub_S_Ts : List_P2' (subtype gamma) Ss Ts) 
    (delta_1 delta_2 : Context) (Xs : list _)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us -> 
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
      ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
    List_P2' (subtype (app_context delta_1 (subst_context delta_2 Xs Us)))
    (map (fun S => Ty_trans S Xs Us) Ss) (map (fun T => Ty_trans T Xs Us) Ts).
    induction Ss; intros; inversion sub_S_Ts; subst; simpl; constructor.
    eapply Type_Subst_Sub_2_5; try eassumption.
    reflexivity.
    eapply IHSs; eauto.
  Qed.

  Definition Type_Subst_WF_2_6_P gamma ty (WF_ty : WF_Type gamma ty) := 
    forall (delta_1 delta_2 : Context) (Xs : list TX)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us -> 
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
      ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
    WF_Type (app_context delta_1 (subst_context delta_2 Xs Us)) (Ty_trans ty Xs Us).

  Variable (cld_typs : cld_ext -> TyP_List).    

  Definition Type_Subst_WF_2_6_Q  gamma cld te 
    (wf_cld : wf_class_ext' gamma cld te) :=
    forall (delta_1 delta_2 : Context) (Xs : list TX)
      (Ns : list N) (Us : list Ty) (XNs : TyP_List) Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (cld_typs cld) Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar (cld_typs cld))),
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
      gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
      List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
      List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
        ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
      wf_class_ext' (app_context delta_1 (subst_context delta_2 Xs Us)) cld 
      (TE_trans te Xs Us).

  Definition Type_Subst_WF_2_6_P1 gamma Ss (WF_Ss : List_P1 (WF_Type gamma) Ss) := 
    forall (delta_1 delta_2 : Context) (Xs : list TX)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us -> 
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
      ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
    List_P1 (WF_Type (app_context delta_1 (subst_context delta_2 Xs Us)))
    (map (fun ty : Ty => Ty_trans ty Xs Us) Ss).

  Definition Ty_trans_trans_subst_P ty := forall Xs Ys Us Ps Vs, 
    length Ys = length Ps ->
    Free_Vars ty Vs -> 
    (forall V, In V Vs -> In V Ys) ->
    Ty_trans (Ty_trans ty Ys Ps) Xs Us = 
    Ty_trans ty Ys (map (fun ty : Ty => Ty_trans ty Xs Us) Ps).

  Definition Ty_trans_trans_subst_Q te := forall Xs Ys Us Ps Vs, 
    length Ys = length Ps ->
    TE_Free_Vars te Vs -> 
    (forall V, In V Vs -> In V Ys) ->
    (TE_trans (TE_trans te Ys Ps) Xs Us) =
    (TE_trans te Ys (map (fun ty : Ty => Ty_trans ty Xs Us) Ps)).

  Lemma GJ_Ty_trans_trans_subst : forall ty, Ty_trans_trans_subst_P (Ty_Wrap ty).
    unfold Ty_trans_trans_subst_P; repeat rewrite GJ_Ty_trans_invert; simpl.
    destruct ty; induction Ys; simpl; intros.
    apply GJ_Free_Vars_invert in H0; inversion H0; subst.
    elimtype False; simpl in H1; eapply H1; left; reflexivity.
    destruct Ps; simpl in H; try discriminate; injection H; intros; simpl.
    repeat rewrite GJ_Ty_trans_invert; simpl.
    destruct (TX_eq_dec a t); simpl; subst.
    reflexivity.
    repeat rewrite <- GJ_Ty_trans_invert; simpl.
    eapply IHYs; eauto.
    intros; destruct (H1 V); auto.
    apply GJ_Free_Vars_invert in H0; inversion H0; subst.
    apply GJ_Ty_Wrap_inject in H6; injection H6; intros; subst.
    simpl in H3; destruct H3; try tauto; congruence.
  Qed.
    
  Lemma FJ_Ty_trans_trans_subst : forall te c, Ty_trans_trans_subst_Q te ->
    Ty_trans_trans_subst_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_trans_subst_P; unfold Ty_trans_trans_subst_Q; intros;
      repeat (rewrite FJ_Ty_trans_invert; simpl).
    erewrite H; eauto.
    apply FJ_Free_Vars_invert in H1; inversion H1; subst;
      apply FJ_Ty_Wrap_inject in H3; injection H3; intros; subst; auto.
  Qed.

  Lemma Ty_trans_trans_subst_H3 : forall te Xs Ys Us Ps Vs, 
    length Ys = length Ps ->
    GJ_TE_Free_Vars (nil, te) Vs -> 
    (forall V, In V Vs -> In V Ys) ->
    (GJ_TE_Trans (GJ_TE_Trans (nil, te) Ys Ps) Xs Us) =
    (GJ_TE_Trans (nil, te) Ys (map (fun ty : Ty => Ty_trans ty Xs Us) Ps)).
    unfold GJ_TE_Trans; simpl; auto.
  Qed.
  
  Lemma Ty_trans_trans_subst_H4 : forall ty tys te, 
    Ty_trans_trans_subst_Q (GTy_ext_Wrap (tys, te)) -> 
    Ty_trans_trans_subst_P ty -> 
    forall Xs Ys Us Ps Vs, 
      length Ys = length Ps ->
      GJ_TE_Free_Vars (ty :: tys, te) Vs -> 
      (forall V, In V Vs -> In V Ys) ->
      (GJ_TE_Trans (GJ_TE_Trans (ty :: tys, te) Ys Ps) Xs Us) =
      (GJ_TE_Trans (ty :: tys, te) Ys (map (fun ty : Ty => Ty_trans ty Xs Us) Ps)).
    unfold Ty_trans_trans_subst_P; unfold Ty_trans_trans_subst_Q; intros.
    unfold GJ_TE_Trans; simpl; auto.
    inversion H2; subst; apply P2_if_P2' in H7; inversion H7; subst.
    erewrite H0; eauto.
    assert (TE_Free_Vars (GTy_ext_Wrap (tys, te)) (fold_right (@app _) nil Bs)) by
      (apply GJ_TE_Free_Vars_Wrap; constructor; apply P2'_if_P2; assumption).
    assert (forall V : TX, In V (fold_right (@app _) nil Bs) -> In V Ys) by
      (intros; eapply H3; simpl; apply in_or_app; tauto).
    generalize (H Xs Ys Us Ps (fold_right (@app _) nil Bs) H1 H4 H5); intro.
    repeat rewrite GJ_TE_Trans_invert in H8; apply GTy_ext_Wrap_inject in H8;
      unfold GJ_TE_Trans in H8; simpl in H8; congruence.
    intros; eapply H3; simpl; apply in_or_app; left; assumption.
  Qed.

  Variable (Ty_trans_trans_subst : forall ty, Ty_trans_trans_subst_P ty).

  Lemma Type_Subst_WF_2_6_ext_H1 : forall gamma (ce : cld_def_ext) tys typs te P1
    (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar typs) tys) typs) (subtype gamma)),
    Type_Subst_WF_2_6_P1 gamma tys P1-> 
    forall (delta_1 delta_2 : Context) (Xs : list TX)
      (Ns : list N) (Us : list Ty) (XNs : TyP_List) Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar typs)),
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
      gamma = app_context delta_1 (update_Tlist delta_2 XNs) -> 
      List_P2 Us Ns (fun U N => subtype delta_1 U (NTy_trans N Xs Us)) -> 
      List_P1 (WF_Type delta_1) Us -> (forall x ty, TLookup delta_1 x ty -> 
        ~ In x Xs /\ (forall Ys, Free_Vars ty Ys -> (forall y, In y Ys -> ~ In y Xs))) -> 
      GJ_wf_class_ext (app_context delta_1 (subst_context delta_2 Xs Us)) 
      (typs, ce) (GJ_TE_Trans (tys, te) Xs Us).
    unfold Type_Subst_WF_2_6_P1; intros.
    inversion H0; subst; econstructor.
    eapply H; eauto.
    simpl; generalize typs len; clear; induction tys; simpl; auto; 
      intros; destruct typs; simpl in len; first [discriminate | injection len; intros; subst;
        simpl; rewrite IHtys; auto].
    simpl; apply P2'_if_P2.
    apply P2_if_P2' in P2; generalize (Type_Subst_Sub_2_5_P2 _ _ _ P2
      _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5) as H'.
    generalize Ty_trans_trans_subst FV_typs Bound_Ys len; clear.
    intros Ty_trans_trans_subst; assert (forall typs' tys Ys
      (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar typs')),
      length (Extract_TyVar typs') = length tys ->
      map (fun T : Ty => Ty_trans T Xs Us)
      (map
        (fun typ' : GTy * N =>
          Ty_trans (snd typ') (Extract_TyVar typs') tys) typs) = 
      map
      (fun typ' : GTy * N =>
        Ty_trans (snd typ') (Extract_TyVar typs')
        (map (fun ty : Ty => Ty_trans ty Xs Us) tys)) typs).
    generalize Ty_trans_trans_subst; clear; induction typs; simpl; intros; auto.
    destruct a; simpl.
    inversion FV_typs; subst; erewrite IHtyps; eauto.
    assert (forall Y : TX, In Y b -> In Y (Extract_TyVar typs')).
    intros; apply Bound_Ys; simpl; apply in_or_app; left; assumption.
    erewrite Ty_trans_trans_subst; eauto.
    intros; eapply Bound_Ys; apply in_or_app; right; assumption.
    intros; erewrite H in H'; eauto.
    generalize tys len; clear; induction typs; simpl; intros; auto.
    destruct tys; try discriminate; simpl in *|-*; injection len; intros.
    erewrite IHtyps; eauto.
  Qed.

  Lemma Type_Subst_WF_2_6_ext_H2 : forall gamma, 
    Type_Subst_WF_2_6_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Type_Subst_WF_2_6_P1; intros; constructor.
  Qed.
    
  Lemma Type_Subst_WF_2_6_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Type_Subst_WF_2_6_P _ _ P_ty -> Type_Subst_WF_2_6_P1 _ tys P_tys -> 
    Type_Subst_WF_2_6_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Type_Subst_WF_2_6_P; unfold Type_Subst_WF_2_6_P1; intros;
      constructor; eauto.
    eapply H0; try eassumption.
  Qed.

  Variable (Type_Subst_WF_2_6_obj_ext : 
    forall gamma te delta_1 delta_2 Xs Us, wf_object_ext' gamma te ->
      wf_object_ext' (app_context delta_1 (subst_context delta_2 Xs Us)) (TE_trans te Xs Us)).

  Lemma GJ_Type_Subst_WF_2_6_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext)
    delta_1 delta_2 Xs Us, GJ_wf_object_ext delta te ->
    GJ_wf_object_ext (app_context delta_1 (subst_context delta_2 Xs Us)) (GJ_TE_Trans te Xs Us).
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_Type_Subst_WF_2_6_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Type_Subst_WF_2_6_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Type_Subst_WF_2_6_P; intros.
    rewrite FJ_Ty_trans_invert; simpl; apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma GJ_L_WF_bound : forall L_WF_Ext' (ce : @GJ_definitions.cld_ext cld_def_ext) gamma c,
    GJ_definitions.L_build_context L_build_context' ce gamma -> 
    GJ_definitions.L_WF_Ext L_WF_Ext' gamma ce c -> 
    exists Ys,
      List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (fst ce) Ys /\
      forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar (fst ce)).
    intros; inversion H; inversion H0; subst; injection H7; intros; subst.
    assert (List_P1  (fun typ : GTy * N => WF_Type (update_Tlist Empty XNs) (snd typ)) XNs) as H5' by
      (assert (exists XNs', XNs' = XNs) as eq_XNs' by (eexists _; reflexivity);
        destruct eq_XNs' as [XNs' eq_XNs'];
          revert H5; rewrite <- eq_XNs' at 1; rewrite <- eq_XNs' at 1;
            generalize XNs (fun T => L_build_context'_Empty_1 _ _ XNs T H1); clear;
              induction XNs'; intros; inversion H0; subst; constructor; eauto); clear H5.
    assert (forall XN, In XN XNs -> 
      forall Xs, Free_Vars (snd XN) Xs -> 
        forall X, In X Xs -> In X (Extract_TyVar XNs)) as wf_free_vars' by
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
    exists p; split; congruence. 
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
      
  Definition cld_typs' cld := cld_typs (cld_ce cld).

  Variable (L_WF_bound : forall cld, L_WF cld -> exists Ys,
      List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (cld_typs' cld) Ys /\
      forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar (cld_typs' cld))).
    
  Lemma FJ_Type_Subst_WF_2_6_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Type_Subst_WF_2_6_Q _ _ _ wf_cld_ext ->
    Type_Subst_WF_2_6_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Type_Subst_WF_2_6_P; unfold Type_Subst_WF_2_6_Q; intros.
    destruct (L_WF_bound _ (WF_CT _ _ CT_c)) as [Ys [Free_Ys Bound_Ys]].
    rewrite FJ_Ty_trans_invert; simpl; apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
  
  Lemma GJ_Type_Subst_WF_2_6 : forall delta S (WF_S : GJ_WF_Type delta S), 
    Type_Subst_WF_2_6_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Type_Subst_WF_2_6_P; intros; inversion WF_S; subst; simpl.
    assert ((exists n, nth_error Xs n = Some tx /\ forall m, nth_error Xs m = Some tx -> n <= m)
      \/ ~ exists n, nth_error Xs n = Some tx).
    generalize TX_eq_dec; clear; induction Xs.
    right; unfold not; intros H; destruct H; destruct x; simpl in H; discriminate.
    intros; destruct (TX_eq_dec tx a); subst.
    left; exists 0; split; intros; auto with arith.
    destruct IHXs; auto.
    left; destruct H as [n' [H0 H1]]; exists (S n'); split; intros; auto.
    destruct m; simpl in H.
    inversion H; congruence.
    auto with arith.
    right; unfold not; intros; apply H.
    destruct H0 as [n' H1]; destruct n'.
    simpl in H1; elimtype False; apply n; injection H1; congruence.
    simpl in H1; exists n'; assumption.
    destruct H1 as [In_n | NIn_n].
    destruct In_n as [n [In_n Max_n]].
    rename H into len_eq.
    assert (exists U, nth_error Us n = Some U /\ GTy_trans (TyVar tx) Xs Us = U).
    generalize Us Xs Max_n len_eq In_n; clear; induction n; intros; destruct Xs; simpl in In_n;
      try discriminate; destruct Us; simpl in len_eq; try discriminate.
    injection In_n; intros; exists t0; split; eauto.
    unfold GTy_trans; destruct (TX_eq_dec t tx); intros; congruence.
    simpl; unfold GTy_trans; destruct (TX_eq_dec t tx); subst.
    elimtype False; generalize (Max_n 0 (refl_equal _)); intros H; inversion H.
    eapply IHn.
    intros; generalize (Max_n (S m) H); auto with arith.
    congruence.
    auto.
    rewrite GJ_Ty_trans_invert; destruct H as [U [In_U Trans_U]]; rewrite Trans_U.
    eapply Weakening_2_1_2.
    rename H3 into WF_Us.
    generalize Us U In_U WF_Us; clear; induction n; intros.
    destruct Us; simpl in In_U; try discriminate.
    injection In_U; intros; subst.
    inversion WF_Us; subst; eauto.
    destruct Us; simpl in In_U.
    discriminate.
    inversion WF_Us; eauto.
    assert (Ty_trans (TyVar tx) Xs Us = TyVar tx).
    rewrite GJ_Ty_trans_invert.
    generalize tx Us NIn_n Ty_trans_nil' Ty_trans_nil TX_eq_dec; clear; induction Xs; simpl; eauto; intros.
    destruct Us.
    reflexivity.
    destruct (TX_eq_dec a tx); subst.
    elimtype False; eapply NIn_n.
    exists 0; simpl; reflexivity.
    eapply IHXs; unfold not; intros; eauto.
    eapply NIn_n; destruct H as [n' nth_n'].
    exists (S n'); auto.
    eapply TX_eq_dec.
    rewrite H1.
    destruct (TLookup_dec delta_1 tx) as [[fnd_X ty'] | NIn_X].
    apply GJ_WF_Type_Wrap; econstructor; eapply TLookup_app; eauto.
    assert (TLookup delta_2 tx ty).
    rename H0 into zip_XNs.
    generalize Xs Ns XNs zip_XNs NIn_n TLookup_update_neq' 
      (TLookup_app'' _ _ _ _ NIn_X H5); clear; induction Xs; intros.
    destruct Ns; simpl in zip_XNs; inversion zip_XNs; subst; auto.
    destruct Ns; simpl in zip_XNs; try discriminate. 
    caseEq (zip Xs Ns (fun x : _ => pair (TyVar x))); rewrite H0 in zip_XNs;
      inversion zip_XNs; subst.
    eapply IHXs; eauto.
    unfold not; intros Nth_X; apply NIn_n; destruct Nth_X as [n' NIn_n']; 
      eexists (S _); simpl; eauto.
    assert (tx <> a) by (unfold not; intros; apply NIn_n; exists 0; subst; reflexivity).
    simpl in H; eapply TLookup_update_neq'; eauto.
    apply GJ_WF_Type_Wrap; econstructor.
    eapply TLookup_app'; auto; eapply TLookup_subst; apply H6.
  Qed.

  Variables (rename_X : TX -> TX -> TX)
    (Ty_rename : Ty -> TX -> Ty)
    (TE_rename : ty_ext -> TX -> ty_ext)
    (NTy_rename : N -> TX -> N)
    (Ty_rename_eq_NTy_rename : forall n X, Ty_rename (N_Wrap n) X = NTy_rename n X)
    (rename_X_inject : forall X Y n, rename_X X n = rename_X Y n -> X = Y).  

  Definition FJ_Ty_rename ty (Y : TX) : Ty :=
    match ty with 
      |  ty_def te c => FJ_Ty_Wrap (ty_def _ _ (TE_rename te Y) c)
    end.

  Definition GJ_Ty_rename (ty : GTy) (Y : TX) : Ty :=
    match ty with 
      | TyVar X' => TyVar (rename_X X' Y)
    end.

  Definition GJ_TE_rename (te : @GTy_ext ty_def_ext) (Y : TX) :=
    match te with 
      (tys, te') => (map (fun ty => Ty_rename ty Y) tys, te')
    end.
        
  Variables (rename_context : Context -> TX -> Context)
  (TLookup_rename_context : forall gamma x ty Y, 
    TLookup gamma x ty -> TLookup (rename_context gamma Y) (rename_X x Y) (NTy_rename ty Y))
  (TLookup_rename_context' : forall gamma x ty n, 
    TLookup (rename_context gamma n) x ty -> exists x', exists ty', x = rename_X x' n /\ 
      ty = NTy_rename ty' n /\ TLookup gamma x' ty')
  (rename_X_eq : forall Y Y' X', rename_X Y X' = rename_X Y' X' -> Y = Y')
  (FJ_Ty_rename_invert : forall (ty : _) Y, Ty_rename (FJ_Ty_Wrap ty) Y = FJ_Ty_rename ty Y)
  (GJ_Ty_rename_invert : forall (ty : GTy) Y, Ty_rename ty Y = GJ_Ty_rename ty Y)
  (GJ_TE_rename_invert : forall te Y, TE_rename (GTy_ext_Wrap te) Y = 
    GTy_ext_Wrap (GJ_TE_rename te Y)).

   Definition Ty_rename_Ty_trans_P ty := forall Xs tys Y, 
     Ty_rename (Ty_trans ty Xs tys) Y = 
     Ty_trans (Ty_rename ty Y) (map (fun X' => rename_X X' Y) Xs) (map (fun ty => Ty_rename ty Y) tys).

   Definition Ty_rename_Ty_trans_Q te := forall Xs tys Y, 
     TE_rename (TE_trans te Xs tys) Y = 
     TE_trans (TE_rename te Y) (map (fun X' => rename_X X' Y) Xs) (map (fun ty => Ty_rename ty Y) tys).

   Lemma GJ_Ty_rename_Ty_trans : forall Y, Ty_rename_Ty_trans_P (Ty_Wrap (TyVar Y)).
     unfold Ty_rename_Ty_trans_P; intros; repeat rewrite GJ_Ty_trans_invert; 
       rewrite GJ_Ty_rename_invert; simpl.
     revert tys; induction Xs; simpl; intros.
     rewrite GJ_Ty_trans_invert; rewrite GJ_Ty_rename_invert; simpl;
       reflexivity.
     destruct tys; simpl.
     rewrite (Ty_trans_nil'); rewrite GJ_Ty_rename_invert; simpl; reflexivity.
     rewrite GJ_Ty_trans_invert; destruct (TX_eq_dec a Y); subst; simpl.
     destruct (TX_eq_dec (rename_X Y Y0) (rename_X Y Y0)).
     reflexivity.
     elimtype False; congruence.
     destruct (TX_eq_dec (rename_X a Y0) (rename_X Y Y0)).
     rewrite (rename_X_eq _ _ _ e) in n; elimtype False; congruence.
     rewrite IHXs; simpl; rewrite GJ_Ty_trans_invert; reflexivity.
   Qed.

   Lemma FJ_Ty_rename_Ty_trans : forall te c, Ty_rename_Ty_trans_Q te -> 
     Ty_rename_Ty_trans_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold Ty_rename_Ty_trans_P; unfold Ty_rename_Ty_trans_Q; intros;
       repeat (rewrite FJ_Ty_trans_invert; rewrite FJ_Ty_rename_invert; simpl).
     rewrite H; reflexivity.
   Qed.

  Lemma Ty_rename_Ty_trans_H3 : forall te Xs tys Y, 
    GJ_TE_rename (GJ_TE_Trans (nil, te) Xs tys) Y = 
    GJ_TE_Trans (GJ_TE_rename (nil, te) Y) (map (fun X' => rename_X X' Y) Xs) (map (fun ty => Ty_rename ty Y) tys).
    reflexivity.
  Qed.
  
  Lemma Ty_rename_Ty_trans_H4 : forall ty tys' te, 
    Ty_rename_Ty_trans_Q (GTy_ext_Wrap (tys', te)) -> 
    Ty_rename_Ty_trans_P ty -> 
    forall Xs tys Y,
    GJ_TE_rename (GJ_TE_Trans (ty :: tys', te) Xs tys) Y = 
    GJ_TE_Trans (GJ_TE_rename (ty :: tys', te) Y) (map (fun X' => rename_X X' Y) Xs) (map (fun ty => Ty_rename ty Y) tys).
    unfold Ty_rename_Ty_trans_P; unfold Ty_rename_Ty_trans_Q; simpl; intros.
    rewrite H0 at 1.
    unfold GJ_TE_Trans; simpl.
    generalize (H Xs tys Y); repeat (rewrite GJ_TE_Trans_invert; rewrite GJ_TE_rename_invert; simpl);
      repeat (rewrite GJ_TE_rename_invert; rewrite GJ_TE_Trans_invert; simpl); intros.
    apply GTy_ext_Wrap_inject in H1; injection H1; intros; subst;
      rewrite H2; reflexivity.
  Qed.

  Variable (Ty_rename_Ty_trans : forall ty, Ty_rename_Ty_trans_P ty).

  Lemma len_map : forall (A B: Type) (f : A -> B) As, length (map f As) = length As.
    induction As; simpl; auto.
  Qed.

  Definition Ty_rename_subtype_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall n, subtype (rename_context gamma n) (Ty_rename S n) (Ty_rename T n).

  Definition Ty_rename_eq_Ty_trans_P ty := forall Vs Y Ys,
    Free_Vars ty Vs -> (forall V, In V Vs -> In V Ys) -> 
    Ty_rename ty Y = Ty_trans ty Ys (map (fun V => Ty_Wrap (TyVar (rename_X V Y))) Ys).

  Definition Ty_rename_eq_Ty_trans_Q te := forall Vs Y Ys,
    TE_Free_Vars te Vs -> (forall V, In V Vs -> In V Ys) -> 
    TE_rename te Y = TE_trans te Ys (map (fun V => Ty_Wrap (TyVar (rename_X V Y))) Ys).

  Lemma GJ_Ty_rename_eq_Ty_trans : forall Y, Ty_rename_eq_Ty_trans_P (Ty_Wrap (TyVar Y)).
    unfold Ty_rename_eq_Ty_trans_P; intros; repeat rewrite GJ_Ty_trans_invert; 
      rewrite GJ_Ty_rename_invert; simpl.
    apply GJ_Free_Vars_invert in H; inversion H; subst.
    apply GJ_Ty_Wrap_inject in H2; injection H2; intros; subst.
    simpl in H0; generalize (H0 _ (or_introl _ (refl_equal _))); clear.
    induction Ys; simpl; intros.
    contradiction.
    destruct H; subst.
    destruct (TX_eq_dec Y Y); subst; auto.
    elimtype False; congruence.
    destruct (TX_eq_dec a Y); subst; auto.
  Qed.

   Lemma FJ_Ty_rename_eq_Ty_trans : forall te c, Ty_rename_eq_Ty_trans_Q te -> 
     Ty_rename_eq_Ty_trans_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold Ty_rename_eq_Ty_trans_P; unfold Ty_rename_eq_Ty_trans_Q; intros;
       repeat (rewrite FJ_Ty_trans_invert; rewrite FJ_Ty_rename_invert; simpl).
     erewrite H; auto.
     apply FJ_Free_Vars_invert in H0; inversion H0; subst.
     apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst; eassumption.
     assumption.
   Qed.

  Lemma Ty_rename_eq_Ty_trans_H3 : forall te Vs Y Ys,
    GJ_TE_Free_Vars (nil, te) Vs -> (forall V, In V Vs -> In V Ys) -> 
    GJ_TE_rename (nil, te) Y =
    GJ_TE_Trans (nil, te) Ys (map (fun V => Ty_Wrap (TyVar (rename_X V Y))) Ys).
    reflexivity.
  Qed.
  
  Lemma Ty_rename_eq_Ty_trans_H4 : forall ty tys te,
    Ty_rename_eq_Ty_trans_Q (GTy_ext_Wrap (tys, te)) -> 
    Ty_rename_eq_Ty_trans_P ty -> 
    forall Vs Y Ys,
    GJ_TE_Free_Vars (ty :: tys, te) Vs -> (forall V, In V Vs -> In V Ys) -> 
    GJ_TE_rename (ty :: tys, te) Y = 
    GJ_TE_Trans (ty :: tys, te) Ys (map (fun V => Ty_Wrap (TyVar (rename_X V Y))) Ys).
    unfold Ty_rename_eq_Ty_trans_P; unfold Ty_rename_eq_Ty_trans_Q; simpl; intros.
    unfold GJ_TE_Trans; simpl.
    inversion H1; apply P2_if_P2' in H6; inversion H6; subst.
    assert (forall V : TX, In V (fold_right (@app _) nil Bs) -> In V Ys) by 
      (intros; eapply H2; simpl; apply in_or_app; right; auto).
    apply P2'_if_P2 in H11;
    generalize (H _ Y _ (GJ_TE_Free_Vars_Wrap _ _ (TE_FV_GTy_ext _ te _ H11)) H3); 
      repeat (rewrite GJ_TE_Trans_invert; rewrite GJ_TE_rename_invert; simpl);
      repeat (rewrite GJ_TE_rename_invert; rewrite GJ_TE_Trans_invert; simpl); intros.
    apply GTy_ext_Wrap_inject in H4; injection H4; intros; subst;
      rewrite H5.
    rewrite H0 at 1; eauto.
    intros; eapply H2; simpl; apply in_or_app; auto.
  Qed.

  Definition FV_subst_tot_P ty := forall tys Vs Ys Xs,
    length Xs = length tys -> 
    List_P2' Free_Vars tys Vs -> 
    Free_Vars ty Ys -> 
    (forall V, In V Ys -> In V Xs) -> 
    exists Ys', Free_Vars (Ty_trans ty Xs tys) Ys' /\
      forall Y, In Y Ys' -> In Y (fold_right (@app _)  nil Vs).

  Definition FV_subst_tot_Q te := forall tys Vs Ys Xs,
    length Xs = length tys -> 
    List_P2' Free_Vars tys Vs -> 
    TE_Free_Vars te Ys -> 
    (forall V, In V Ys -> In V Xs) -> 
    exists Ys', TE_Free_Vars (TE_trans te Xs tys) Ys' /\
      forall Y, In Y Ys' -> In Y (fold_right (@app _)  nil Vs).

  Lemma GJ_FV_subst_tot : forall Y, FV_subst_tot_P (Ty_Wrap (TyVar Y)).
    unfold FV_subst_tot_P; repeat rewrite GJ_Ty_trans_invert; intros.
    apply GJ_Free_Vars_invert in H1; inversion H1; subst.
    apply GJ_Ty_Wrap_inject in H4; injection H4; intros; subst.
    simpl in H1; generalize tys Vs H H0 GJ_Ty_trans_invert (H2 _ (or_introl _ (refl_equal _))); clear.
    induction Xs; destruct tys; simpl; intros; try discriminate.
    contradiction.
    repeat rewrite GJ_Ty_trans_invert; destruct H1; subst; simpl.
    destruct (TX_eq_dec Y Y); subst; auto.
    inversion H0; subst.
    exists b; split; auto.
    simpl; intros; apply in_or_app; auto.
    elimtype False; congruence.
    destruct (TX_eq_dec a Y); subst; auto.
    inversion H0; subst.
    exists b; split; auto.
    simpl; intros; apply in_or_app; auto.
    inversion H0; subst.
    injection H; intros.
    destruct (IHXs _ _ H2 H6 GJ_Ty_trans_invert H1) as [Ys' [FV_t In_Y]].
    exists Ys'; split; auto.
    rewrite <- GJ_Ty_trans_invert; assumption.
    intros; simpl; apply in_or_app; right; auto.
  Qed.

   Lemma FJ_FV_subst_tot : forall te c, FV_subst_tot_Q te -> 
     FV_subst_tot_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold FV_subst_tot_P; unfold FV_subst_tot_Q; intros;
       repeat (rewrite FJ_Ty_trans_invert; rewrite FJ_Ty_rename_invert; simpl).
     apply FJ_Free_Vars_invert in H2; inversion H2; subst.
     apply FJ_Ty_Wrap_inject in H4; injection H4; intros; subst.
     destruct (H _ _ _ _ H0 H1 H5 H3) as [Ys' [FV_te In_Ys']].
     exists Ys'; split; auto.
     rewrite FJ_Ty_trans_invert; simpl; apply FJ_Free_Vars_Wrap; constructor; auto.
   Qed.

  Lemma FV_subst_tot_H3 : forall te tys Vs Ys Xs,
    length Xs = length tys -> 
    List_P2' Free_Vars tys Vs -> 
    GJ_TE_Free_Vars (nil, te) Ys -> 
    (forall V, In V Ys -> In V Xs) -> 
    exists Ys', GJ_TE_Free_Vars (GJ_TE_Trans (nil, te) Xs tys) Ys' /\
      forall Y, In Y Ys' -> In Y (fold_right (@app _)  nil Vs).
    intros.
    exists nil; split; simpl; auto; intros; try contradiction.
    unfold GJ_TE_Trans; simpl.
    eapply (TE_FV_GTy_ext nil te nil).
    apply P2'_if_P2; constructor.
  Qed.

  Lemma FV_subst_tot_H4 : forall ty tys te,
    FV_subst_tot_Q (GTy_ext_Wrap (tys, te)) -> 
    FV_subst_tot_P ty -> 
    forall tys' Vs Ys Xs, 
      length Xs = length tys' -> 
      List_P2' Free_Vars tys' Vs -> 
      GJ_TE_Free_Vars (ty :: tys, te) Ys -> 
      (forall V, In V Ys -> In V Xs) -> 
      exists Ys', GJ_TE_Free_Vars (GJ_TE_Trans (ty :: tys, te) Xs tys') Ys' /\
        forall Y, In Y Ys' -> In Y (fold_right (@app _)  nil Vs).
    unfold FV_subst_tot_P; unfold FV_subst_tot_Q; simpl; intros.
    unfold GJ_TE_Trans; simpl.
    inversion H3; apply P2_if_P2' in H8; inversion H8; subst.
    assert (forall V : TX, In V (fold_right (@app _) nil Bs) -> In V Xs) by 
      (intros; eapply H4; simpl; apply in_or_app; right; auto).
    assert (forall V, In V b -> In V Xs) by (intros; eapply H4; simpl; apply in_or_app; auto).
    apply P2'_if_P2 in H13;
      destruct (H _ _ _ _ H1 H2 (GJ_TE_Free_Vars_Wrap _ _ (TE_FV_GTy_ext _ te _ H13)) H5) as 
        [Ys' [FV_te In_Ys']]. 
    destruct (H0 _ _ _ _ H1 H2 H11 H6) as [Ys'' [FV_ty In_Ys'']].
    repeat (rewrite GJ_TE_Trans_invert in *|-*; rewrite GJ_TE_rename_invert in *|-*; simpl);
      repeat (rewrite GJ_TE_rename_invert in *|-*; rewrite GJ_TE_Trans_invert in *|-*; simpl).
    exists (Ys'' ++ Ys'); split; auto.
    rewrite (GJ_TE_Trans_invert) in FV_te; simpl in FV_te;
      apply GJ_TE_Free_Vars_invert in FV_te; inversion FV_te; subst.    
    eapply (TE_FV_GTy_ext _ _ (Ys'' :: txs)).
    apply P2_if_P2' in H12; inversion H12; subst;
      apply P2'_if_P2; econstructor; auto.
    constructor.
    constructor; auto.
    intros; apply in_app_or in H7; destruct H7; eauto.
  Qed.

  Definition Free_Vars_id_P ty := forall Us Us', Free_Vars ty Us -> Free_Vars ty Us' -> Us = Us'.
  
  Definition Free_Vars_id_Q te := forall Us Us', TE_Free_Vars te Us -> TE_Free_Vars te Us' -> Us = Us'.

  Lemma GJ_Free_Vars_id : forall Y, Free_Vars_id_P (Ty_Wrap (TyVar Y)).
    unfold Free_Vars_id_P; intros; apply GJ_Free_Vars_invert in H;
      apply GJ_Free_Vars_invert in H0; inversion H; inversion H0; subst.
    rewrite <- H2 in H4; apply GJ_Ty_Wrap_inject in H4; injection H4; congruence.
  Qed.

  Lemma FJ_Free_Vars_id : forall te c, Free_Vars_id_Q te -> 
     Free_Vars_id_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Free_Vars_id_P; unfold Free_Vars_id_Q; intros.
    apply FJ_Free_Vars_invert in H0; apply FJ_Free_Vars_invert in H1;
      inversion H0; inversion H1; subst; apply FJ_Ty_Wrap_inject in H2; 
        apply FJ_Ty_Wrap_inject in H5; injection H2; injection H5; intros; subst; 
          eauto.
  Qed.

  Lemma Free_Vars_id_H3 : forall te Us Us',
    GJ_TE_Free_Vars (nil, te) Us -> GJ_TE_Free_Vars (nil, te) Us' -> Us = Us'.
    intros; inversion H; inversion H0; subst.
    apply P2_if_P2' in H4; apply P2_if_P2' in H8; inversion H4; inversion H8; subst.
    reflexivity.
  Qed.

  Lemma Free_Vars_id_H4 : forall ty tys te,
    Free_Vars_id_Q (GTy_ext_Wrap (tys, te)) -> 
    Free_Vars_id_P ty -> 
    forall Us Us',
    GJ_TE_Free_Vars (ty :: tys, te) Us -> GJ_TE_Free_Vars (ty :: tys, te) Us' -> Us = Us'.
    unfold Free_Vars_id_Q; unfold Free_Vars_id_P; intros;
      inversion H1; inversion H2; subst.
    apply P2_if_P2' in H6; apply P2_if_P2' in H10; inversion H6; inversion H10; subst.
    rewrite (H0 _ _ H5 H12); apply P2'_if_P2 in H14; apply P2'_if_P2 in H8.
    simpl; rewrite (H _ _ (GJ_TE_Free_Vars_Wrap _ _ (TE_FV_GTy_ext _ te _ H8))
      (GJ_TE_Free_Vars_Wrap _ _ (TE_FV_GTy_ext _ te _ H14))).
    reflexivity.
  Qed.

  Variable (Ty_rename_eq_Ty_trans : forall ty, Ty_rename_eq_Ty_trans_P ty)
    (FV_subst_tot : forall ty, FV_subst_tot_P ty).

  Lemma All_In_map : forall A B (f g : A -> B) As,
    (forall n', nth_error (map f As) n' = nth_error (map g As) n') -> 
    map f As = map g As.
    clear; induction As; simpl; intros; auto.
    rewrite (IHAs).
    generalize (H 0); simpl; intros; injection H0; intros; congruence.
    intros; apply (H (S n')).
  Qed.

  Lemma exists_Free_Vars_P2 : forall tys, exists Vs', List_P2' Free_Vars tys Vs'.
    generalize exists_Free_Vars; clear; induction tys.
    exists nil; intros; constructor.
    intros; destruct (exists_Free_Vars a); destruct IHtys; eexists (_ :: _); constructor; eauto.
  Qed.

  Lemma Ty_rename_Ty_trans_tot' : forall ty Xs tys n Vs
    (len_Xs : length Xs = length tys),
    Free_Vars ty Vs -> 
    (forall V, In V Vs-> In V Xs) -> 
    Ty_rename (Ty_trans ty Xs tys) n =
    Ty_trans ty Xs (map (fun ty => Ty_rename ty n) tys).
    intros.
    destruct (exists_Free_Vars_P2 tys) as [Vs' FV_tys].
    destruct (FV_subst_tot ty tys Vs' Vs Xs) as [Ys' [FV_trans In_Ys'_Vs']]; auto.
    erewrite (Ty_rename_eq_Ty_trans _ _ n _ FV_trans); auto.
    erewrite (Ty_trans_trans_subst ty _ Xs _ tys _).
    generalize (nth_error_map _ _ (fun ty0 : Ty => Ty_rename ty0 n) tys); intros.
    generalize (nth_error_map _ _ (fun ty0 : Ty =>
        Ty_trans ty0 (fold_right (@app _) nil Vs')
        (map (fun V : TX => Ty_Wrap (TyVar (rename_X V n))) (fold_right (@app _) nil Vs'))) tys);
    intros.
    assert (forall n', 
       nth_error
         (map
            (fun ty0 : Ty =>
             Ty_trans ty0 (fold_right (@app _) nil Vs')
               (map (fun V : TX => Ty_Wrap (TyVar (rename_X V n)))
                 (fold_right (@app _) nil Vs'))) tys) n' = 
         nth_error (map (fun ty0 : Ty => Ty_rename ty0 n) tys) n').
    intros; caseEq (nth_error tys n').
    rewrite (H1 _ _ H3); rewrite (H2 _ _ H3).
    generalize FV_tys as FV_tys'; intros FV_tys'; 
      apply P2'_if_P2 in FV_tys'; destruct FV_tys' as [In_ty NIn_ty];
      destruct (In_ty _ _ H3) as [Bs [nth_Vs' FV_t]].
    rewrite (Ty_rename_eq_Ty_trans t Bs n (fold_right (@app _) nil Vs')); auto.
    generalize Vs' nth_Vs'; clear; induction n'; simpl; destruct Vs'; intros;
      try discriminate;
    simpl; apply in_or_app; first [left; injection nth_Vs'; intros; subst; auto; fail |
      right; eauto].
    repeat rewrite (nth_error_map' _ _ _ _ _ H3); reflexivity.
    rewrite (All_In_map _ _ _ _ _ H3).
    reflexivity.
    auto.
    eassumption.
    eassumption.
  Qed.
  
  Definition Ty_rename_GJ_Ty_Wrap_eq_P T' := forall T n,
    Ty_Wrap T = Ty_rename T' n -> 
    exists Y, T' = TyVar Y.

  Definition Ty_rename_FJ_Ty_Wrap_eq_P T := forall c n te,
    FJ_Ty_Wrap (ty_def _ _ te c) = Ty_rename T n -> 
    exists te', TE_rename te' n = te /\ T = FJ_Ty_Wrap (ty_def _ _ te' c).

  Definition Ty_rename_inject_P ty := forall ty' n, Ty_rename ty n = Ty_rename ty' n-> 
    ty = ty'.

  Definition Ty_rename_inject_Q te := forall te' n, TE_rename te n = TE_rename te' n-> 
    te = te'.

  Variable (Ty_rename_GJ_Ty_Wrap_eq : forall ty', Ty_rename_GJ_Ty_Wrap_eq_P ty')
    (Ty_rename_FJ_Ty_Wrap_eq : forall ty', Ty_rename_FJ_Ty_Wrap_eq_P ty').

  Lemma GJ_Ty_rename_inject : forall Y, Ty_rename_inject_P (Ty_Wrap (TyVar Y)).
    unfold Ty_rename_inject_P; intros; rewrite GJ_Ty_rename_invert in H;
      simpl in H.
    destruct (Ty_rename_GJ_Ty_Wrap_eq _ _ _ H); subst.
    rewrite GJ_Ty_rename_invert in H; simpl in H.
    apply GJ_Ty_Wrap_inject in H; injection H; intros.
    rewrite (rename_X_inject _ _ _ H0); reflexivity.
   Qed.

   Lemma FJ_Ty_rename_inject : forall te c, Ty_rename_inject_Q te -> 
     Ty_rename_inject_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold Ty_rename_inject_P; unfold Ty_rename_inject_Q; intros;
       repeat (rewrite FJ_Ty_rename_invert in H0; simpl in H0).
     destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H0) as [te' [te'_eq H2]].
     subst.
     erewrite (H te' n); auto.
   Qed.

  Lemma Ty_rename_inject_H3 : forall te te' Y, 
    GJ_TE_rename (nil, te) Y = GJ_TE_rename te' Y -> (nil (A:= Ty), te) = te'.
    intros; destruct te'; destruct l.
    simpl in H; injection H; intros; subst; reflexivity.
    simpl in H; discriminate.
  Qed.
  
  Lemma Ty_rename_inject_H4 : forall ty tys te, 
    Ty_rename_inject_Q (GTy_ext_Wrap (tys, te)) -> 
    Ty_rename_inject_P ty -> 
    forall te' Y,
      GJ_TE_rename (ty :: tys, te) Y = GJ_TE_rename te' Y -> 
      (ty :: tys, te) = te'.
    unfold Ty_rename_inject_P; unfold Ty_rename_inject_Q; simpl; intros.
    destruct te'; simpl in H1; destruct l; try discriminate; injection H1; simpl; intros; subst.
    rewrite (H0 _ _ H4); generalize (H (GTy_ext_Wrap (l, t)) Y).
    intros H2; repeat rewrite GJ_TE_rename_invert in H2; simpl in H2; 
      injection H1; intros; rewrite H5 in H2.
    generalize (GTy_ext_Wrap_inject _ _ (H2 (refl_equal _))); intros te_eq_te'; 
      injection te_eq_te'; intros; subst; reflexivity.
  Qed.  

  Variable (Ty_rename_inject : forall ty, Ty_rename_inject_P ty).

  Lemma Ty_rename_Ty_trans_tot : forall typs tys tys' n Vs',
    List_P2' Free_Vars tys' Vs' ->
    length typs = length tys -> 
    (forall V, In V (fold_right (@app _) nil Vs') -> In V (Extract_TyVar typs)) ->
    map (fun ty : Ty => Ty_rename ty n) (Tys_Trans typs tys tys') =
    Tys_Trans typs (map (fun ty => Ty_rename ty n) tys) tys'.
    intros;
    assert (map (fun ty : Ty => Ty_rename ty n) (Tys_Trans typs tys tys') = 
       map (fun ty : Ty => Ty_rename (Ty_trans ty (Extract_TyVar typs) tys) n) tys') as H2 by 
    (clear H; generalize typs tys; induction tys'; simpl; intros;
      first [reflexivity | rewrite IHtys'; reflexivity]); rewrite H2; clear H2.
    apply All_In_map; intros.
    generalize (nth_error_map _ _ (fun ty : Ty => Ty_rename (Ty_trans ty (Extract_TyVar typs) tys) n)
      tys'); intros.
    generalize (nth_error_map _ _ (fun ty' : Ty =>
      Ty_trans ty' (Extract_TyVar typs)
      (map (fun ty : Ty => Ty_rename ty n) tys)) tys'); intros.
    caseEq (nth_error tys' n').
    rewrite (H2 _ _ H4); rewrite (H3 _ _ H4).
    apply P2'_if_P2 in H; destruct H.
    destruct (H _ _ H4) as [Bs [nth_Vs' FV_t]].
    rewrite (Ty_rename_Ty_trans_tot' _ _ _ _ Bs).
    reflexivity.
    generalize tys H0; clear; induction typs; destruct tys; simpl; intros; 
      try discriminate; auto.
    assumption.
    intros; apply H1.
    generalize Bs Vs' nth_Vs' H6; clear; induction n'; destruct Vs'; simpl; intros;
      try discriminate.
    injection nth_Vs'; intros; injection H; intros; subst; simpl; apply in_or_app; auto.
    apply in_or_app; right; eauto.
    repeat rewrite nth_error_map'; auto.
  Qed.

  Lemma GJ_rename_build_te {build_te' L_WF_Ext' } :
    forall gamma ce c te te'' te' n ce',
    GJ_definitions.L_build_context L_build_context' ce gamma -> 
    GJ_definitions.L_WF_Ext L_WF_Ext' gamma ce c -> 
    @GJ_wf_class_ext cld_def_ext _ gamma ce' te' -> 
    @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te'' ->
    @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' (GJ_TE_rename te'' n).
    intros; inversion H2; subst.
    unfold GJ_TE_rename.
    destruct (exists_Free_Vars_P2 tys') as [Vs FV_tys'].
    destruct (GJ_L_WF_bound _ _ _ _ H H0) as [Ys' [FV_tys In_Ys_tys]].
    erewrite Ty_rename_Ty_trans_tot; eauto.
    constructor; auto.
    rewrite len_map; assumption.
    intros.
    inversion H1; subst.
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
    
  Lemma GJ_rename_build_te_obj {build_te' L_WF_Ext' } :
    forall gamma ce c te te'' te' n, 
      GJ_definitions.L_build_context L_build_context' ce gamma -> 
      GJ_definitions.L_WF_Ext L_WF_Ext' gamma ce c -> 
      GJ_wf_object_ext gamma te' -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te'' ->
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' (GJ_TE_rename te'' n).
    intros; inversion H1; subst.
    inversion H2; subst; simpl.
    constructor; auto.
    rewrite len_map; assumption.
  Qed.
      
  Variable 
  (rename_build_te : 
    forall gamma ce c te te'' te' n cld', 
      L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
      wf_class_ext' gamma cld' te' ->
      build_te ce te te' te'' ->
      build_te ce (TE_rename te n) te' (TE_rename te'' n))
  (rename_build_te_obj : 
    forall gamma ce c te te'' te' n, 
      L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
      wf_object_ext' gamma te' ->
      build_te ce te te' te'' ->
      build_te ce (TE_rename te n) te' (TE_rename te'' n))
  (Ty_rename_eq_inject : forall ty ty' n, Ty_rename ty n = Ty_rename ty' n -> ty = ty').
  
  Lemma FJ_Ty_rename_subtype (rename_rect : forall delta S T sub_S_T, Ty_rename_subtype_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Ty_rename_subtype_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Ty_rename_subtype_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap. 
    repeat rewrite FJ_Ty_rename_invert; simpl; econstructor 3; eauto.
    generalize (WF_CT _ _ CT_c); intros WF_c; inversion WF_c; subst.
    apply FJ_WF_Type_Wrap_invert in H13; inversion H13; subst;
      apply FJ_Ty_Wrap_inject in H; injection H; intros; subst.
    eapply rename_build_te_obj; eauto.
    eapply rename_build_te; eauto.
    apply rename_rect.
  Defined.
    
  Lemma GJ_Ty_rename_subtype : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Ty_rename_subtype_P _ _ _ sub_S_T.
    unfold Ty_rename_subtype_P; intros; apply subtype_Wrap.
    inversion sub_S_T; subst; rewrite GJ_Ty_rename_invert; simpl. 
    rewrite Ty_rename_eq_NTy_rename.
    constructor.
    eauto.
  Qed.

  Lemma FJ_Ty_rename_FJ_Ty_Wrap_eq : forall te c, 
    Ty_rename_FJ_Ty_Wrap_eq_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_rename_FJ_Ty_Wrap_eq_P; intros.
    rewrite FJ_Ty_rename_invert in H; simpl in H.
    apply FJ_Ty_Wrap_inject in H; injection H; intros; subst.
    clear; eexists _; split; eauto.
  Qed.

  Lemma GJ_Ty_rename_FJ_Ty_Wrap_eq: forall X,
    Ty_rename_FJ_Ty_Wrap_eq_P (TyVar X).
    unfold Ty_rename_FJ_Ty_Wrap_eq_P; intros.
    rewrite GJ_Ty_rename_invert in H; simpl in H.
    elimtype False; apply (Ty_Wrap_discriminate _ _ H).
  Qed.
  
  Lemma FJ_Ty_rename_GJ_Ty_Wrap_eq : forall te c, 
    Ty_rename_GJ_Ty_Wrap_eq_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_rename_GJ_Ty_Wrap_eq_P; intros.
    rewrite FJ_Ty_rename_invert in H; simpl in H.
    elimtype False; apply (Ty_Wrap_discriminate _ _ (sym_eq H)).
  Qed.

  Lemma GJ_Ty_rename_GJ_Ty_Wrap_eq: forall X,
    Ty_rename_GJ_Ty_Wrap_eq_P (TyVar X).
    unfold Ty_rename_GJ_Ty_Wrap_eq_P; intros.
    rewrite GJ_Ty_rename_invert in H; simpl in H.
    destruct T.
    eexists _; reflexivity.
  Qed.

  Lemma GJ_TE_rename_build_te {L_WF_Ext' build_te'} : 
    forall gamma ce c te te' te'' n ce',
      GJ_definitions.L_build_context L_build_context' ce gamma -> 
      GJ_definitions.L_WF_Ext L_WF_Ext' gamma ce c -> 
      @GJ_wf_class_ext cld_def_ext _ gamma ce' te' -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' te'' -> 
      exists te3, te'' = GJ_TE_rename te3 n.
    intros; inversion H2; subst.
    unfold GJ_TE_rename.
    destruct (exists_Free_Vars_P2 tys') as [Vs FV_tys'].
    destruct (GJ_L_WF_bound _ _ _ _ H H0) as [Ys' [FV_tys In_Ys_tys]].
    destruct te; unfold GJ_TE_rename in H3; injection H3; intros; subst.
    eexists (Tys_Trans typs l tys', _); 
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

  Variable 
    (TE_rename_build_te : 
      forall gamma ce c te te' te'' n cld',
        L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
        wf_class_ext' gamma cld' te' -> 
        build_te ce (TE_rename te n) te' te'' -> 
        exists te3, te'' = TE_rename te3 n)
    (TE_rename_build_obj_te : 
      forall gamma ce te te' te'' n,
        wf_object_ext' gamma te' -> 
        build_te ce  (TE_rename te n) te' te'' -> 
        exists te3, te'' = TE_rename te3 n)
    (TE_rename_build_te' : forall gamma ce c te te' te'' n cld',
        L_build_context ce gamma -> L_WF_Ext gamma ce c -> 
        wf_class_ext' gamma cld' te' -> 
        build_te ce  
        (TE_rename te n) te' (TE_rename te'' n) ->
        build_te ce  te te' te'')
    (TE_rename_build_obj_te' : forall gamma ce te te' te'' n,
      wf_object_ext' gamma te' -> 
      build_te ce  
      (TE_rename te n) te' (TE_rename te'' n) ->
      build_te ce te te' te'').

  Lemma GJ_TE_rename_build_te' {L_WF_Ext' build_te'} : 
    forall gamma ce c te te' te'' n ce',
      GJ_definitions.L_build_context L_build_context' ce gamma -> 
      GJ_definitions.L_WF_Ext L_WF_Ext' gamma ce c -> 
      @GJ_wf_class_ext cld_def_ext _ gamma ce' te' -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' (GJ_TE_rename te'' n) -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te''.
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

  Lemma GJ_TE_rename_build_obj_te {build_te'} : 
    forall gamma ce te te' te'' n,
      GJ_wf_object_ext gamma te' -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' te'' ->
      exists te3, te'' = GJ_TE_rename te3 n.
    intros; inversion H; subst.
    inversion H0; subst; simpl.
    eexists (nil, _); simpl; reflexivity.
  Qed.

  Lemma GJ_TE_rename_build_obj_te' {build_te'} : 
    forall gamma ce te te' te'' n,
      GJ_wf_object_ext gamma te' -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce (GJ_TE_rename te n) te' (GJ_TE_rename te'' n) -> 
      @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te''.
    intros; inversion H; subst.
    inversion H0; subst; simpl.
    destruct te; destruct te''; simpl in H1, H5.
    injection H1; intros; subst; injection H5; intros; subst.
    destruct l0.
    econstructor; auto.
    rewrite len_map in H7; assumption.
    simpl in H3; discriminate.
  Qed.

  Definition ex_Ty_rename_subtype_P_r gamma S T (sub_S_T : subtype gamma S T) :=
    forall gamma' n S', gamma = rename_context gamma' n -> 
      S = Ty_rename S' n -> exists T', T = Ty_rename T' n.

  Definition ex_Ty_rename_subtype_P_l gamma S T (sub_S_T : subtype gamma S T) :=
    forall gamma' n T', gamma = rename_context gamma' n -> 
      T = Ty_rename T' n -> exists S', S = Ty_rename S' n.

  Lemma FJ_ex_Ty_rename_subtype_P_r
    (rename_rect : forall delta S T sub_S_T, ex_Ty_rename_subtype_P_r delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
      ex_Ty_rename_subtype_P_r delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold ex_Ty_rename_subtype_P_r; 
      first [assumption | clear rename_rect]; intros; subst. 
    exists S'; reflexivity.
    destruct (H _ _ _ (refl_equal _) (refl_equal _)); eapply H0; eauto.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H0) as [te3 [te_eq S'_eq]]; subst.
    generalize (WF_CT _ _ CT_c); intros H; inversion H; subst.
    apply FJ_WF_Type_Wrap_invert in H15; inversion H15; subst;
      apply FJ_Ty_Wrap_inject in H1; injection H1; intros; subst.
    destruct (TE_rename_build_obj_te _ _ _ _ _ _ H3 bld_te); subst.
    exists (FJ_Ty_Wrap (ty_def C ty_ext x (Object C)));
      rewrite FJ_Ty_rename_invert; simpl; reflexivity.
    destruct (TE_rename_build_te _ _ _ _ _ _ _ _ H8 H16 H4 bld_te).
    subst; eexists (FJ_Ty_Wrap (ty_def C ty_ext x _));
      rewrite FJ_Ty_rename_invert; simpl; reflexivity.
  Defined.
    
  Lemma GJ_ex_Ty_rename_subtype_P_r : forall delta S T (sub_S_T : GJ_subtype delta S T),
    ex_Ty_rename_subtype_P_r delta S T sub_S_T.
    unfold ex_Ty_rename_subtype_P_r; intros; inversion sub_S_T; subst.
    destruct (TLookup_rename_context' _ _ _ _ H1) as [x' [ty' [eq_x' [eq_ty' Lookup_x']]]].
    exists ty'; rewrite Ty_rename_eq_NTy_rename; rewrite eq_ty'; reflexivity.
  Qed.

  Variable (ex_Ty_rename_subtype : forall delta S T sub_S_T,
    ex_Ty_rename_subtype_P_r delta S T sub_S_T).

  Definition Ty_rename_subtype_P' gamma S T (sub_S_T : subtype gamma S T) :=
    forall gamma' n S' T', gamma = rename_context gamma' n -> 
      S = Ty_rename S' n -> T = Ty_rename T' n -> subtype gamma' S' T'.

  Lemma FJ_Ty_rename_subtype' (rename_rect : forall delta S T sub_S_T, Ty_rename_subtype_P' delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
      Ty_rename_subtype_P' delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Ty_rename_subtype_P'; 
      first [assumption | clear rename_rect]; intros; subst; eapply FJ_subtype_Wrap.
    rewrite (Ty_rename_eq_inject _ _ _ H1); constructor.
    destruct (ex_Ty_rename_subtype _ _ _ sub_c _ _ _ (refl_equal _) (refl_equal _));
      subst.
    econstructor 2.
    eapply H; eauto.
    eapply H0; eauto.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H0) as [te3 [eq_te3 eq_S']].
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H1) as [te4 [eq_te4 eq_T']]; subst.
    econstructor 3; try eassumption.
    generalize (WF_CT _ _ CT_c); intros H2; inversion H2; subst;
      apply FJ_WF_Type_Wrap_invert in H16; inversion H16; subst.
    eapply TE_rename_build_obj_te'; auto.
    apply FJ_Ty_Wrap_inject in H; injection H; intros; subst; eassumption.
    eassumption.
    eapply TE_rename_build_te'; auto; try eassumption.
    apply FJ_Ty_Wrap_inject in H; injection H; intros; subst; eassumption.
  Defined.
    
  Lemma GJ_Ty_rename_subtype' : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Ty_rename_subtype_P' _ _ _ sub_S_T.
    unfold Ty_rename_subtype_P'; intros; apply subtype_Wrap.
    inversion sub_S_T; subst.
    destruct (TLookup_rename_context' _ _ _ _ H2) as [x' [ty' [eq_x' [eq_ty' Lookup_x']]]];
      subst.
    rewrite <- Ty_rename_eq_NTy_rename in H5; apply Ty_rename_eq_inject in H5; subst.
    destruct (Ty_rename_GJ_Ty_Wrap_eq _ _ _ H4) as [X' eq_X']; subst.
    rewrite GJ_Ty_rename_invert in H4; simpl in H4; apply GJ_Ty_Wrap_inject in H4; 
      injection H4; intros; subst; apply rename_X_inject in H; subst.
    constructor; auto.
  Qed.

  Variable (Ty_rename_subtype : forall delta S T sub_S_T, Ty_rename_subtype_P delta S T sub_S_T)
    (Ty_rename_subtype' : forall delta S T sub_S_T, Ty_rename_subtype_P' delta S T sub_S_T).

  Definition Ty_rename_WF_Type_P gamma ty (WF_ty : WF_Type gamma ty) :=
    forall n, WF_Type (rename_context gamma n) (Ty_rename ty n).

  Definition Ty_rename_WF_Type_Q gamma cld te (WF_te : wf_class_ext' gamma cld te) :=
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (cld_typs cld) Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar (cld_typs cld)))
    n, wf_class_ext' (rename_context gamma n) cld (TE_rename te n).

  Definition Ty_rename_WF_Type_P1 gamma tys (WF_tys : List_P1 (WF_Type gamma) tys) :=
    forall n, List_P1 (WF_Type (rename_context gamma n)) (map (fun ty => Ty_rename ty n) tys).

  Variable (Ty_rename_WF_object : forall gamma te n, wf_object_ext' gamma te ->
    wf_object_ext' (rename_context gamma n) (TE_rename te n))
  (Free_Vars_id : forall ty Us Us', Free_Vars ty Us -> Free_Vars ty Us' -> Us = Us').
  
  Lemma GJ_Ty_rename_WF_object :  forall gamma te n, GJ_wf_object_ext gamma te ->
    GJ_wf_object_ext (rename_context gamma n) (GJ_TE_rename te n).
    intros; inversion H; subst; simpl; constructor.
  Qed.

  Lemma FJ_Ty_rename_WF_Type_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Ty_rename_WF_Type_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Ty_rename_WF_Type_P; intros.
    rewrite (FJ_Ty_rename_invert); simpl; apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma FJ_Ty_rename_WF_Type_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Ty_rename_WF_Type_Q _ _ _ wf_cld_ext ->
    Ty_rename_WF_Type_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Ty_rename_WF_Type_P; unfold Ty_rename_WF_Type_Q; intros.
    destruct (L_WF_bound _ (WF_CT _ _ CT_c)) as [Ys [Free_Ys Bound_Ys]].
    rewrite (FJ_Ty_rename_invert); simpl; apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma Ty_rename_WF_Type_ext_H1 : forall gamma (ce : cld_def_ext) tys typs te P1
    (len : length typs = length tys)
    (P2 : List_P2 tys (map
      (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar typs) tys) typs) (subtype gamma)),
    Ty_rename_WF_Type_P1 gamma tys P1-> 
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar typs))
      n, GJ_wf_class_ext (rename_context gamma n) 
      (typs, ce) (GJ_TE_rename (tys,te) n).
    intros; constructor.
    eapply H.
    rewrite len_map; assumption.
    destruct P2; split; intros.
    caseEq (nth_error tys n0).
    generalize (nth_error_map _ _ (fun ty : Ty => Ty_rename ty n) _ _ _ H3); intros H3';
      rewrite H3' in H2; injection H2; intros; subst; clear H2.
    destruct (H0 _ _ H3) as [ty' [nth_ty' sub_t_ty']].
    caseEq (nth_error typs n0).
    generalize (nth_error_map _ _ (fun typ' : GTy * N =>
      Ty_trans (snd typ') (Extract_TyVar typs) tys) _ _ _ H2); intros nth_ty'';
      rewrite nth_ty'' in nth_ty'; injection nth_ty'; intros; subst; clear nth_ty'.
    exists (Ty_rename (Ty_trans (snd p) (Extract_TyVar typs) tys) n); split.
    rewrite (nth_error_map _ _ (fun typ' : GTy * N =>
      Ty_trans (snd typ') (Extract_TyVar typs)
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

  Lemma Ty_rename_WF_Type_ext_H2 : forall gamma, 
    Ty_rename_WF_Type_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Ty_rename_WF_Type_P1; intros; constructor.
  Qed.
    
  Lemma Ty_rename_WF_Type_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Ty_rename_WF_Type_P _ _ P_ty -> Ty_rename_WF_Type_P1 _ tys P_tys -> 
    Ty_rename_WF_Type_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Ty_rename_WF_Type_P; unfold Ty_rename_WF_Type_P1; intros.
    constructor.
    eapply H.
    eapply H0.
  Qed.

  Lemma GJ_Ty_rename_WF_Type : forall delta S (WF_S : GJ_WF_Type delta S), 
    Ty_rename_WF_Type_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Ty_rename_WF_Type_P; intros; inversion WF_S; subst.
    rewrite GJ_Ty_rename_invert; simpl.
    eapply GJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Definition Ty_rename_WF_Type'_P gamma ty (WF_ty : WF_Type gamma ty) :=
    forall gamma' n ty', gamma = rename_context gamma' n -> 
      ty = Ty_rename ty' n -> WF_Type gamma' ty'.

  Definition Ty_rename_WF_Type'_Q gamma cld te (WF_te : wf_class_ext' gamma cld te) :=
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) (cld_typs cld) Ys) 
    (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar (cld_typs cld)))
    gamma' te' n, gamma = rename_context gamma' n -> te = TE_rename te' n ->
    wf_class_ext' gamma' cld te'.

  Definition Ty_rename_WF_Type'_P1 gamma tys (WF_tys : List_P1 (WF_Type gamma) tys) :=
    forall n gamma' tys', 
      gamma = rename_context gamma' n -> tys = map (fun ty => Ty_rename ty n) tys' ->
      List_P1 (WF_Type gamma') tys'.

  Variable (Ty_rename_WF_object' : forall gamma te n,
    wf_object_ext' (rename_context gamma n) (TE_rename te n) ->  wf_object_ext' gamma te).
  
  Lemma GJ_Ty_rename_WF_object' :  forall gamma te n, 
    GJ_wf_object_ext (rename_context gamma n) (GJ_TE_rename te n) ->
    GJ_wf_object_ext gamma te.
    intros; inversion H; subst; simpl.
    destruct te; simpl in H2; injection H2; intros.
    destruct l; simpl in H1; first [discriminate | constructor].
  Qed.

  Lemma FJ_Ty_rename_WF_Type'_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Ty_rename_WF_Type'_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Ty_rename_WF_Type'_P; intros.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H0) as [te' [te'_eq ty'_eq]]; subst.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma FJ_Ty_rename_WF_Type'_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Ty_rename_WF_Type'_Q _ _ _ wf_cld_ext ->
    Ty_rename_WF_Type'_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Ty_rename_WF_Type'_P; unfold Ty_rename_WF_Type'_Q; intros.
    destruct (Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ H1) as [te' [te'_eq ty'_eq]]; subst.
    destruct (L_WF_bound _ (WF_CT _ _ CT_c)) as [Ys [Free_Ys Bound_Ys]].
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma Ty_rename_WF_Type_ext'_H1 : forall gamma (ce : cld_def_ext) tys typs te P1
    (len : length typs = length tys)
    (P2 : List_P2 tys (map
      (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar typs) tys) typs) (subtype gamma)),
    Ty_rename_WF_Type'_P1 gamma tys P1-> 
    forall Ys (FV_typs : List_P2' (fun (typ : GTy * N) => Free_Vars (snd typ)) typs Ys) 
      (Bound_Ys : forall Y, In Y (fold_right (@app _) nil Ys) -> In Y (Extract_TyVar typs))
      gamma' te' n, gamma = rename_context gamma' n -> (tys, te) = GJ_TE_rename te' n ->
      GJ_wf_class_ext gamma' (typs, ce) te'.
    unfold Ty_rename_WF_Type'_P1; intros; destruct te' as [tys' te']; simpl in H1; 
      injection H1; intros; subst.
    constructor.
    eapply H; auto.
    rewrite len_map in len; assumption.
    destruct P2; split; intros.
    generalize (nth_error_map _ _ (fun ty : Ty => Ty_rename ty n) _ _ _ H3); intros H3'.
    destruct (H0 _ _ H3') as [ty' [nth_ty' sub_t_ty']].
    caseEq (nth_error typs n0).
    generalize (nth_error_map _ _ (fun typ' : GTy * N =>
                  Ty_trans (snd typ') (Extract_TyVar typs)
                    (map (fun ty : Ty => Ty_rename ty n) tys')) _ _ _ H4); intros nth_ty'';
      rewrite nth_ty'' in nth_ty'; injection nth_ty'; intros; subst; clear nth_ty'.
    exists (Ty_trans (snd p) (Extract_TyVar typs) tys'); split.
    rewrite (nth_error_map _ _ (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys') _ _ _ H4).
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
    reflexivity.
  Qed.

  Lemma Ty_rename_WF_Type_ext'_H2 : forall gamma, 
    Ty_rename_WF_Type'_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Ty_rename_WF_Type'_P1; intros. 
    destruct tys'; first [simpl in H0; discriminate | constructor].
  Qed.
    
  Lemma Ty_rename_WF_Type_ext'_H3 : forall gamma ty tys P_ty P_tys, 
    Ty_rename_WF_Type'_P _ _ P_ty -> Ty_rename_WF_Type'_P1 _ tys P_tys -> 
    Ty_rename_WF_Type'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Ty_rename_WF_Type'_P; unfold Ty_rename_WF_Type'_P1; intros.
    destruct tys'; simpl in H2; first [discriminate | injection H2; intros; subst].
    constructor.
    eapply H; reflexivity.
    eapply H0; reflexivity.
  Qed.

  Lemma GJ_Ty_rename_WF_Type' : forall delta S (WF_S : GJ_WF_Type delta S), 
    Ty_rename_WF_Type'_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Ty_rename_WF_Type'_P; intros; inversion WF_S; subst.
    destruct (Ty_rename_GJ_Ty_Wrap_eq _ _ _ H3) as [X' eq_X']; subst.
    destruct (TLookup_rename_context' _ _ _ _ H1) as [x' [ty' [eq_x' [eq_ty' Lookup_x']]]];
      subst.
    rewrite GJ_Ty_rename_invert in H3; simpl in H3; apply GJ_Ty_Wrap_inject in H3; 
      injection H3; intros; subst; apply rename_X_inject in H; subst.
    apply GJ_WF_Type_Wrap; econstructor; eassumption.
  Qed.

  Definition subtype_context_shuffle_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      subtype (app_context delta_2 delta_1) S T.

  Lemma FJ_subtype_context_shuffle 
    (shuffle_rect : forall delta S T sub_S_T, subtype_context_shuffle_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    subtype_context_shuffle_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold subtype_context_shuffle_P.
    intros; subst; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor 2.
    intros; apply (H _ _ H1 H2).
    intros; apply (H0 _ _ H1 H2).
    intros; eapply FJ_subtype_Wrap; econstructor 3; eassumption.
    assumption.
  Defined.
    
  Lemma GJ_subtype_context_shuffle : forall delta S T (sub_S_T : GJ_subtype delta S T),
    subtype_context_shuffle_P _ _ _ sub_S_T.
    unfold subtype_context_shuffle_P; intros; inversion sub_S_T; subst; apply subtype_Wrap.
    constructor.
    destruct (TLookup_dec delta_1 x) as [[ty' TLookup_ty'] | NTLookup].
    eapply TLookup_app'.
    eauto.
    rewrite (TLookup_unique _ _ _ ty' H1); auto.
    apply TLookup_app.
    eapply TLookup_app''; eassumption.
  Defined.

  Variable (subtype_context_shuffle : forall delta S T sub_S_T,
    subtype_context_shuffle_P delta S T sub_S_T).

  Definition WF_context_shuffle_P gamma S (wf_S : WF_Type gamma S) :=
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      WF_Type (app_context delta_2 delta_1) S.

  Definition WF_context_shuffle_Q gamma cld te (WF_te : wf_class_ext' gamma cld te) :=
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      wf_class_ext' (app_context delta_2 delta_1) cld te.

  Definition WF_context_shuffle_P1 gamma tys (WF_tys : List_P1 (WF_Type gamma) tys) :=
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      List_P1 (WF_Type (app_context delta_2 delta_1)) tys.

  Variable (WF_context_shuffle_obj_ext : forall delta_1 delta_2 te, 
    wf_object_ext' (app_context delta_1 delta_2) te ->
    wf_object_ext' (app_context delta_2 delta_1) te).
  
  Lemma GJ_WF_context_shuffle_obj_ext : forall delta_1 delta_2 te, 
    @GJ_wf_object_ext ty_def_ext (app_context delta_1 delta_2) te ->
    GJ_wf_object_ext (app_context delta_2 delta_1) te.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_WF_context_shuffle_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    WF_context_shuffle_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold WF_context_shuffle_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; subst; eauto.
  Qed.

  Lemma FJ_WF_context_shuffle_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    WF_context_shuffle_Q _ _ _ wf_cld_ext ->
    WF_context_shuffle_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold WF_context_shuffle_P; unfold WF_context_shuffle_Q; intros; subst.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.

  Lemma WF_context_shuffle_ext_H1 : forall gamma (ce : cld_def_ext) tys typs 
    (te : ty_def_ext) P1
    (len : length typs = length tys)
    (P2 : List_P2 tys (map
      (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar typs) tys) typs) (subtype gamma)),
    WF_context_shuffle_P1 gamma tys P1-> 
    forall delta_1 delta_2, gamma = app_context delta_1 delta_2 -> 
      (forall X ty, TLookup delta_1 X ty -> forall ty', ~ TLookup delta_2 X ty') -> 
      GJ_wf_class_ext (app_context delta_2 delta_1) 
      (typs, ce) (tys, te).
    unfold WF_context_shuffle_P1; intros; subst.
    constructor; eauto.
    destruct P2; split; intros.
    destruct (H0 _ _ H3) as [b [nth_b sub_a_b]]; exists b; split; eauto.
    eapply subtype_context_shuffle; eauto.
    eauto.
  Qed.

  Lemma WF_context_shuffle_ext_H2 : forall gamma, 
    WF_context_shuffle_P1 gamma _ (Nil (WF_Type gamma)).
    unfold WF_context_shuffle_P1; intros; constructor.
  Qed.
    
  Lemma WF_context_shuffle_ext_H3 : forall gamma ty tys P_ty P_tys, 
    WF_context_shuffle_P _ _ P_ty -> WF_context_shuffle_P1 _ tys P_tys -> 
    WF_context_shuffle_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold WF_context_shuffle_P; unfold WF_context_shuffle_P1; intros.
    constructor; subst.
    eapply H; eauto.
    eapply H0; eauto.
  Qed.

  Lemma GJ_WF_context_shuffle : forall delta S (WF_S : GJ_WF_Type delta S), 
    WF_context_shuffle_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold WF_context_shuffle_P; intros; inversion WF_S; subst.
    destruct (TLookup_dec delta_1 tx) as [[ty' TLookup_ty'] | NTLookup].
    eapply GJ_WF_Type_Wrap; econstructor.
    eapply TLookup_app'.
    eauto.
    eapply TLookup_ty'.
    eapply GJ_WF_Type_Wrap; econstructor.
    apply TLookup_app.
    eapply TLookup_app''; eassumption.
  Qed.

   Definition Type_Subst_Sub_2_5_P' gamma S T (sub_S_T : subtype gamma S T) :=
     forall (delta_1 : Context) (Xs : list _)
     (Ns : list N) (Us : list Ty) (XNs : TyP_List),
     length Xs = length Us -> 
     zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
     gamma = (update_Tlist Empty XNs) -> 
     List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) -> 
     List_P1 (WF_Type delta_1) Us -> 
     List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
     subtype (app_context delta_1 (subst_context Empty Xs Us)) 
     (Ty_trans S Xs Us) (Ty_trans T Xs Us).

  Lemma FJ_Type_Subst_Sub_2_5' 
    (subtype_rect : forall delta S T sub_S_T, Type_Subst_Sub_2_5_P' delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Type_Subst_Sub_2_5_P' delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; try assumption; clear subtype_rect;
      unfold Type_Subst_Sub_2_5_P'; intros; subst.
    eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor 2; eauto.
    repeat rewrite FJ_Ty_trans_invert; simpl.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    destruct (exists_Free_Vars (FJ_Ty_Wrap (ty_def C ty_ext te'' d))).
    generalize (WF_CT _ _ CT_c) as WF_d; intros.
    inversion WF_d; subst.
    apply FJ_WF_Type_Wrap_invert in H19; inversion H19; subst;
      apply FJ_Ty_Wrap_inject in H5; injection H5; intros; subst.
    eapply (Type_Subst_Sub_2_5_TE' ce); try eassumption.
    generalize H2 Ty_trans_eq_NTy_trans;
      clear; intros H'; destruct H'; split; intros.
    destruct (H _ _ H1) as [b [Nth_b sub_a_b]].
    exists b; rewrite Ty_trans_eq_NTy_trans; split; auto.
    eauto.
    eapply (Type_Subst_Sub_2_5_TE ce); try eassumption.
    generalize H2 Ty_trans_eq_NTy_trans;
      clear; intros H; destruct H; split; intros.
    destruct (H _ _ H1) as [b [Nth_b sub_a_b]].
    exists b; rewrite Ty_trans_eq_NTy_trans; split; auto.
    eauto.
  Defined.
    
   Variable (subst_context_Empty : forall Xs Us, subst_context Empty Xs Us = Empty)
     (app_context_Empty : forall gamma, app_context gamma Empty = gamma)
     (Finite_Context : forall gamma, exists n, forall X ty ty' Ys, TLookup gamma X ty ->
       Free_Vars (Ty_rename ty' n) Ys -> ~ In X Ys).

  Lemma GJ_Type_Subst_Sub_2_5' : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Type_Subst_Sub_2_5_P' _ _ _ sub_S_T.
    unfold Type_Subst_Sub_2_5_P'; intros; rewrite subst_context_Empty; rewrite app_context_Empty.
    destruct (Finite_Context delta) as [n NIn_n_delta].
    inversion sub_S_T; subst.
    assert (exists n, nth_error Xs n = Some x /\ forall n', n' < n -> nth_error Xs n' <> Some x).
    assert (WF_Type (update_Tlist Empty XNs) (TyVar x)) by
      (apply GJ_WF_Type_Wrap; econstructor; eassumption).
    assert (Free_Vars (TyVar x) (x :: nil)) by
      (apply GJ_Free_Vars_Wrap; constructor).
    generalize (wf_free_vars _ _ H1 XNs (x :: nil) (refl_equal _) H6 _ (or_introl _ (refl_equal _))).
    generalize TX_eq_dec XNs Ns H0; clear; induction Xs; destruct Ns; simpl; intros;  try discriminate.
    injection H0; intros; subst; simpl in H; contradiction.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))).
    rewrite H1 in H0; injection H0; intros; subst.
    destruct H; subst.
    exists 0; split; try reflexivity.
    intros; destruct n'; inversion H.
    destruct (TX_eq_dec a x); subst.
    exists 0; split; try reflexivity.
    intros; destruct n'; inversion H2.
    destruct (IHXs TX_eq_dec _ _ H1 H) as [n'' [nth_Xs min_n]].
    exists (S n''); simpl; split; try assumption.
    intros; destruct n'; simpl.
    unfold not; intros H3; apply n0; injection H3; auto.
    apply min_n; auto with arith.
    rewrite H1 in H0; discriminate.
    destruct H1 as [n' [nth_Xs min_n']].
    assert (exists N', nth_error Ns n' = Some N').
    generalize n' Ns XNs nth_Xs H0; clear; induction Xs; destruct Ns; simpl; intros;  try discriminate.
    injection H0; intros; subst; destruct n'; simpl in nth_Xs; discriminate.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))).
    rewrite H in H0; injection H0; intros; subst.
    destruct n'; simpl in nth_Xs.
    injection nth_Xs; intros; subst.
    exists n; reflexivity.
    simpl; eapply IHXs; eassumption.
    rewrite H in H0; discriminate.
    destruct H1 as [N' nth_Ns].
    destruct H2.
    caseEq (nth_error Us n').
    destruct (H1 _ _ H6) as [b [nth_Ns' sub_a_b]].
    rewrite nth_Ns' in nth_Ns; injection nth_Ns; intros; subst.
    assert (Ty_trans (TyVar x) Xs Us = t).
    rewrite GJ_Ty_trans_invert; generalize n' Us min_n' nth_Xs H6; clear; induction Xs; destruct Us; simpl;
      intros; destruct n'; try discriminate.
    simpl in nth_Xs, H6; injection nth_Xs; injection H6; intros; subst.
    destruct (TX_eq_dec x x); congruence.
    destruct (TX_eq_dec a x).
    elimtype False; apply (min_n' 0).
    auto with arith.
    simpl; subst; reflexivity.
    simpl in nth_Xs; simpl in H6; eapply IHXs; eauto.
    intros; apply (min_n' (S n'0)); auto with arith.
    rewrite H7.
    assert (N' = ty).
    generalize TLookup_TUpdate_eq TLookup_TUpdate_neq' TLookup_unique TX_eq_dec n' Ns XNs 
      H0 H5 nth_Ns' nth_Xs min_n'; clear; 
      induction Xs; destruct Ns; simpl in *|-*; destruct n'; intros; try discriminate.
    simpl in *|-*; injection nth_Ns'; injection nth_Xs; intros; subst.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); rewrite H in H0;
      first [discriminate | injection H0; intros; subst; clear H0].
    simpl in H5.
    rewrite (TLookup_unique _ _ _ _ H5 (TLookup_TUpdate_eq _ _ _)); reflexivity.
    destruct (TX_eq_dec x a); subst.
    elimtype False; apply (min_n' 0); auto with arith.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); rewrite H in H0;
      first [discriminate | injection H0; intros; subst; clear H0].
    simpl in H5; apply TLookup_TUpdate_neq' in H5.
    eapply IHXs; try eassumption.
    intros; apply (min_n' (S n'0)); auto with arith.
    assumption.
    rewrite <- H8; assumption.
    rewrite (H2 _ H6 ) in nth_Ns; discriminate.
  Defined.

   Lemma In_List_P1 : forall A (P : A -> Prop) (As : list A), 
     (forall a, In a As -> P a) -> List_P1 P As.
     induction As; intros.
     constructor.
     simpl; constructor.
     apply H; simpl; auto.
     apply IHAs; intros; apply H; simpl; auto.
   Qed.

   Lemma In_List_P1' : forall A (P : A -> Prop) (As : list A), 
     List_P1 P As -> (forall a, In a As -> P a).
     induction As; simpl; intros; inversion H; destruct H0; subst; eauto.
   Qed.

   Definition Free_Vars_Ty_Rename_P ty := forall Ys n Y, Free_Vars (Ty_rename ty n) Ys -> 
     In Y Ys -> exists y, Y = rename_X y n.

   Definition Free_Vars_TE_Rename_P te := forall Ys n Y, TE_Free_Vars (TE_rename te n) Ys -> 
     In Y Ys -> exists y, Y = rename_X y n.

   Lemma GJ_Free_Vars_Ty_Rename : forall Y, Free_Vars_Ty_Rename_P (Ty_Wrap (TyVar Y)).
     unfold Free_Vars_Ty_Rename_P; intros; rewrite GJ_Ty_rename_invert in H;
       simpl in H.
     apply GJ_Free_Vars_invert in H; inversion H; subst.
     apply GJ_Ty_Wrap_inject in H2; injection H2; intros; subst.
     destruct H0; subst.
     eexists _; reflexivity.
     contradiction.
   Qed.
   
   Lemma FJ_Free_Vars_Ty_Rename : forall te c, Free_Vars_TE_Rename_P te -> 
     Free_Vars_Ty_Rename_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold Free_Vars_Ty_Rename_P; unfold Free_Vars_TE_Rename_P; intros;
       repeat (rewrite FJ_Ty_rename_invert in H0; simpl in H0).
     apply FJ_Free_Vars_invert in H0; inversion H0; subst.
     apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst.
     eauto.
   Qed.

  Lemma Free_Vars_Ty_Rename_H3 : forall te Ys n Y, GJ_TE_Free_Vars (GJ_TE_rename (nil, te) n) Ys -> 
    In Y Ys -> exists y, Y = rename_X y n.
    simpl; intros; inversion H; subst.
    destruct txs; simpl in *|-*.
    contradiction.
    destruct H4.
    generalize (H2 0 (refl_equal _)); simpl; intros; discriminate.
  Qed.
  
  Lemma Free_Vars_Ty_Rename_H4 : forall ty tys te, 
    Free_Vars_TE_Rename_P (GTy_ext_Wrap (tys, te)) -> 
    Free_Vars_Ty_Rename_P ty -> 
    forall Ys n Y, GJ_TE_Free_Vars (GJ_TE_rename (ty :: tys, te) n) Ys -> 
     In Y Ys -> exists y, Y = rename_X y n.
    unfold Free_Vars_Ty_Rename_P; unfold Free_Vars_TE_Rename_P; simpl; intros.
    simpl in H1; inversion H1; subst.
    destruct txs; simpl in H2.
    contradiction.
    destruct H6.
    apply in_app_or in H2; destruct H2.
    eapply H0; try eassumption.
    destruct (H3 _ 0 (refl_equal _)) as [b [nth_b FV_l0]].
    simpl in nth_b; injection nth_b; intros; subst.
    assumption.
    eapply H; try eassumption.
    rewrite GJ_TE_rename_invert; simpl.
    eapply GJ_TE_Free_Vars_Wrap; constructor.
    split; intros.
    eapply (H3 _ (S _) H5).
    eapply (H4 (S _) H5).
  Qed.

   Variables (Ty_rename_WF_Type : forall delta S (WF_S : WF_Type delta S), Ty_rename_WF_Type_P delta S WF_S)
     (Ty_rename_WF_Type' : forall delta S (WF_S : WF_Type delta S), Ty_rename_WF_Type'_P delta S WF_S)
     (Type_Subst_Sub_2_5' : forall delta S T sub_S_T, Type_Subst_Sub_2_5_P' delta S T sub_S_T)
     (WF_context_shuffle : forall delta S WF_S, WF_context_shuffle_P delta S WF_S)
     (Free_Vars_Ty_Rename : forall ty, Free_Vars_Ty_Rename_P ty)
     (Type_Subst_WF_2_6 : forall delta S WF_S, Type_Subst_WF_2_6_P delta S WF_S).

   Lemma Type_Subst_WF_2_6' : forall gamma ty (WF_ty : WF_Type gamma ty)
     (delta_1 : Context) (Xs : list _)
    (Ns : list N) (Us : list Ty) (XNs : TyP_List),
    length Xs = length Us ->
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    gamma = update_Tlist Empty XNs ->
    List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) ->
    List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
    List_P1 (WF_Type delta_1) Us ->
    WF_Type (app_context delta_1 (subst_context Empty Xs Us)) (Ty_trans ty Xs Us).
     intros; subst.
     destruct (Finite_Context (update_Tlist Empty XNs)) as [n max_n].
     assert (List_P1 (WF_Type (rename_context delta_1 n)) (map (fun ty => Ty_rename ty n) Us)).
     apply In_List_P1; intros.
     destruct (nth_error_in' _ _ _ H1) as [n'' nth_error_Us].
     caseEq (nth_error Us n'').
     apply In_List_P1' with (a := t) in H4.
     rewrite (nth_error_map _ _ _ _ _ _ H5) in nth_error_Us; injection nth_error_Us; intros; subst.
     apply Ty_rename_WF_Type; auto.
     eapply nth_error_in; eauto.
     erewrite (nth_error_map' _ _ _ Us n'' H5) in nth_error_Us; discriminate.
     assert (List_P2 (map (fun ty => Ty_rename ty n) Us) Ns (fun (U : Ty) (N : N) => subtype (rename_context delta_1 n) 
       U (Ty_trans (N_Wrap N) Xs (map (fun ty => Ty_rename ty n) Us)))).
     destruct H2; split; intros.
     caseEq (nth_error Us n0); intros.
     rewrite (nth_error_map _ _ _ _ _ _ H7) in H6; injection H6; intros; subst; clear H6.
     destruct (H2 _ _ H7) as [b [nth_error_Ns sub_a_b]].
     exists b; split; auto.
     destruct (exists_Free_Vars (N_Wrap b)) as [Bs FV_b].
     rewrite <- (Ty_rename_Ty_trans_tot' _ Xs Us n Bs); auto.
     apply Ty_rename_subtype; auto.
     intros; generalize (wf_free_vars _ _ (In_List_P1' _ _ _ H3 _ (nth_error_in _ _ _ _ nth_error_Ns)) 
     _ _ (refl_equal _) FV_b _ H6); intro.
     generalize XNs Ns H0 H8; clear; induction Xs; destruct Ns; simpl; intros; try discriminate.
     injection H0; intros; subst; simpl in H8; contradiction.
     caseEq (zip Xs Ns (fun x => pair (TyVar x))); rewrite H in H0; try discriminate.
     injection H0; intros; subst; destruct H8; subst; simpl; auto.
     right; apply (IHXs _ _ H H1).
     rewrite (nth_error_map' _ _ _ _ _ H7) in H6; discriminate.
     apply H5.
     caseEq (nth_error Us n0); auto.
     rewrite (nth_error_map _ _ _ _ _ _ H7) in H6; discriminate.
     assert (WF_Type (app_context (rename_context delta_1 n) (update_Tlist Empty XNs)) ty).
     eapply WF_context_shuffle.
     apply (Weakening_2_1_2 _ _ WF_ty (rename_context delta_1 n)).
     reflexivity.
     intros; unfold not; intros TLookup_X0; 
       destruct (TLookup_rename_context' _ _ _ _ TLookup_X0) as [X0' [ty'' [X0_eq [ty''_eq TLookup_X0']]]];
         subst.
     eapply (max_n _ _ (TyVar X0') _ H6).
     rewrite GJ_Ty_rename_invert; simpl; apply GJ_Free_Vars_Wrap; constructor.
     simpl; auto.
     assert (length Xs = length (map (fun ty : Ty => Ty_rename ty n) Us)) as len_Xs by 
       (rewrite len_map; assumption).
     assert (forall x (ty : _),
     TLookup (rename_context delta_1 n) x ty ->
     ~ In x Xs /\
     (forall Ys,
      Free_Vars ty Ys -> forall y , In y Ys -> ~ In y Xs)).
     intros x ty' H8; destruct (TLookup_rename_context' _ _ _ _ H8) as [n' [ty'' [eq_X [eq_n Lookup_ty']]]]; split.
     unfold not; intros; assert (exists ty3, TLookup (update_Tlist Empty XNs) x ty3). 
     generalize TX_eq_dec TLookup_update_eq TLookup_update_neq TLookup_update_neq' XNs Ns H0 H7 ; 
       clear; induction Xs; destruct Ns; simpl; intros; try discriminate.
     contradiction.
     caseEq (zip Xs Ns (fun x  => pair (TyVar x))); rewrite H in H0; try discriminate.
     injection H0; intros; subst; clear H0.
     destruct H7; subst.
     exists n; apply TLookup_update_eq.
     destruct (TX_eq_dec x a); subst.
     exists n; apply TLookup_update_eq.
     destruct (IHXs TX_eq_dec TLookup_update_eq TLookup_update_neq TLookup_update_neq' _ _ H H0).
     exists x0; eapply TLookup_update_neq; eauto.
     destruct H9 as [ty3 TLookup_ty3]; subst.
     eapply (max_n _ _ (TyVar n') ((rename_X n' n) :: nil) TLookup_ty3).
     rewrite GJ_Ty_rename_invert; simpl; apply GJ_Free_Vars_Wrap; constructor.
     simpl; auto.
     intros; rewrite eq_n in H7.
     rewrite <- Ty_rename_eq_NTy_rename in H7.
     destruct (Free_Vars_Ty_Rename _ _ _ _ H7 H9).
     unfold not; intros; assert (exists ty3, TLookup (update_Tlist Empty XNs) y ty3). 
     generalize TX_eq_dec TLookup_update_eq TLookup_update_neq XNs Ns H0 H11; 
       clear; induction Xs; destruct Ns; simpl; intros; try discriminate.
     contradiction.
     caseEq (zip Xs Ns (fun x  => pair (TyVar x))); rewrite H in H0; try discriminate.
     injection H0; intros; subst; clear H0.
     destruct H11; subst.
     exists n; apply TLookup_update_eq.
     destruct (TX_eq_dec y a); subst.
     exists n; apply TLookup_update_eq.
     destruct (IHXs TX_eq_dec TLookup_update_eq TLookup_update_neq _ _ H H0).
     exists x; eapply TLookup_update_neq; eauto.
     destruct H12 as [ty3 TLookup_ty3].
     subst; eapply (max_n _ _ _ _ TLookup_ty3).
     eauto.
     assumption.
     generalize (fun H5 => Type_Subst_WF_2_6 _ _  H6 _ _ _ _ _ _ len_Xs H0 (refl_equal _) H5 H1 H7).
     repeat rewrite subst_context_Empty; repeat rewrite app_context_Empty.
     assert (Extract_TyVar XNs = Xs).
     generalize Ns XNs H0; clear; induction Xs; destruct Ns; simpl; intros; try discriminate.
     injection H0; intros; subst; reflexivity.
     caseEq (zip Xs Ns (fun x => pair (TyVar x))); rewrite H in H0; try discriminate;
       injection H0; intros; subst.
     simpl; erewrite IHXs; eauto.
     intros; eapply Ty_rename_WF_Type'; try reflexivity.
     destruct (exists_Free_Vars ty).
     erewrite (Ty_rename_Ty_trans_tot'); eauto.
     intros; apply H9.
     destruct H5; split; intros.
     destruct (H5 _ _ H12) as [b [bth_error_b sub_a_b]].
     exists b; split; auto.
     rewrite Ty_trans_eq_NTy_trans.
     apply sub_a_b.
     eauto.
     intros; rewrite <- H8; apply (wf_free_vars _ _ WF_ty _ _ (refl_equal _) H10 _ H11).
   Qed.

   Variable (mtype_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
     (mtype_build_te'' : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop).

   Definition proj_ce {C F M X ty_ext Ty E md_ext cld_ext}
     (cld' : cFJ.L C F M X ty_ext Ty E md_ext cld_ext) : cld_ext :=
     match cld' with 
       cFJ.cld ce _ _ _ _ _ => ce
     end.

   Lemma GJ_WF_cld_ext_Lem' {L_WF_Ext'} : forall (gamma : Context) ce te,
     @GJ_wf_class_ext cld_def_ext ty_def_ext gamma ce te -> 
     forall te'' c c1 gamma' gamma'' gamma''' (ce' : @GJ_definitions.cld_ext cld_def_ext) te' 
       (WF_ce : GJ_definitions.L_WF_Ext L_WF_Ext' gamma'' ce c1) 
       (WF_ce' : GJ_definitions.L_WF_Ext L_WF_Ext' gamma''' ce' c)
       (build_gamma''' : GJ_definitions.L_build_context L_build_context' ce' gamma'''),
       @GJ_wf_class_ext cld_def_ext ty_def_ext gamma' ce' te' -> 
       GJ_definitions.L_build_context L_build_context' ce gamma'' ->
       GJ_definitions.L_build_context L_build_context' ce gamma' -> 
       mtype_build_te mtype_build_te' ce te te' te'' ->
       GJ_wf_class_ext gamma ce' te''. 
     intros; inversion H; inversion H0.
     injection H14; injection H15; intros; clear H14 H15; subst.
     inversion H3; subst; econstructor.
     unfold Tys_Trans.

     assert (List_P1 (fun ty => WF_Type gamma (Ty_trans ty (Extract_TyVar typs) tys)) tys0).
     apply In_List_P1; intros.
     inversion H2.
     assert (forall a, In a tys0 -> WF_Type (update_Tlist Empty typs) a) by
       (rewrite <- H9 in H10; intros; eapply L_build_context'_Empty_1; try eassumption;
         eapply In_List_P1'; try eassumption).
     assert (app_context gamma (subst_context Empty (Extract_TyVar typs) tys) = gamma) 
       as subst_Empty by (rewrite subst_context_Empty; rewrite app_context_Empty; reflexivity).
     rewrite <- subst_Empty; eapply Type_Subst_WF_2_6' with (XNs := typs) (Ns := map (@snd _ _) typs).
     eapply H15; auto.
     generalize tys H5; clear; induction typs; simpl; auto.
     intros; destruct tys; first [discriminate | injection H5; intros; rewrite (IHtyps _ H); reflexivity].
     clear; induction typs; simpl.
     reflexivity.
     rewrite IHtyps; destruct a; destruct g; simpl; reflexivity.
     reflexivity.
     assert (exists Ys, Extract_TyVar typs = Ys) as ex_Ys by (eexists _; reflexivity);
       destruct ex_Ys as [Ys' eq_Ys']; rewrite eq_Ys' in *|-*.
     assert (exists tys'', tys = tys'') as ex_tys'' by (eexists _; reflexivity);
       destruct ex_tys'' as [tys'' eq_tys''];
         rewrite eq_tys'' at 1; revert H6; rewrite eq_tys'' at 1; intros.
     apply P2'_if_P2; apply P2_if_P2' in H6; generalize tys Ys' typs H6; clear;
       induction tys''; simpl; intros; inversion H6; subst.
     destruct typs; simpl.
     constructor.
     simpl in H; discriminate.
     destruct typs; simpl in H1; first [discriminate | injection H1; intros; subst; clear H1].
     econstructor; auto.
     rewrite <- H9 in H12.
     inversion WF_ce.
     apply In_List_P1; intros.
     inversion H1.
     eapply L_build_context'_Empty_1; try eassumption.
     assert (exists X', In (X', a0) typs).
     generalize H24; clear; induction typs; simpl; intros; destruct H24.
     destruct a; exists g; simpl in H; subst; auto.
     destruct (IHtyps H); eexists _; right; eauto.
     destruct H29 as [X' eq_a0].
     generalize (In_List_P1' _ _ _ H23 _ eq_a0).
     rewrite H26; auto.
     assumption.
     apply In_List_P1; intros.
     assert (exists a', In a' tys0 /\ a = Ty_trans a' (Extract_TyVar typs) tys).
     generalize H8; clear; induction tys0; simpl; intros; destruct H8.
     exists a0; auto.
     destruct (IHtys0 H) as [a' [In_a' eq_a]]; exists a'; split; auto.
     destruct H9 as [a' [In_a' eq_a]].
     rewrite eq_a; apply (In_List_P1' _ _ _ H7 _ In_a').
     generalize tys0 H11; clear; induction typs0; destruct tys0; simpl; intros; try discriminate.
     reflexivity.
     injection H11; intros H; rewrite (IHtyps0 _ H); reflexivity.
     destruct H12 as [In_tys' NIn_tys']; split; intros.
     assert (exists a', nth_error tys0 n = Some a' /\ a = (Ty_trans a' (Extract_TyVar typs) tys)).
     revert n H7; clear; induction tys0; simpl; intros.
     rewrite nth_error_nil in H7; discriminate.
     destruct n; simpl in *|-*.
     injection H7; intros; subst; exists a0; split; reflexivity.
     eauto.
     destruct H8 as [a' [nth_tys' a'_eq]]; subst.
     destruct (In_tys' _ _ nth_tys') as [b [nth_t sub_a'_b]].
     exists (Ty_trans b (Extract_TyVar typs) tys); split.
     simpl in build_gamma'''; inversion build_gamma'''; subst.
     assert (exists typs', typs0 = typs') as eq_typs0 by (eexists _; reflexivity); destruct 
       eq_typs0 as [typs' eq_typs']; rewrite eq_typs' at 1.
     revert nth_t; rewrite eq_typs' at 1; intros nth_t.     
     simpl in WF_ce'; inversion WF_ce'.
     assert (List_P1 (fun typ : GTy * N => WF_Type (update_Tlist Empty typs0) (snd typ)) typs').
     rewrite <- eq_typs'.
     apply In_List_P1; intros; eapply L_build_context'_Empty_1; try eassumption.
     apply (In_List_P1' _ _ _ H16 _ H19).
     assert (forall typ, In typ typs' -> exists Vs, Free_Vars (snd typ) Vs /\ forall V, In V Vs -> 
       In V (Extract_TyVar typs0)).
     intros.
     generalize (In_List_P1' _ _ _ H19 _ H20); intros.
     destruct (exists_Free_Vars (snd typ)) as [Vs FV_typ].
     exists Vs; split; auto.
     eapply wf_free_vars; try eassumption.
     reflexivity.
     generalize map_Ty_trans' n typs nth_t H20 H11; clear; induction typs'; intros; simpl in nth_t.
     rewrite nth_error_nil in nth_t; discriminate.
     destruct n; simpl in *|-.
     injection nth_t; intros; subst; simpl.
     destruct a; destruct g; simpl.
     destruct (H20 (TyVar t, n)) as [Vs [FV_typ Bnd_Vs]]; auto.
     rewrite (map_Ty_trans' (N_Wrap n) (Extract_TyVar typs) Vs tys tys0 typs0 FV_typ H11 Bnd_Vs);
       reflexivity.
     simpl.
     rewrite (IHtyps' map_Ty_trans' _ _ nth_t); try reflexivity.
     intros; apply H20; auto.
     assumption.
     rewrite <- (app_context_Empty gamma); rewrite <- (subst_context_Empty (Extract_TyVar typs) tys).
     inversion H2; rewrite <- H9 in sub_a'_b.
     eapply L_build_context'_Empty_2 in sub_a'_b.
     eapply Type_Subst_Sub_2_5' with (XNs := typs) (Ns := map (@snd _ _) typs).
     apply sub_a'_b.
     generalize tys H5; clear; induction typs; simpl; auto.
     intros; destruct tys; first [discriminate | injection H5; intros; rewrite (IHtyps _ H); reflexivity].
     clear; induction typs; simpl.
     reflexivity.
     rewrite IHtyps; destruct a; destruct g; simpl; reflexivity.
     reflexivity.
     assert (exists Ys, Extract_TyVar typs = Ys) as ex_Ys by (eexists _; reflexivity);
       destruct ex_Ys as [Ys' eq_Ys']; rewrite eq_Ys' in *|-*.
     assert (exists tys'', tys = tys'') as ex_tys'' by (eexists _; reflexivity);
       destruct ex_tys'' as [tys'' eq_tys''];
         rewrite eq_tys'' at 1; revert H6; rewrite eq_tys'' at 1; intros.
     apply P2'_if_P2; apply P2_if_P2' in H6; generalize tys Ys' typs H6; clear;
       induction tys''; simpl; intros; inversion H6; subst.
     destruct typs; simpl.
     constructor.
     simpl in H; discriminate.
     destruct typs; simpl in H1; first [discriminate | injection H1; intros; subst; clear H1].
     econstructor; auto.
     assumption.
     apply In_List_P1; intros.
     assert (exists a', snd a' = a /\ In a' typs).
       generalize H14; clear; induction typs; simpl; intros H; destruct H.
     exists a0; split; auto.
     destruct (IHtyps H) as [a' [eq_a' In_a']]; exists a'; split; auto.
     destruct H15 as [a'' [eq_a'' In_a'']].
     inversion H1.
     inversion WF_ce.
     generalize (In_List_P1' _ _ _ H26 _ In_a''); subst.
     intros; eapply L_build_context'_Empty_1.
     eassumption.
     assumption.
     eassumption.
     assert (nth_error tys0 n = None).
     generalize n H7; clear; induction tys0; simpl; intros; auto;
       destruct n; simpl in *|-*; first [discriminate | eauto].
     assert (exists Ys, Extract_TyVar typs0 = Ys) as ex_Ys by (eexists _; reflexivity);
       destruct ex_Ys as [Ys' eq_Ys']; rewrite eq_Ys' in *|-*.
     generalize n Ys' (NIn_tys' _ H8); clear; induction typs0; simpl; intros; auto.
     destruct n; simpl in *|-*; first [discriminate | eauto].
   Qed.

   Variables (WF_cld_ext_Lem' : forall (gamma : Context) ce te,
     wf_class_ext' gamma ce te ->
     forall te'' c c1 gamma' gamma'' gamma''' ce' te' (WF_ce : L_WF_Ext gamma'' ce c1),
       L_WF_Ext gamma''' ce' c -> L_build_context ce' gamma''' -> 
       wf_class_ext' gamma' ce' te' -> 
       L_build_context ce gamma'' -> L_build_context ce gamma' -> 
       mtype_build_te'' ce te te' te'' ->
       wf_class_ext' gamma ce' te'')
   (CT_eq : forall c ce c' d fds k' mds, 
     CT c = Some (cld C F M X ty_ext Ty E md_ext cld_ext ce c' d fds k' mds) -> c = c').

   Lemma WF_cld_ext_Lem : forall gamma cld te (wf_cld : wf_class_ext' gamma cld te),
     WF_cld_ext_Lem_Q C F M X _ Ty E md_ext _ CT
     Context wf_class_ext' mtype_build_te'' L_build_context gamma cld te wf_cld.
     unfold WF_cld_ext_Lem_Q.
     intros; subst.
     generalize (WF_CT _ _ H0) as WF_cld1; intros; destruct (L_WF_bound _ WF_cld1) as [Ys [FV_te' Bound_Ys]].
     generalize (WF_CT _ _ H4) as WF_c1; intros; destruct (L_WF_bound _ WF_c1) as [Vs [FV_te'' Bound_Vs]].
     inversion WF_c1; subst.
     destruct cld'.
     inversion WF_cld1; subst.
     eapply WF_cld_ext_Lem' with (ce := cld) (gamma''' := gamma2).
     apply wf_cld.
     apply H19.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
     eassumption.
   Qed.

   Definition Lem_2_8_P delta S T (sub_S_T : subtype delta S T) :=
     forall T' fds', Bound' delta T T' ->
     fields Empty T' fds' ->
     exists S' : _,
       Bound' delta S S' /\
       (exists fds,
         fields Empty S' fds /\
         (forall fd' (n : nat),
           nth_error fds' n = Some fd' -> nth_error fds n = Some fd')).

   Lemma fields_build_te_id' 
     (fields_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop) 
     (build_te' : cld_def_ext ->
       ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop) 
     (H : forall ce te te' te'' te''', 
       build_te' ce te te' te'' -> fields_build_te' ce te te' te''' -> te'' = te''') :
     forall ce te te' te'' te''',
     @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te' te'' ->
     fields_build_te fields_build_te' ce te te' te''' -> te'' = te'''.
     intros; inversion H0; inversion H1; subst.
     injection H10; injection H11; injection H12; intros; subst.
     rewrite (H _ _ _ _ _ H2 H8).
     reflexivity.
   Qed.

   Variable (N_Bound'_invert : forall delta n ty, Bound' delta (N_Wrap n) ty -> N_Bound delta n ty)
     (GJ_Bound'_invert : forall delta n ty, Bound' delta (Ty_Wrap n) (N_Wrap ty) -> GJ_Bound delta n ty).

   Variable (Bound_total : forall gamma S T sub_S_T, Bound_total_P gamma S T sub_S_T).
   
   Set Printing Coercions.

   Lemma GJ_Lem_2_8 :  forall delta S T (sub_S_T : GJ_subtype delta S T),
     Lem_2_8_P delta S T sub_S_T.
     unfold Lem_2_8_P; intros.
     inversion sub_S_T; subst.
     apply N_Bound'_invert in H; inversion H; subst.
     apply N_Wrap_inject in H4; subst.
     exists ty; split; eauto.
     apply GJ_Bound'_Wrap.
     constructor; assumption.
   Qed.

   Variable WF_mtype_ty_0_map_id : forall S delta T T', WF_mtype_ty_0_map delta S T ->
     WF_mtype_ty_0_map delta S T' -> T = T'.
   Variable WF_mtype_ty_0_map_refl : forall delta (T : N), WF_mtype_ty_0_map delta T T.
   Variable WF_mtype_ty_0_map_TLookup : forall delta x ty, TLookup delta x ty ->
     WF_mtype_ty_0_map delta (TyVar x) ty.

   Lemma GJ_Lem_2_9 : forall delta S T (sub_S_T : GJ_subtype delta S T),
     Lem_2_9_P _ _ _ _ _ subtype mtype WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T.
     unfold Lem_2_9_P; intros.
     inversion sub_S_T; subst.
     rewrite (WF_mtype_ty_0_map_id _ _ _ _ H (WF_mtype_ty_0_map_refl _ _)) in H0.
     rewrite (WF_mtype_ty_0_map_id _ _ _ _ H4 (WF_mtype_ty_0_map_TLookup _ _ _ H5)).
     repeat eexists _; split; try eassumption; eexists _; repeat split; try eassumption.
     apply FJ_subtype_Wrap; constructor.
   Qed.

   Lemma GJ_Subtype_Weaken : forall gamma S T (sub_S_T : GJ_subtype gamma S T),
     Subtype_Weaken_P _ _ subtype Empty gamma S T sub_S_T.
     cbv; intros; inversion sub_S_T; subst.
     elimtype False; eapply TLookup_Empty; eauto.
   Qed.

   Definition Weaken_subtype_Update_list_P  delta' S T (_ : subtype delta' S T) :=
     forall delta Vars, delta' = update_list delta Vars -> subtype delta S T.
   
   Lemma TLookup_Update_Weaken : forall gamma Vars X ty,
     TLookup (update_list gamma Vars) X ty -> TLookup gamma X ty.
     induction Vars; simpl; intros; auto.
     destruct a; apply IHVars; eauto.
   Qed.
   
   Lemma FJ_Weaken_subtype_Update_list
     (subtype_rect : forall delta S T sub_S_T, Weaken_subtype_Update_list_P delta S T sub_S_T) :
     forall delta S T (sub_S_T : FJ_subtype delta S T),
       Weaken_subtype_Update_list_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
     intros; eapply FJ_subtype_rect with (P := Weaken_subtype_Update_list_P); try assumption;
       unfold Weaken_subtype_Update_list_P; clear subtype_rect; intros; apply FJ_subtype_Wrap.
     constructor.
     constructor 2 with (d := d); eauto.
     econstructor 3; try eassumption.
   Defined.

   Lemma GJ_Weaken_subtype_Update_list :
     forall delta S T (sub_S_T : GJ_subtype delta S T),
       Weaken_subtype_Update_list_P delta S T (subtype_Wrap _ _ _ sub_S_T).
     unfold Weaken_subtype_Update_list_P; intros.
     intros; inversion sub_S_T; subst.
     apply subtype_Wrap; constructor.
     eapply TLookup_Update_Weaken; eauto.
   Qed.

   Variable (Weaken_subtype_Update_list : forall delta S T sub_S_T, Weaken_subtype_Update_list_P delta S T sub_S_T).

   Definition Weaken_WF_Update_list_P  delta' S (_ : WF_Type delta' S) :=
     forall delta Vars, delta' = update_list delta Vars -> WF_Type delta S.
   
   Definition Weaken_WF_Update_list_Q delta' cld te (_ : wf_class_ext' delta' cld te) :=
     forall delta Vars, delta' = update_list delta Vars -> wf_class_ext' delta cld te.
   
   Definition Weaken_WF_Update_list_P1 delta' tys (_ : List_P1 (WF_Type delta') tys) :=
     forall delta Vars, delta' = update_list delta Vars -> List_P1 (WF_Type delta) tys.
   
  Lemma Weaken_WF_Update_list_ext_H1 : forall gamma (ce : cld_def_ext) tys typs 
    (te : ty_def_ext) P1 (len : length typs = length tys)
    (P2 : List_P2 tys 
      (map (fun typ' => Ty_trans (N_Wrap (snd typ')) (Extract_TyVar typs) tys) typs) (subtype gamma)),
    Weaken_WF_Update_list_P1 gamma tys P1-> 
    forall delta Vars, gamma = update_list delta Vars -> 
      GJ_wf_class_ext delta (typs, ce) (tys, te).
    unfold Weaken_WF_Update_list_P1; intros; subst.
    constructor; auto.
    eapply H; reflexivity.
    destruct P2 as [In_ty NIn_ty]; split; intros.
    destruct (In_ty _ _ H0) as [b [nth_b sub_a_b]]; exists b; split; auto.
    eapply Weaken_subtype_Update_list; try eassumption; reflexivity.
    auto.
  Qed.
    
  Lemma Weaken_WF_Update_list_ext_H2 : forall gamma, 
    Weaken_WF_Update_list_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Weaken_WF_Update_list_P1; intros; constructor.
  Qed.
    
  Lemma Weaken_WF_Update_list_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Weaken_WF_Update_list_P _ _ P_ty -> Weaken_WF_Update_list_P1 _ tys P_tys -> 
    Weaken_WF_Update_list_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Weaken_WF_Update_list_P; unfold Weaken_WF_Update_list_P1; intros;
      constructor; eauto.
  Qed.

  Variable (Weaken_WF_Update_list_obj_ext : 
    forall gamma te, wf_object_ext' gamma te ->
      forall delta Vars, gamma = update_list delta Vars -> wf_object_ext' delta te).

  Lemma GJ_Weaken_WF_Update_list_obj_ext : forall gamma (te : @GTy_ext ty_def_ext), GJ_wf_object_ext gamma te ->
      forall delta Vars, gamma = update_list delta Vars -> GJ_wf_object_ext delta te.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_Weaken_WF_Update_list_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Weaken_WF_Update_list_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Weaken_WF_Update_list_P; intros; apply FJ_WF_Type_Wrap; constructor.
    apply (Weaken_WF_Update_list_obj_ext _ _ wf_obj _ _ H).
  Qed.
    
  Lemma FJ_Weaken_WF_Update_list_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Weaken_WF_Update_list_Q _ _ _ wf_cld_ext ->
    Weaken_WF_Update_list_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Weaken_WF_Update_list_Q; unfold Weaken_WF_Update_list_P; intros; apply FJ_WF_Type_Wrap.
    econstructor; try eassumption.
    exact (H _ _ H0).
  Qed.
  
  Lemma GJ_Weaken_WF_Update_list : forall delta S (WF_S : GJ_WF_Type delta S), 
    Weaken_WF_Update_list_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Weaken_WF_Update_list_P; intros.
    inversion WF_S; subst.
    apply GJ_WF_Type_Wrap.
    econstructor.
    apply (TLookup_Update_Weaken _ _ _ _ H0).
  Qed.
   
  Variable (Weaken_WF_Update_list : forall delta S WF_S, Weaken_WF_Update_list_P delta S WF_S).

  Lemma WF_mtype_ext_update_list_id' (m_call_ext' mty_def_ext' : Set)
    (WF_mtype_ext' : Context -> m_call_ext' -> mty_def_ext' -> Prop) 
    (H1 : forall gamma mce mtye vars, WF_mtype_ext' (update_list gamma vars) mce mtye ->
      WF_mtype_ext' gamma mce mtye) : 
    forall (gamma : Context) (mce : @MCall_ext m_call_ext') (mtye : mty_ext)
      (vars : list (Var X * Ty)),
      GJ_WF_mtype_ext _ _ WF_mtype_ext' (update_list gamma vars) mce mtye ->
      GJ_WF_mtype_ext _ _ WF_mtype_ext' gamma mce mtye.
    unfold GJ_WF_mtype_ext; intros; destruct mce; destruct mtye;
      destruct H as [FJ_WF_mce' [WF_Vs sub_Vs]]; repeat split.
    apply (H1 _ _ _ _ FJ_WF_mce').
    apply In_List_P1; intros; generalize (In_List_P1' _ _ _ WF_Vs _ H); intros.
    eapply Weaken_WF_Update_list; try eassumption; reflexivity.
     destruct sub_Vs as [H H2]; intros a n nth_l; 
       destruct (H _ _ nth_l) as [b [nth_b sub_a_b]]; exists b; split; auto.
     eapply Weaken_subtype_Update_list; eauto.
     destruct sub_Vs as [H H2]; eauto.
   Qed.

   Lemma build_te_id'
     (mbody_build_te' : cld_def_ext ->
       ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
     (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop) 
     (H : forall ce te te' te'',
       mbody_build_te' ce te te'' te' -> build_te' ce te te'' te') :
     forall ce te te' te'',
     mbody_build_te mbody_build_te' ce te te'' te' ->
     @GJ_build_te cld_def_ext ty_def_ext build_te' ce te te'' te'.
     intros; inversion H0; subst.
     constructor; auto.
   Qed.   

   Lemma WF_mtype_Us_map_len' 
     (WF_mtype_Us_map' : Context -> m_call_ext -> mty_def_ext -> list Ty -> list Ty -> Prop) 
     (H : forall delta mce mtye Ds Ds', WF_mtype_Us_map' delta mce mtye Ds Ds' -> length Ds = length Ds'):
     forall (delta : Context) mce mtye Ds Ds',
     GJ_WF_mtype_Us_map m_call_ext mty_def_ext WF_mtype_Us_map' delta mce mtye Ds Ds' -> length Ds = length Ds'.
     intros; inversion H0; subst.
     unfold Tys_Trans; rewrite len_map.
     eapply H; eauto.
   Qed.
   
   Lemma mtype_build_tys_len' 
     (mtype_build_tys' : cld_def_ext -> ty_ext -> Ty -> list VD -> md_def_ext -> list Ty -> list Ty -> Prop)
     (H : forall ce te ty vds mde Ds Ds', mtype_build_tys' ce te ty vds mde Ds Ds' -> length Ds = length Ds'):
     forall ce te ty vds mde Ds Ds',
       mtype_build_tys mtype_build_tys' ce te ty vds mde Ds Ds' -> length Ds = length Ds'.
     intros; inversion H0; subst.
     unfold Tys_Trans; repeat rewrite len_map.
     eapply H; eauto.
   Qed.
   
   Lemma methods_build_te_id' 
     (mtype_build_te''' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (mbody_build_te''' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (H : forall ce te te' te'' te''', mtype_build_te''' ce te te' te'' ->
       mbody_build_te''' ce te te' te''' -> te'' = te''') :
     forall ce te te' te'' te''',
       mtype_build_te mtype_build_te''' ce te te' te'' ->
       mbody_build_te mbody_build_te''' ce te te' te''' -> te'' = te'''.
     intros; inversion H0; inversion H1; subst.
     injection H10; injection H11; injection H12; intros; subst; clear H10 H11 H12.
     rewrite (H _ _ _ _ _ H2 H8); reflexivity.
   Qed.
   
   Variable (FJ_N_Ty_Wrap_inject : forall n n', FJ_N_Ty_Wrap n = FJ_N_Ty_Wrap n' -> n = n')
     (FJ_fields_id : forall gamma ty fds fields_ty, fields_id_P C F ty_ext Ty FJ_Ty_Wrap
       _ fields gamma ty fds fields_ty).

   Lemma WF_fields_map_sub' : forall (gamma : Context) (c : cFJ.CL C)
     (tye tye' : ty_ext) (fds fds' : list (cFJ.FD _ Ty)),
     Bound' gamma (FJ_Ty_Wrap (ty_def _ _ tye c)) (FJ_Ty_Wrap (ty_def _ _ tye' c)) ->
     fields Empty (FJ_Ty_Wrap (ty_def _ _ tye c)) fds ->
     fields Empty (FJ_Ty_Wrap (ty_def _ _ tye' c)) fds' ->
     List_P2'
     (fun fd' fd''  =>
       match fd' with
         | fd S' _ => match fd'' with
                        | fd T' _ => subtype Empty S' T'
                      end
       end) fds fds'.
     intros; apply N_Bound'_invert in H; inversion H; subst.
     apply N_Wrap_inject in H4; apply N_Wrap_inject in H5; subst.
     apply FJ_N_Ty_Wrap_inject in H5; injection H5; intros; subst.
     rewrite (FJ_fields_id _ _ _ H1 _ _ _ (refl_equal _) H0).
     generalize FJ_subtype_Wrap; clear; induction fds; intros; constructor.
     destruct a; apply FJ_subtype_Wrap; constructor.
     apply IHfds; auto.
   Qed.
   
   Definition WF_mtype_mab_sub_def gamma ty ty' (Bound_ty : Bound' gamma ty ty') :=
     subtype gamma ty ty'.

   Lemma N_WF_mtype_map_sub : forall gamma ty ty' Bound_ty,
     WF_mtype_mab_sub_def gamma ty ty' (N_Bound'_Wrap _ _ _ Bound_ty).
     unfold WF_mtype_mab_sub_def; intros.
     apply FJ_subtype_Wrap.
     destruct Bound_ty; constructor.
   Qed.
     
   Lemma GJ_WF_mtype_map_sub : forall gamma ty ty' Bound_ty,
     WF_mtype_mab_sub_def _ _ _ (GJ_Bound'_Wrap gamma ty ty' Bound_ty).
     unfold WF_mtype_mab_sub_def; intros.
     destruct Bound_ty; apply subtype_Wrap; constructor.
     assumption.
   Qed.
 
  Lemma mtype_mbody_build_te
     (mtype_build_te''' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (mbody_build_te''' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (H : forall ce te te' te'', mtype_build_te''' ce te te' te'' ->
       mbody_build_te''' ce te te' te'') :
     forall ce te te' te'',
       mtype_build_te mtype_build_te''' ce te te' te'' ->
       mbody_build_te mbody_build_te''' ce te te' te''.
    intros; inversion H0; subst; constructor; auto.
  Qed.

  Lemma WF_mtype_ty_0_map_Empty_refl' : 
    forall (gamma : Context) te c (ty : Ty),
      Bound' gamma (FJ_Ty_Wrap (ty_def _ _ te c)) ty -> ty = FJ_Ty_Wrap (ty_def _ _ te c).
    intros; apply N_Bound'_invert in H; inversion H.
    rewrite H2.
    reflexivity.
  Qed.
 
  Lemma build_te_id 
     (mbody_build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (build_te' : cld_def_ext -> ty_ext -> ty_ext -> ty_ext -> Prop) 
     (H : forall ce te te' te'', mbody_build_te' ce te te' te'' ->
       build_te' ce te te' te'') :
     forall ce te te' te'',
       mbody_build_te mbody_build_te' ce te te' te'' ->
       GJ_build_te build_te' ce te te' te''.
    intros; inversion H0; subst; constructor; auto.
  Qed.

  Lemma WF_mtype_ty_0_map_cl_id'' : forall (delta : Context) te  
    (d : cFJ.CL _) (S' : Ty),
    Bound' delta (FJ_Ty_Wrap (ty_def _ _ te d)) S' -> S' = FJ_N_Ty_Wrap (ty_def _ _ te d).
    intros; apply N_Bound'_invert in H; inversion H; subst.
    reflexivity.
  Qed.

  Lemma WF_mtype_ty_0_map_tot' : forall (delta : Context) te c,
    exists S' : Ty, Bound' delta (FJ_Ty_Wrap (ty_def _ _ te c)) S'.
    intros; exists (FJ_N_Ty_Wrap (ty_def _ _ te c)); apply N_Bound'_Wrap. 
    eapply N_bound.
  Qed.

  Definition WF_Type_par_Lem_P' mtype_build_te := 
    WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty FJ_Ty_Wrap E _ _ CT Context wf_class_ext'
    WF_Type mtype_build_te L_build_context.

  Lemma GJ_WF_Type_par_Lem' mtype_build_te : 
    forall gamma ty wf_ty, WF_Type_par_Lem_P' mtype_build_te gamma ty (GJ_WF_Type_Wrap _ _ wf_ty).
    unfold WF_Type_par_Lem_P'; unfold cFJ.WF_Type_par_Lem_P'; intros; subst.
    inversion wf_ty; subst.
    apply sym_eq in H; apply Ty_Wrap_discriminate in H; contradiction.
  Qed.

  Lemma Bound_tot : forall (gamma : Context) te  (c : cFJ.CL _),
    exists te', Bound' gamma (FJ_N_Ty_Wrap (ty_def _ _ te c)) (FJ_N_Ty_Wrap (ty_def _ _ te' c)).
    intros; exists te; apply N_Bound'_Wrap; econstructor.
  Qed.

  Variable (GJ_Bound'_invert' : forall (delta : Context) (Y : GTy) (ty : Ty),
    Bound' delta Y ty -> exists n, ty = N_Wrap n /\ GJ_Bound delta Y n).

  Lemma GJ_Bound_ty : forall delta (ty : GTy) ty', Bound' delta ty ty' ->
    exists n, ty' = N_Wrap n.
    intros; eapply GJ_Bound'_invert' in H; destruct H as [n [n_eq Bound_ty]]; subst;
      eexists _; reflexivity.
  Qed.

  Lemma GJ_Bound_id : forall delta ty ty', GJ_Bound delta ty ty' -> 
    forall ty'', Bound' delta ty ty'' -> (N_Wrap ty') = ty''.
    intros; inversion H; subst.
    destruct (GJ_Bound_ty _ _ _ H0) as [n eq_ty'']; rewrite eq_ty'' in H0.
    apply GJ_Bound'_invert in H0; inversion H0; subst.
    apply GJ_Ty_Wrap_inject in H2; injection H2; intros; subst.
    rewrite (TLookup_unique _ _ _ _ H1 H4); reflexivity.
  Qed.

  Lemma N_Bound_id : forall delta ty ty', N_Bound delta ty ty' -> 
    forall ty'', Bound' delta ty ty'' -> ty' = ty''.
    intros; inversion H; subst; apply N_Bound'_invert in H0; inversion H0; subst.
    reflexivity.
  Qed.

  Lemma GJ_WF_Type_par mtype_build_te : forall delta ty (WF_ty : GJ_WF_Type delta ty),
    cFJ.WF_Type_par_P _ _ _ _ ty_ext Ty FJ_Ty_Wrap E _ _ CT _ WF_Type mtype_build_te
    L_build_context delta ty (GJ_WF_Type_Wrap _ _ WF_ty).
    unfold WF_Type_par_P; intros.
    inversion WF_ty; subst.
    elimtype False; apply (Ty_Wrap_discriminate _ _ (sym_eq H6)).
  Qed.

  Section fields_build_te_id_sec.
    
    Variable (fields_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
      (fields_build_te' : forall ce te te' te'' te''', 
        build_te ce te te' te'' -> fields_build_te ce te te' te''' -> te'' = te''').

    Lemma fields_build_te_id_Bound : forall (gamma : Context) ce c d te te' te'' te3 te4 te5,
      build_te ce te te5 te' ->
      Bound' gamma (FJ_Ty_Wrap (ty_def _ _ te' d)) (FJ_Ty_Wrap (ty_def _ _ te'' d)) ->
      Bound' gamma (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) (FJ_Ty_Wrap (ty_def _ _ te3 (cl _ c))) ->
      fields_build_te ce te3 te5 te4 -> te'' = te4.
      intros; apply N_Bound'_invert in H0; apply N_Bound'_invert in H1; inversion H0; inversion H1; 
        subst.
      apply N_Wrap_inject in H5; apply N_Wrap_inject in H6; apply N_Wrap_inject in H8;
        apply N_Wrap_inject in H9; subst; apply FJ_N_Ty_Wrap_inject in H6;
          apply FJ_N_Ty_Wrap_inject in H9; injection H9; injection H6; intros; subst.
      eapply fields_build_te'; eassumption.
    Qed.
  
  End fields_build_te_id_sec.  

  Lemma bld_te_eq_fields_build_te : forall {cld_def_ext ty_def_ext : Set}
    (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
    (fields_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
    (H1 : forall ce te te' te'',  build_te' ce te te' te'' -> fields_build_te' ce te te' te'') 
    ce te te' te'',
    GJ_build_te build_te' ce te te' te'' ->
    fields_build_te fields_build_te' ce te te' te''.
    intros; inversion H; subst.
    constructor; auto; eapply (H1 _ _ _ _ H0). 
  Qed.

  Lemma GJ_WF_mtype_ty_0_map_refl : forall (delta : Context) T,
    Bound' delta (FJ_Ty_Wrap T) (FJ_Ty_Wrap T).
    intros; apply N_Bound'_Wrap; constructor.
  Qed.

  Lemma GJ_WF_mtype_ty_0_map_TLookup : forall delta x ty, TLookup delta x ty ->
    Bound' delta (Ty_Wrap (TyVar x)) ty.
    intros; eapply GJ_Bound'_Wrap; constructor; assumption.
  Qed.

  Lemma Extract_TyVar_Typs_Trans_eq : forall YOs XNs Ts,
    Extract_TyVar (Typs_Trans XNs Ts YOs) = Extract_TyVar YOs.
    clear; unfold Extract_TyVar; unfold Typs_Trans; induction YOs; simpl; intros; auto.
    destruct a; destruct g; simpl; rewrite IHYOs; reflexivity.
  Qed.

  Lemma Extract_TyVar_app : forall tys tys', 
    Extract_TyVar (tys ++ tys') = (Extract_TyVar tys) ++ (Extract_TyVar tys').
    induction tys; simpl; intros; auto; destruct a; destruct g; simpl; congruence.
  Qed.

  Definition Bound'_sub_P X := forall delta Y, Bound' delta X Y -> subtype delta X Y.
  
  Lemma N_Bound'_sub : forall ty, Bound'_sub_P (FJ_Ty_Wrap ty).
    unfold Bound'_sub_P; intros; apply N_Bound'_invert in H; inversion H; subst.
    unfold FJ_Ty_Wrap; rewrite H2; apply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma GJ_Bound'_sub : forall ty, Bound'_sub_P (Ty_Wrap ty).
    unfold Bound'_sub_P; intros; apply GJ_Bound'_invert' in H; destruct H as [n [eq_n Bound'_ty]];
      inversion Bound'_ty; subst; apply GJ_Ty_Wrap_inject in H; subst.
    apply subtype_Wrap; econstructor; assumption.
  Qed.

  Variable build_fresh_tot : forall tys ty tys' Xs Ys, exists Xs', build_fresh tys ty tys' Xs Ys Xs'.
  Variable build_fresh_len : forall tys ty vds Xs Ys Zs, build_fresh tys ty vds Xs Ys Zs -> length Ys = length Zs.

  Lemma mtype_build_mtye_tot 
    (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
    (mtype_build_mtye' : cld_def_ext -> ty_def_ext -> Ty -> list VD -> md_def_ext -> mty_def_ext -> Prop) 
    (H : forall ce te te' te'' ty vds mde', 
      build_te' ce te te'' te' -> exists mtye' , mtype_build_mtye' ce te ty vds mde' mtye') :
    forall ce te te' te'' (ty : Ty) vds mde', 
      GJ_build_te build_te' ce te te'' te' -> 
      exists mtye' : mty_ext, mtype_build_mtye mtype_build_mtye' ce te ty vds mde' mtye'.
    intros; inversion H0; subst; destruct mde'.
    destruct (H _ _ _ _ ty vds m H1) as [mtye' build_mtye'].
    destruct (build_fresh_tot tys ty (map (fun vd' : VD => match vd' with | vd ty0 _ => ty0 end) vds) 
      (Extract_TyVar typs) t) as [fresh_tys build_fresh'].
    assert (forall fresh_tys' t', exists ZQs', zip fresh_tys (map (fun typ' : GTy * N => N_Trans t'
      (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys') (snd typ')) t) (fun x : TX => pair (TyVar x)) = 
    Some ZQs') by 
    (generalize t (build_fresh_len _ _ _ _ _ _ build_fresh'); clear; induction fresh_tys; destruct t;
      simpl; intros; try discriminate; try (exists nil; reflexivity);
        injection H; intros H0; destruct (IHfresh_tys _ H0 fresh_tys' t') as [ZQs' eq_ZQs'];
          rewrite eq_ZQs'; eexists _; reflexivity).
    destruct (H3 fresh_tys t) as [ZQs' eq_ZQs'].
    exists (Typs_Trans typs tys ZQs', mtye'); econstructor; try eassumption.
  Qed.

  Lemma mtype_build_tys_tot
    (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
    (mtype_build_tys' : cld_def_ext -> ty_def_ext -> Ty -> list VD -> md_def_ext -> list Ty -> list Ty -> Prop) 
    (H : forall ce te te' te'' ty vds md tys, 
      build_te' ce te te'' te' -> exists tys' , mtype_build_tys' ce te ty vds md tys tys') :
    forall ce te te' te'' (ty : Ty) vds md tys, 
      GJ_build_te build_te' ce te te'' te' -> 
      exists tys' : list Ty, mtype_build_tys mtype_build_tys' ce te ty vds md tys tys'.
    intros; inversion H0; subst; destruct md.
    destruct (H _ _ _ _ ty vds m tys H1) as [mtye' build_mtye'].
    destruct (build_fresh_tot tys0 ty (map (fun vd' : VD => match vd' with | vd ty0 _ => ty0 end) vds) 
      (Extract_TyVar typs) t) as [fresh_tys build_fresh'].
    assert (forall fresh_tys' t', exists ZQs', zip fresh_tys (map (fun typ' : GTy * N => N_Trans t'
      (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys') (snd typ')) t) (fun x : TX => pair (TyVar x)) = 
    Some ZQs') by 
    (generalize t (build_fresh_len _ _ _ _ _ _ build_fresh'); clear; induction fresh_tys; destruct t;
      simpl; intros; try discriminate; try (exists nil; reflexivity);
        injection H; intros H0; destruct (IHfresh_tys _ H0 fresh_tys' t') as [ZQs' eq_ZQs'];
          rewrite eq_ZQs'; eexists _; reflexivity).
    destruct (H3 fresh_tys t) as [ZQs' eq_ZQs'].
    eexists _; econstructor; try eassumption.
  Qed.

  Variable build_te_build_mtye_te'' : forall ce te te' te'', 
    build_te ce te te' te'' -> mtype_build_te'' ce te te' te''.
  
  Lemma build_te_build_ty_0_id : forall (ce : cld_ext) (c : _) 
    (d : cFJ.CL _) te te' te'' te''' te4 (delta : Context),
    build_te ce te te4 te' ->
    WF_mtype_ty_0_map delta (FJ_Ty_Wrap (ty_def _ _ te' d)) (FJ_Ty_Wrap (ty_def _ _ te''' d)) ->
    WF_mtype_ty_0_map delta (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) (FJ_Ty_Wrap (ty_def _ _ te'' (cl _ c))) ->
    mtype_build_te'' ce te'' te4 te'''.
    intros.
    generalize (WF_mtype_ty_0_map_id _ _ _ _ H0 (WF_mtype_ty_0_map_refl _ _)).
    generalize (WF_mtype_ty_0_map_id _ _ _ _ H1 (WF_mtype_ty_0_map_refl _ _)).
    intros; apply FJ_Ty_Wrap_inject in H2; apply FJ_Ty_Wrap_inject in H3; injection H2; injection H3; 
      intros; subst.
    apply build_te_build_mtye_te''; auto.
  Qed.

  Lemma GJ_build_te_build_mtye_te'' 
    (build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop) 
    (H : forall ce te te' te'', build_te' ce te te' te'' -> mtype_build_te' ce te te' te''): 
    forall ce te te' te'', GJ_build_te build_te' ce te te' te'' -> mtype_build_te mtype_build_te' ce te te' te''.
    intros; inversion H0; subst; constructor; auto.
  Qed.

  Lemma FJ_build_te_build_mtye_te'' : forall (ce : FJ_cld_ext) (te te' te'' : FJ_ty_ext),
    FJ_build_te ce te te' te'' -> FJ_mtype_build_te ce te te' te''.
    intros; inversion H; subst; constructor.
  Qed.

  Definition Weaken_subtype_app_TList_P delta S T (sub_S_T : subtype delta S T) :=
    forall XNs YOs, delta = (update_Tlist Empty XNs) -> subtype (update_Tlist Empty (XNs ++ YOs)) S T.
  
  Lemma FJ_Weaken_subtype_app_TList
    (Weakening_rect : forall delta S T sub_S_T, Weaken_subtype_app_TList_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Weaken_subtype_app_TList_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Weaken_subtype_app_TList_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    apply Weakening_rect; auto.
  Defined.

  Lemma TLookup_app_TList : forall XNs YOs x ty, 
    TLookup (update_Tlist Empty XNs) x ty -> TLookup (update_Tlist Empty (XNs ++ YOs)) x ty.
    intros; generalize TLookup_Empty TX_eq_dec TLookup_TUpdate_eq TLookup_TUpdate_neq 
      TLookup_TUpdate_neq' TLookup_id H; clear; induction XNs; simpl; intros.
    elimtype False; apply (TLookup_Empty _ _ H). 
    destruct a; destruct g; destruct (TX_eq_dec x t); subst.
    rewrite (TLookup_id _ _ _ _ H (TLookup_TUpdate_eq _ _ _)); apply TLookup_TUpdate_eq.
    apply TLookup_TUpdate_neq; auto; apply IHXNs; try assumption.
    eapply TLookup_TUpdate_neq'; eassumption.    
  Qed.

  Lemma GJ_Weaken_subtype_app_TList : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Weaken_subtype_app_TList_P _ _ _ sub_S_T.
    unfold Weaken_subtype_app_TList_P; intros; apply subtype_Wrap;
      inversion sub_S_T; subst; constructor; auto.
    apply TLookup_app_TList; auto.
  Qed.
    
  Variable (Weaken_subtype_app_TList : forall delta S T sub_S_T, Weaken_subtype_app_TList_P delta S T sub_S_T).

  Definition Weaken_WF_Type_app_TList_P delta S (WF_S : WF_Type delta S) :=
    forall XNs YOs, delta = update_Tlist Empty XNs -> WF_Type (update_Tlist Empty (XNs ++ YOs)) S.

  Definition Weaken_WF_Type_app_TList_Q delta cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext delta cld te) :=
    forall XNs YOs, delta = update_Tlist Empty XNs -> GJ_wf_class_ext (update_Tlist Empty (XNs ++ YOs)) cld te.
  
  Definition Weaken_WF_Type_app_TList_P1 delta Ss (WF_Ss : List_P1 (WF_Type delta) Ss) :=
    forall XNs YOs, delta = update_Tlist Empty XNs -> List_P1 (WF_Type (update_Tlist Empty (XNs ++ YOs))) Ss.

  Lemma Weaken_WF_Type_app_TList_ext_H1 : forall gamma ce tys typs te P1 len P2, 
    Weaken_WF_Type_app_TList_P1 gamma tys P1 -> 
    Weaken_WF_Type_app_TList_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold Weaken_WF_Type_app_TList_P1; unfold Weaken_WF_Type_app_TList_Q; intros; subst.
    constructor; auto.
    assert (exists tys', tys' = (map (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys) typs)) 
      as tys'_eq by (eexists _; reflexivity); destruct tys'_eq as [tys' tys'_eq]; rewrite <- tys'_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in P2; generalize tys' Weaken_subtype_app_TList P2; clear; 
      induction tys; intros;
      inversion P2; subst; constructor.
    eapply Weaken_subtype_app_TList; eauto.
    inversion P2; subst; eauto.
  Qed.    

  Lemma Weaken_WF_Type_app_TList_ext_H2 : forall gamma, 
    Weaken_WF_Type_app_TList_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Weaken_WF_Type_app_TList_P1; intros; constructor.
  Qed.
    
  Lemma Weaken_WF_Type_app_TList_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Weaken_WF_Type_app_TList_P _ _ P_ty -> Weaken_WF_Type_app_TList_P1 _ tys P_tys -> 
    Weaken_WF_Type_app_TList_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Weaken_WF_Type_app_TList_P; unfold Weaken_WF_Type_app_TList_P1; intros;
      constructor; eauto.
  Qed.

  Definition Weaken_WF_Type_app_TList_ext := 
    wf_class_ext_rect Weaken_WF_Type_app_TList_P Weaken_WF_Type_app_TList_Q Weaken_WF_Type_app_TList_P1
    Weaken_WF_Type_app_TList_ext_H1 Weaken_WF_Type_app_TList_ext_H2 Weaken_WF_Type_app_TList_ext_H3.
 
  Lemma Weaken_WF_Type_app_TList_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext),
    GJ_wf_object_ext delta te ->
    forall XNs YOs, delta = update_Tlist Empty XNs -> GJ_wf_object_ext (update_Tlist Empty (XNs ++ YOs)) te.
    intros; inversion H; subst; constructor.
  Qed.
  
  Variable Weaken_wf_object_ext_app_TList : forall delta te (wf_cld : wf_object_ext' delta te), 
    forall XNs YOs, delta = update_Tlist Empty XNs -> wf_object_ext' (update_Tlist Empty (XNs ++ YOs)) te.

  Definition Weaken_WF_Type_app_TList_Q' delta cld te 
    (wf_cld : wf_class_ext' delta cld te) :=
    forall XNs YOs, delta = update_Tlist Empty XNs -> wf_class_ext' (update_Tlist Empty (XNs ++ YOs)) cld te.

  Lemma FJ_Weaken_WF_Type_app_TList_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Weaken_WF_Type_app_TList_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Weaken_WF_Type_app_TList_P; intros.
    apply FJ_WF_Type_Wrap; econstructor 1; try eassumption.
    eapply Weaken_wf_object_ext_app_TList; eassumption.
  Qed.
    
  Lemma FJ_Weaken_WF_Type_app_TList_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Weaken_WF_Type_app_TList_Q' _ _ _ wf_cld_ext ->
    Weaken_WF_Type_app_TList_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Weaken_WF_Type_app_TList_Q; unfold Weaken_WF_Type_app_TList_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
        
  Lemma GJ_Weaken_WF_Type_app_TList : forall delta S (WF_S : GJ_WF_Type delta S), 
    Weaken_WF_Type_app_TList_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Weaken_WF_Type_app_TList_P; intros; apply GJ_WF_Type_Wrap;
      inversion WF_S; subst; econstructor; apply TLookup_app_TList; eassumption.
  Qed.

  Definition Strengthen_Bound'_P S := forall delta vars S',
      Bound' (update_list delta vars) S S' -> Bound' delta S S'.

  Lemma  FJ_Strengthen_Bound' : forall te c, Strengthen_Bound'_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Strengthen_Bound'_P; intros; apply N_Bound'_invert in H; inversion H; subst.
    apply N_Wrap_inject in H2; injection H2; intros; subst; apply N_Bound'_Wrap; constructor.
  Qed.
  
  Lemma GJ_Strengthen_Bound' : forall Y, Strengthen_Bound'_P (Ty_Wrap (TyVar Y)).
    generalize GJ_Bound'_invert' GJ_Ty_Wrap_inject GJ_Bound'_Wrap; 
      unfold Strengthen_Bound'_P; intros; destruct (GJ_Bound'_invert' _ _ _ H) as [n [T'_eq Bound_Y]].
    inversion Bound_Y; subst. apply GJ_Ty_Wrap_inject in H0;
    injection H0; intros; subst; apply GJ_Bound'_Wrap; constructor. 
    eapply TLookup_Update_list; eassumption.
  Qed.

  Definition Strengthen_Bound''_P S := forall delta vars S',
    Bound' delta S S' -> Bound' (update_list delta vars) S S'.

  Lemma  FJ_Strengthen_Bound'' : forall te c, Strengthen_Bound''_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Strengthen_Bound''_P; intros; apply N_Bound'_invert in H; inversion H; subst.
    apply N_Wrap_inject in H2; injection H2; intros; subst; apply N_Bound'_Wrap; constructor.
  Qed.
  
  Lemma GJ_Strengthen_Bound'' : forall Y, Strengthen_Bound''_P (Ty_Wrap (TyVar Y)).
    generalize GJ_Bound'_invert' GJ_Ty_Wrap_inject GJ_Bound'_Wrap; 
      unfold Strengthen_Bound''_P; intros; destruct (GJ_Bound'_invert' _ _ _ H) as [n [T'_eq Bound_Y]].
    inversion Bound_Y; subst. apply GJ_Ty_Wrap_inject in H0;
    injection H0; intros; subst; apply GJ_Bound'_Wrap; constructor. 
    apply TLookup_Update_list'; assumption.
  Qed.

  Lemma Extract_TyVar_zip : forall (Xs : list _) (Ns : list N) (XNs : list (GTy * N)),
    zip Xs Ns (fun x : _ => pair (TyVar x)) = Some XNs -> Extract_TyVar XNs = Xs.
    clear; induction Xs; destruct Ns; destruct XNs; simpl; intros; try discriminate; auto;
      caseEq (zip Xs Ns (fun x => pair (TyVar x))); intros; rewrite H0 in H; try discriminate.
    injection H; intros; subst; simpl; rewrite (IHXs _ _ H0); reflexivity.
  Qed.

  Lemma GJ_mbody_new_map_TE_Trans : forall (XNs : list (GTy * N)) 
    (Xs : list _) (Ns : list N) (Us : list Ty) (te te' : GTy_ext),
    @zip _ N (GTy * N) Xs Ns (fun x : _ => @pair GTy N (TyVar x)) =
    @Some (list (GTy * N)) XNs -> GJ_mbody_new_map _ XNs Us te te' ->
    te' = GJ_TE_Trans te Xs Us.
    intros; inversion H0; subst; simpl; unfold GJ_TE_Trans; unfold Tys_Trans.
    simpl; rewrite (Extract_TyVar_zip _ _ _ H); reflexivity.
  Qed.

  Definition subtype_update_Tupdate_P delta S T (sub_S_T : subtype delta S T) :=
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      subtype (update_list (update_Tlist gamma XNs) Vars) S T.

  Lemma FJ_subtype_update_Tupdate
    (Weakening_rect : forall delta S T sub_S_T, subtype_update_Tupdate_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    subtype_update_Tupdate_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold subtype_update_Tupdate_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    apply Weakening_rect; auto.
  Defined.

  Lemma TLookup_update_Tupdate : forall gamma XNs Vars x ty, 
    TLookup (update_Tlist (update_list gamma Vars) XNs) x ty -> 
    TLookup (update_list (update_Tlist gamma XNs) Vars) x ty.
    induction XNs; simpl; intros.
    assumption.
    destruct a; destruct g; apply TLookup_Update_list'; destruct (TX_eq_dec x t); subst.
    rewrite (TLookup_id _ _ _ _ H (TLookup_TUpdate_eq _ _ _)); apply TLookup_TUpdate_eq.
    apply TLookup_TUpdate_neq; auto; eapply TLookup_Update_list; apply IHXNs; try assumption.
    eapply TLookup_TUpdate_neq'; eassumption.    
  Qed.

  Lemma GJ_subtype_update_Tupdate : forall delta S T (sub_S_T : GJ_subtype delta S T),
    subtype_update_Tupdate_P _ _ _ sub_S_T.
    unfold subtype_update_Tupdate_P; intros; apply subtype_Wrap; inversion sub_S_T; subst; constructor; auto.
    apply TLookup_update_Tupdate; auto.
  Qed.
    
  Variable (subtype_update_Tupdate : forall delta S T sub_S_T, subtype_update_Tupdate_P delta S T sub_S_T).

  Definition WF_Type_update_Tupdate_P delta S (WF_S : WF_Type delta S) :=
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      WF_Type (update_list (update_Tlist gamma XNs) Vars) S.    

  Definition WF_Type_update_Tupdate_Q delta cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext delta cld te) :=
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      GJ_wf_class_ext (update_list (update_Tlist gamma XNs) Vars) cld te.
  
  Definition WF_Type_update_Tupdate_P1 delta Ss (WF_Ss : List_P1 (WF_Type delta) Ss) :=
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
    List_P1 (WF_Type (update_list (update_Tlist gamma XNs) Vars)) Ss.

  Lemma WF_Type_update_Tupdate_ext_H1 : forall gamma ce tys typs te P1 len P2, 
    WF_Type_update_Tupdate_P1 gamma tys P1 -> 
    WF_Type_update_Tupdate_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold WF_Type_update_Tupdate_P1; unfold WF_Type_update_Tupdate_Q; intros; subst.
    constructor; auto.
    assert (exists tys', tys' = (map (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys) typs)) 
      as tys'_eq by (eexists _; reflexivity); destruct tys'_eq as [tys' tys'_eq]; rewrite <- tys'_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in P2; generalize tys' subtype_update_Tupdate P2; clear; 
      induction tys; intros;
      inversion P2; subst; constructor.
    eapply subtype_update_Tupdate; eauto.
    inversion P2; subst; eauto.
  Qed.    

  Lemma WF_Type_update_Tupdate_ext_H2 : forall gamma, 
    WF_Type_update_Tupdate_P1 gamma _ (Nil (WF_Type gamma)).
    unfold WF_Type_update_Tupdate_P1; intros; constructor.
  Qed.
    
  Lemma WF_Type_update_Tupdate_ext_H3 : forall gamma ty tys P_ty P_tys, 
    WF_Type_update_Tupdate_P _ _ P_ty -> WF_Type_update_Tupdate_P1 _ tys P_tys -> 
    WF_Type_update_Tupdate_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold WF_Type_update_Tupdate_P; unfold WF_Type_update_Tupdate_P1; intros;
      constructor; eauto.
  Qed.

  Definition WF_Type_update_Tupdate_ext := 
    wf_class_ext_rect WF_Type_update_Tupdate_P WF_Type_update_Tupdate_Q WF_Type_update_Tupdate_P1
    WF_Type_update_Tupdate_ext_H1 WF_Type_update_Tupdate_ext_H2 WF_Type_update_Tupdate_ext_H3.

  Variable wf_object_ext_update_Tupdate: forall delta te (wf_cld : wf_object_ext' delta te), 
     forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      wf_object_ext' (update_list (update_Tlist gamma XNs) Vars) te.
  
  Lemma WF_Type_update_Tupdate_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext),
    GJ_wf_object_ext delta te ->
     forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
       GJ_wf_object_ext (update_list (update_Tlist gamma XNs) Vars) te.
    intros; inversion H; subst; constructor.
  Qed.
  
  Lemma FJ_WF_Type_update_Tupdate_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    WF_Type_update_Tupdate_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold WF_Type_update_Tupdate_P; intros.
    apply FJ_WF_Type_Wrap; econstructor 1; try eassumption.
    eapply wf_object_ext_update_Tupdate; eassumption.
  Qed.

  Definition WF_Type_update_Tupdate_Q' delta cld te (wf_cld : wf_class_ext' delta cld te) := 
    forall XNs Vars gamma, delta = update_Tlist (update_list gamma Vars) XNs ->
      wf_class_ext' (update_list (update_Tlist gamma XNs) Vars) cld te.
    
  Lemma FJ_WF_Type_update_Tupdate_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    WF_Type_update_Tupdate_Q' _ _ _ wf_cld_ext -> 
    WF_Type_update_Tupdate_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold WF_Type_update_Tupdate_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
        
  Lemma GJ_WF_Type_update_Tupdate : forall delta S (WF_S : GJ_WF_Type delta S), 
    WF_Type_update_Tupdate_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold WF_Type_update_Tupdate_P; intros; apply GJ_WF_Type_Wrap;
      inversion WF_S; subst; econstructor; apply TLookup_update_Tupdate; eassumption.
  Qed.

  Definition subtype_update_list_id'_P delta S T (sub_S_T : subtype delta S T) :=
    forall Vars, subtype (update_list delta Vars) S T.

  Lemma FJ_subtype_update_list_id'
    (Weakening_rect : forall delta S T sub_S_T, subtype_update_list_id'_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    subtype_update_list_id'_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold subtype_update_list_id'_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    apply Weakening_rect; auto.
  Defined.

  Lemma GJ_subtype_update_list_id' : forall delta S T (sub_S_T : GJ_subtype delta S T),
    subtype_update_list_id'_P _ _ _ sub_S_T.
    unfold subtype_update_list_id'_P; intros; apply subtype_Wrap; inversion sub_S_T; subst; constructor; auto.
    apply TLookup_Update_list'; auto.
  Qed.
    
  Variable (subtype_update_list_id' : forall delta S T sub_S_T, subtype_update_list_id'_P delta S T sub_S_T).

  Definition WF_Type_update_list_id'_P delta S (WF_S : WF_Type delta S) :=
    forall Vars, WF_Type (update_list delta Vars) S.

  Definition WF_Type_update_list_id'_Q delta cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext delta cld te) :=
    forall Vars, GJ_wf_class_ext (update_list delta Vars) cld te.
  
  Definition WF_Type_update_list_id'_P1 delta Ss (WF_Ss : List_P1 (WF_Type delta) Ss) :=
    forall Vars, List_P1 (WF_Type (update_list delta Vars)) Ss.

  Lemma WF_Type_update_list_id'_ext_H1 : forall gamma ce tys typs te P1 len P2, 
    WF_Type_update_list_id'_P1 gamma tys P1 -> 
    WF_Type_update_list_id'_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold WF_Type_update_list_id'_P1; unfold WF_Type_update_list_id'_Q; intros; subst.
    constructor; auto.
    assert (exists tys', tys' = (map (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys) typs)) 
      as tys'_eq by (eexists _; reflexivity); destruct tys'_eq as [tys' tys'_eq]; rewrite <- tys'_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in P2; generalize tys' subtype_update_list_id' P2; clear; 
      induction tys; intros;
      inversion P2; subst; constructor.
    eapply subtype_update_list_id'; eauto.
    inversion P2; subst; eauto.
  Qed.    

  Lemma WF_Type_update_list_id'_ext_H2 : forall gamma, 
    WF_Type_update_list_id'_P1 gamma _ (Nil (WF_Type gamma)).
    unfold WF_Type_update_list_id'_P1; intros; constructor.
  Qed.
    
  Lemma WF_Type_update_list_id'_ext_H3 : forall gamma ty tys P_ty P_tys, 
    WF_Type_update_list_id'_P _ _ P_ty -> WF_Type_update_list_id'_P1 _ tys P_tys -> 
    WF_Type_update_list_id'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold WF_Type_update_list_id'_P; unfold WF_Type_update_list_id'_P1; intros;
      constructor; eauto.
  Qed.

  Definition WF_Type_update_list_id'_ext := 
    wf_class_ext_rect WF_Type_update_list_id'_P WF_Type_update_list_id'_Q WF_Type_update_list_id'_P1
    WF_Type_update_list_id'_ext_H1 WF_Type_update_list_id'_ext_H2 WF_Type_update_list_id'_ext_H3.

  Variable wf_object_ext_update_list_id': forall delta te (wf_cld : wf_object_ext' delta te), 
    forall Vars, wf_object_ext' (update_list delta Vars) te.
  
  Lemma WF_Type_update_list_id'_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext),
    GJ_wf_object_ext delta te ->
    forall Vars, GJ_wf_object_ext (update_list delta Vars) te.
    intros; inversion H; subst; constructor.
  Qed.
  
  Lemma FJ_WF_Type_update_list_id'_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    WF_Type_update_list_id'_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold WF_Type_update_list_id'_P; intros.
    apply FJ_WF_Type_Wrap; econstructor 1; try eassumption.
    eapply wf_object_ext_update_list_id'; eassumption.
  Qed.

  Definition WF_Type_update_list_id'_Q' delta cld te (wf_cld : wf_class_ext' delta cld te) :=
    forall Vars, wf_class_ext' (update_list delta Vars) cld te.
    
  Lemma FJ_WF_Type_update_list_id'_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    WF_Type_update_list_id'_Q' _ _ _ wf_cld_ext -> 
    WF_Type_update_list_id'_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold WF_Type_update_list_id'_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
        
  Lemma GJ_WF_Type_update_list_id' : forall delta S (WF_S : GJ_WF_Type delta S), 
    WF_Type_update_list_id'_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold WF_Type_update_list_id'_P; intros; apply GJ_WF_Type_Wrap;
      inversion WF_S; subst; econstructor; apply TLookup_Update_list'; eassumption.
  Qed.

  Variable (WF_Type_update_list_id' : forall delta S WF_S, WF_Type_update_list_id'_P delta S WF_S).

  Variable WF_mtype_Us_map_update_list : forall gamma vars mce mde tys tys', 
    WF_mtype_Us_map gamma mce mde tys tys' ->
    WF_mtype_Us_map (update_list gamma vars) mce mde tys tys'.
  Variable WF_mtype_U_map_update_list : forall gamma vars mce mde ty ty', 
    WF_mtype_U_map gamma mce mde ty ty' ->
    WF_mtype_U_map (update_list gamma vars) mce mde ty ty'.
  Variable WF_mtype_ext_update_list : forall gamma vars mce mde, 
    WF_mtype_ext gamma mce mde -> WF_mtype_ext (update_list gamma vars) mce mde.

  Lemma GJ_WF_mtype_Us_map_update_list : forall gamma vars mce mde tys tys', 
    GJ_WF_mtype_Us_map m_call_ext mty_def_ext WF_mtype_Us_map gamma mce mde tys tys' ->
    GJ_WF_mtype_Us_map m_call_ext mty_def_ext WF_mtype_Us_map (update_list gamma vars) mce mde tys tys'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma GJ_WF_mtype_U_map_update_list : forall gamma vars mce mde ty ty', 
    GJ_WF_mtype_U_map m_call_ext mty_def_ext WF_mtype_U_map gamma mce mde ty ty' ->
    GJ_WF_mtype_U_map m_call_ext mty_def_ext WF_mtype_U_map (update_list gamma vars) mce mde ty ty'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma GJ_WF_mtype_ext_update_list : forall gamma vars mce mde, 
    GJ_WF_mtype_ext m_call_ext mty_def_ext WF_mtype_ext gamma mce mde ->
    GJ_WF_mtype_ext m_call_ext mty_def_ext WF_mtype_ext (update_list gamma vars) mce mde.
    unfold GJ_WF_mtype_ext; intros; destruct mce; destruct mde; destruct H as [H1 [H2 H3]]; split; try split; auto.
    generalize WF_Type_update_list_id' H2; clear; induction l; intros; constructor; inversion H2; subst; auto;
      eapply WF_Type_update_list_id'; assumption.
    assert (exists tys, tys = (Tys_Trans t l (map (fun yo : GTy * N => N_Wrap (snd yo)) t))) as tys_eq by 
      (eexists _; reflexivity); destruct tys_eq as [tys tys_eq]; rewrite <- tys_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in H3.
    generalize l subtype_update_list_id' H3; clear; induction tys; intros; inversion H3; subst; constructor.
    intros; eapply subtype_update_list_id'; assumption.
    auto.
  Qed.

  Lemma FJ_WF_mtype_Us_map_update_list : forall gamma vars mce mde tys tys', 
    FJ_WF_mtype_Us_map Ty Context gamma mce mde tys tys' ->
    FJ_WF_mtype_Us_map _ _ (update_list gamma vars) mce mde tys tys'.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Lemma FJ_WF_mtype_U_map_update_list : forall gamma vars mce mde ty ty', 
    FJ_WF_mtype_U_map Ty Context gamma mce mde ty ty' ->
    FJ_WF_mtype_U_map _ _ (update_list gamma vars) mce mde ty ty'.
    intros; inversion H; subst; constructor; auto.
  Qed.
  
  Lemma FJ_WF_mtype_ext_update_list : forall gamma vars mce mde, 
    FJ_WF_mtype_ext Context gamma mce mde ->
    FJ_WF_mtype_ext _ (update_list gamma vars) mce mde.
    intros; inversion H; subst; constructor; auto.
  Qed.

  Definition Trans_Bound'_P T := forall (delta delta' : Context) 
    (T' : Ty) (Xs : list _) (Us : list Ty),
    Bound' delta T T' -> Bound' delta' (Ty_trans T' Xs Us) (Ty_trans T' Xs Us).

  Lemma FJ_Trans_Bound' : forall T, Trans_Bound'_P (FJ_Ty_Wrap T).
    unfold Trans_Bound'_P; intros; apply N_Bound'_invert in H; 
      inversion H; subst; apply N_Wrap_inject in H2; injection H2; intros; subst.
    fold (FJ_Ty_Wrap T); rewrite FJ_Ty_trans_invert; destruct T; simpl; 
      apply N_Bound'_Wrap; constructor.
  Qed.

  Lemma GJ_Trans_Bound' : forall T, Trans_Bound'_P (Ty_Wrap T).
    unfold Trans_Bound'_P; intros; destruct (GJ_Bound'_invert' _ _ _ H) as [n [T'_eq Bound_Y]];
      subst.
    inversion Bound_Y; subst.
    apply GJ_Ty_Wrap_inject in H0; injection H0; intros; subst; clear H1.
    rewrite <- Ty_trans_eq_NTy_trans; apply N_Bound'_Wrap; econstructor.
  Qed.

  Variable Trans_Bound' : forall T, Trans_Bound'_P T.

  Definition Bound'_id_P ty := forall delta S T, Bound' delta ty S -> Bound' delta ty T -> S = T.
  
  Lemma FJ_Bound'_id : forall T, Bound'_id_P (FJ_Ty_Wrap T).
    unfold Bound'_id_P; intros; apply N_Bound'_invert in H; inversion H; 
      apply N_Bound'_invert in H0; inversion H0; subst.
    apply N_Wrap_inject in H3; injection H3; apply N_Wrap_inject in H6; injection H6; 
      intros; subst; reflexivity.
  Qed.
    
  Lemma GJ_Bound'_id : forall S, Bound'_id_P (Ty_Wrap S).
    unfold Bound'_id_P; intros; destruct (GJ_Bound'_invert' _ _ _ H) as [n [T'_eq Bound_Y]];
      destruct (GJ_Bound'_invert' _ _ _ H0) as [n' [T'_eq' Bound_Y']]; subst.
    inversion Bound_Y; inversion Bound_Y'; subst.
    apply GJ_Ty_Wrap_inject in H1; apply GJ_Ty_Wrap_inject in H5; injection H1; injection H5; 
      intros; subst; injection H2; intros; subst; rewrite (TLookup_id _ _ _ _ H3 H7);
        reflexivity.
  Qed.

  Variable Bound'_id : forall T, Bound'_id_P T.

  Definition sub_Bound'_P delta S T (sub_S_T : subtype delta S T) :=
    forall S' T', Bound' delta T T' -> Bound' delta S S' -> subtype delta S' T'.
    
  Lemma FJ_sub_Bound' (Weakening_rect : forall delta S T sub_S_T, sub_Bound'_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
      sub_Bound'_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; try assumption; clear Weakening_rect;
      unfold sub_Bound'_P; intros; subst.
    rewrite (Bound'_id _ _ _ _ H H0); apply FJ_subtype_Wrap; constructor.
    destruct (Bound_total _ _ _ sub_d _ H1) as [d' Bound_d].
    apply FJ_subtype_Wrap; constructor 2 with (d := d'); eauto.
    apply N_Bound'_invert in H; apply N_Bound'_invert in H0; inversion H; inversion H0;
      subst; apply N_Wrap_inject in H3; apply N_Wrap_inject in H6; injection H3; injection H6;
        intros; subst.
    fold (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))); fold (FJ_Ty_Wrap (ty_def C ty_ext te' d));
      apply FJ_subtype_Wrap; econstructor 3; eassumption.
  Defined.
  
  Lemma GJ_sub_Bound' : forall delta S T (sub_S_T : GJ_subtype delta S T),
    sub_Bound'_P _ _ _ sub_S_T.
    unfold sub_Bound'_P; intros; inversion sub_S_T; subst.
    destruct (GJ_Bound'_invert' _ _ _ H0) as [n [T'_eq Bound_Y]];
      apply N_Bound'_invert in H; inversion H; subst; apply N_Wrap_inject in H4;
        inversion Bound_Y; subst; apply GJ_Ty_Wrap_inject in H2;
          injection H2; intros; subst; rewrite (TLookup_id _ _ _ _ H1 H5).
    apply FJ_subtype_Wrap; constructor.
  Defined.
  
  Variable sub_Bound' : forall delta S T sub_S_T, sub_Bound'_P delta S T sub_S_T.

  Definition Lem_2_7''_P T := forall (delta delta_1 : Context) (Xs : list TX) (Ns : list N)
    (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) T',
    length Xs = length Us ->
    zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
    delta = (update_Tlist (update_list Empty vars) XNs) ->
    List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) ->
    List_P1 (WF_Type delta_1) Us ->
    List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
    Bound' (update_Tlist (update_list Empty vars) XNs) T T' ->
    exists T'', Bound' delta_1 (Ty_trans T Xs Us) T'' /\
      subtype delta_1 T'' (Ty_trans T' Xs Us).

  Lemma FJ_Lem_2_7'' : forall T, Lem_2_7''_P (FJ_Ty_Wrap T).
    unfold Lem_2_7''_P; intros.
    apply N_Bound'_invert in H5; inversion H5; subst.
    apply N_Wrap_inject in H8; injection H8; intros; subst.
    fold (FJ_Ty_Wrap T); destruct T; repeat rewrite FJ_Ty_trans_invert.
    unfold FJ_Ty_Wrap; eexists _; split.
    apply N_Bound'_Wrap; constructor.
    apply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma GJ_Lem_2_7'' : forall T, Lem_2_7''_P (Ty_Wrap T).
    unfold Lem_2_7''_P; intros; destruct (GJ_Bound'_invert' _ _ _ H5) as [n [T'_eq Bound_Y]];
      subst.
    inversion Bound_Y; subst.
    apply TLookup_update_Tupdate in H7; apply TLookup_Update_list in H7.
    apply GJ_Ty_Wrap_inject in H1; injection H1; intros; subst; clear H6.
    assert (exists n', exists U, nth_error Us n' = Some U /\ Ty_trans (Ty_Wrap (TyVar x)) Xs Us = U
      /\ nth_error Ns n' = Some n) as ex_n.
    generalize Xs Ns Us H0 H7 TLookup_Empty TLookup_TUpdate_eq TLookup_TUpdate_neq GJ_Ty_trans_invert
        TLookup_TUpdate_neq' TX_eq_dec TLookup_id (length_List_P2 _ _ _ _ _ H2); clear; induction XNs; 
          simpl; intros.
    elimtype False; eapply TLookup_Empty; eassumption.
    destruct Xs; destruct Ns; destruct Us; simpl in *|-*; try discriminate;
      destruct a; destruct g; simpl in *|-*; destruct (TX_eq_dec t x); subst.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); intros; rewrite H1 in H0; 
      try discriminate; injection H0; intros; subst; clear H0.
    exists 0; exists t0; repeat split.
    auto; rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec t1 t1); congruence.
    rewrite (TLookup_id _ _ _ _ H7 (TLookup_TUpdate_eq _ _ _)); reflexivity.
    caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); intros; rewrite H1 in H0; 
      try discriminate; injection H0; intros; subst; clear H0.
    injection H; intros; destruct (IHXNs _ _ Us H1) as [n' [U' [nth_Us [Trans_x nth_Ns]]]]; 
      try assumption; try eapply TLookup_TUpdate_neq'; eauto.
    exists (S n'); exists U'; repeat split; auto; rewrite GJ_Ty_trans_invert; simpl;
      destruct (TX_eq_dec t1 x); congruence.
    destruct ex_n as [n' [U' [nth_Us [Trans_x nth_Ns]]]].
    generalize (Trans_Bound' _ _ delta_1 _ Xs Us H5); intros Bound'_n.
    destruct H2 as [In_Us _]; destruct (In_Us _ _ nth_Us) as [N' [nth_N' sub_U]].
    rewrite nth_Ns in nth_N'; injection nth_N'; intros; subst.
    destruct (Bound_total _ _ _ sub_U _ Bound'_n) as [x' Bound_x].
    exists x'; split; auto.
    eapply sub_Bound'; eassumption.
  Qed.

  Lemma FJ_build_context'_Empty_1 : forall ce me vds gamma XNs T,
    FJ_Meth_build_context _ ce me (update_list Empty vds) gamma -> 
    WF_Type (update_Tlist gamma XNs) T -> 
    WF_Type (update_Tlist (update_list Empty vds) XNs) T.
    intros; inversion H; subst; auto.
  Qed.

  Lemma FJ_build_context'_Empty_2 : forall ce me vds gamma XNs S T,
    FJ_Meth_build_context _ ce me (update_list Empty vds) gamma -> 
    subtype (update_Tlist gamma XNs) S T -> 
    subtype (update_Tlist (update_list Empty vds) XNs) S T.
    intros; inversion H; subst; auto.
  Qed.

  Lemma FJ_build_context'_Empty_3 : forall ce me vds gamma XNs e T,
    FJ_Meth_build_context _ ce me (update_list Empty vds) gamma -> 
    E_WF (update_Tlist gamma XNs) e T -> 
    E_WF (update_Tlist (update_list Empty vds) XNs) e T.
    intros; inversion H; subst; auto.
  Qed.

  Lemma FJ_WF_mtype_U_map'_id : forall delta mce mtye ty ty', 
    FJ_WF_mtype_U_map Ty Context delta mce mtye ty ty' -> ty = ty'.
    intros; inversion H; subst; reflexivity.
  Qed.

  Lemma FJ_WF_mtype_Us_map'_id : forall delta mce mtye tys tys', 
    FJ_WF_mtype_Us_map Ty Context delta mce mtye tys tys' -> tys = tys'.
    intros; inversion H; subst; reflexivity.
  Qed.

  Lemma FJ_mtype_build_tys'_id : forall ce te T vds mde tys tys',
    FJ_mtype_build_tys X Ty ce te T vds mde tys tys' -> tys = tys'.
    intros; inversion H; subst; reflexivity.
  Qed.

  Definition Ty_trans_app_P (S : Ty) := forall Xs Ys Ts Vs Zs, 
    length Xs = length Ts -> Free_Vars S Zs -> (forall Z, In Z Zs -> In Z Xs) -> 
    Ty_trans S Xs Ts = Ty_trans S (Xs ++ Ys) (Ts ++ Vs).
  
  Definition TE_trans_app_Q te := forall (Xs Ys : list _) (Ts Vs : list Ty) (Zs : list _),
    length Xs = length Ts -> TE_Free_Vars te Zs -> (forall Y : _, In Y Zs -> In Y Xs) ->
    TE_trans te Xs Ts = TE_trans te (Xs ++ Ys) (Ts ++ Vs).

  Lemma FJ_Ty_trans_app te c : TE_trans_app_Q te -> Ty_trans_app_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_app_P; unfold TE_trans_app_Q; intros.
    apply FJ_Free_Vars_invert in H1; inversion H1; subst.
    repeat rewrite FJ_Ty_trans_invert; simpl.
    apply FJ_Ty_Wrap_inject in H3; injection H3; intros; subst; rewrite (H _ Ys _ Vs _ H0 H4); auto.
  Qed.

  Lemma GJ_Ty_trans_app X' : Ty_trans_app_P (Ty_Wrap (TyVar X')).
    unfold Ty_trans_app_P; intros; apply GJ_Free_Vars_invert in H0; inversion H0; 
      subst; apply GJ_Ty_Wrap_inject in H3; injection H3; intros; subst; clear H3.
    repeat rewrite GJ_Ty_trans_invert; generalize Ts H (H1 _ (or_introl _ (refl_equal _))); clear;
      induction Xs; simpl; intros; destruct H0; destruct Ts; destruct Vs; simpl; subst;
        try (destruct (TX_eq_dec X' X'); congruence); try (elimtype False; assumption);
          simpl in H; try discriminate; injection H; intros.
    destruct (TX_eq_dec a X'); simpl; auto.
    destruct (TX_eq_dec a X'); simpl; auto.
  Qed.

  Lemma TE_trans_app_H1 te' : forall (Xs Ys : list _) (Ts Vs : list Ty) (Zs : list _),
    length Xs = length Ts -> GJ_TE_Free_Vars (nil, te') Zs -> (forall Y : _, In Y Zs -> In Y Xs) ->
    GJ_TE_Trans (nil, te') Xs Ts = GJ_TE_Trans (nil, te') (Xs ++ Ys) (Ts ++ Vs).
    unfold GJ_TE_Trans; simpl; reflexivity.
  Qed.
  
  Lemma TE_trans_app_H2 ty tys te' : 
    (forall Xs Ys Ts Vs Zs, length Xs = length Ts -> GJ_TE_Free_Vars (tys, te') Zs -> 
      (forall Y : _, In Y Zs -> In Y Xs) ->
      GJ_TE_Trans (tys, te') Xs Ts = GJ_TE_Trans (tys, te') (Xs ++ Ys) (Ts ++ Vs)) -> 
    Ty_trans_app_P ty -> 
    forall (Xs Ys : list _) (Ts Vs : list Ty) (Zs : list _),
    length Xs = length Ts -> GJ_TE_Free_Vars (ty :: tys, te') Zs -> (forall Y : _, In Y Zs -> In Y Xs) ->
    GJ_TE_Trans (ty :: tys, te') Xs Ts = GJ_TE_Trans (ty :: tys, te') (Xs ++ Ys) (Ts ++ Vs).
    unfold GJ_TE_Trans; unfold Ty_trans_app_P; simpl; intros.
    inversion H2; apply P2_if_P2' in H7; inversion H7; subst.
    rewrite <- (H0 _ _ _ _ _ H1 H10).
    assert (GJ_TE_Free_Vars (tys, te') (fold_right (@app _) nil Bs)) as FV_tys by 
      (constructor; apply P2'_if_P2; assumption); 
      assert (forall Y, In Y (fold_right (@app _) nil Bs) -> In Y Xs) as Bound_Bs by 
        (intros; apply H3; auto; apply in_or_app; right; assumption); 
        generalize (H _ Ys _ Vs _ H1 FV_tys Bound_Bs);
          intros eq_tys; injection eq_tys; intros; subst.
    rewrite H4; reflexivity.
    intros; apply H3; auto; apply in_or_app; left; assumption.
    Qed.

  Variable Ty_trans_app : forall S, Ty_trans_app_P S.
  Variable TE_trans_app : forall te, TE_trans_app_Q te.

  Variable WF_Type_update_Tupdate : forall gamma S WF_S, WF_Type_update_Tupdate_P gamma S WF_S.

  Definition Strengthen_subtype_update_TList_P delta S T (sub_S_T : subtype delta S T) :=
    forall gamma Vars, delta = update_list gamma Vars -> subtype gamma S T.

  Lemma FJ_Strengthen_subtype_update_TList
    (Weakening_rect : forall delta S T sub_S_T, Strengthen_subtype_update_TList_P delta S T sub_S_T) :
    forall delta S T (sub_S_T : FJ_subtype delta S T),
    Strengthen_subtype_update_TList_P delta S T (FJ_subtype_Wrap _ _ _ sub_S_T).
    intros; eapply FJ_subtype_rect; unfold Strengthen_subtype_update_TList_P.
    intros; eapply FJ_subtype_Wrap; constructor.
    intros; eapply FJ_subtype_Wrap; econstructor; eauto.
    intros; eapply FJ_subtype_Wrap; econstructor 3; eauto.
    apply Weakening_rect; auto.
  Defined.

  Lemma GJ_Strengthen_subtype_update_TList : forall delta S T (sub_S_T : GJ_subtype delta S T),
    Strengthen_subtype_update_TList_P _ _ _ sub_S_T.
    unfold Strengthen_subtype_update_TList_P; intros; apply subtype_Wrap; 
      inversion sub_S_T; subst; constructor; auto; eapply TLookup_Update_list; eauto.
  Qed.
    
  Variable (Strengthen_subtype_update_TList : forall delta S T sub_S_T, 
    Strengthen_subtype_update_TList_P delta S T sub_S_T).

  Definition Strengthen_WF_Type_update_TList_P delta S (WF_S : WF_Type delta S) :=
    forall gamma Vars, delta = update_list gamma Vars -> WF_Type gamma S.

  Definition Strengthen_WF_Type_update_TList_Q delta cld te 
    (wf_cld : @GJ_wf_class_ext cld_def_ext ty_def_ext delta cld te) :=
    forall gamma Vars, delta = update_list gamma Vars -> GJ_wf_class_ext gamma cld te.
  
  Definition Strengthen_WF_Type_update_TList_P1 delta Ss (WF_Ss : List_P1 (WF_Type delta) Ss) :=
    forall gamma Vars, delta = update_list gamma Vars -> List_P1 (WF_Type gamma) Ss.

  Lemma Strengthen_WF_Type_update_TList_ext_H1 : forall gamma ce tys typs te P1 len P2, 
    Strengthen_WF_Type_update_TList_P1 gamma tys P1 -> 
    Strengthen_WF_Type_update_TList_Q _ _ _ (@wf_class_ext cld_def_ext ty_def_ext 
      ce gamma typs tys te P1 len P2).
    unfold Strengthen_WF_Type_update_TList_P1; unfold Strengthen_WF_Type_update_TList_Q; intros; subst.
    constructor; eauto.
    assert (exists tys', tys' = (map (fun typ' : GTy * N => Ty_trans (snd typ') (Extract_TyVar typs) tys) typs)) 
      as tys'_eq by (eexists _; reflexivity); destruct tys'_eq as [tys' tys'_eq]; rewrite <- tys'_eq in *|-*.
    apply P2'_if_P2; apply P2_if_P2' in P2; generalize tys' Strengthen_subtype_update_TList P2; clear; 
      induction tys; intros;
      inversion P2; subst; constructor.
    eapply Strengthen_subtype_update_TList; eauto.
    inversion P2; subst; eauto.
  Qed.    

  Lemma Strengthen_WF_Type_update_TList_ext_H2 : forall gamma, 
    Strengthen_WF_Type_update_TList_P1 gamma _ (Nil (WF_Type gamma)).
    unfold Strengthen_WF_Type_update_TList_P1; intros; constructor.
  Qed.
    
  Lemma Strengthen_WF_Type_update_TList_ext_H3 : forall gamma ty tys P_ty P_tys, 
    Strengthen_WF_Type_update_TList_P _ _ P_ty -> Strengthen_WF_Type_update_TList_P1 _ tys P_tys -> 
    Strengthen_WF_Type_update_TList_P1 gamma _ (Cons_a _ ty tys P_ty P_tys).
    unfold Strengthen_WF_Type_update_TList_P; unfold Strengthen_WF_Type_update_TList_P1; intros;
      constructor; eauto.
  Qed.

  Definition Strengthen_WF_Type_update_TList_ext := 
    wf_class_ext_rect Strengthen_WF_Type_update_TList_P Strengthen_WF_Type_update_TList_Q 
    Strengthen_WF_Type_update_TList_P1 Strengthen_WF_Type_update_TList_ext_H1 
    Strengthen_WF_Type_update_TList_ext_H2 Strengthen_WF_Type_update_TList_ext_H3.

  Variable Strengthen_wf_object_ext_update_TList : forall delta te (wf_cld : wf_object_ext' delta te), 
    forall gamma Vars, delta = update_list gamma Vars -> wf_object_ext' gamma te.
  
  Lemma Strengthen_WF_Type_update_TList_obj_ext : forall (delta : Context) (te : @GTy_ext ty_def_ext),
    GJ_wf_object_ext delta te ->
    forall gamma Vars, delta = update_list gamma Vars -> GJ_wf_object_ext gamma te.
    intros; inversion H; subst; constructor.
  Qed.
  
  Lemma FJ_Strengthen_WF_Type_update_TList_H1 : forall (gamma : Context) (te : ty_ext)
    (wf_obj : wf_object_ext' gamma te),
    Strengthen_WF_Type_update_TList_P gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (Object C)))
      (WF_Obj C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT Context
        wf_class_ext' wf_object_ext' gamma te wf_obj)).
    unfold Strengthen_WF_Type_update_TList_P; intros.
    apply FJ_WF_Type_Wrap; econstructor 1; try eassumption.
    eapply Strengthen_wf_object_ext_update_TList; eassumption.
  Qed.

  Definition Strengthen_WF_Type_update_TList_Q' delta cld te (wf_cld : wf_class_ext' delta cld te) :=
    forall gamma Vars, delta = update_list gamma Vars -> wf_class_ext' gamma cld te.

  Lemma FJ_Strengthen_WF_Type_update_TList_H2 : forall (gamma : Context) (c : C)
    (cld : cFJ.L C F M X ty_ext Ty E md_ext cld_ext)
    (te : ty_ext) (CT_c : CT c = Some cld)
    (wf_cld_ext : wf_class_ext' gamma (cld_ce cld) te),
    Strengthen_WF_Type_update_TList_Q' _ _ _ wf_cld_ext -> 
    Strengthen_WF_Type_update_TList_P gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
    (FJ_WF_Type_Wrap gamma (FJ_Ty_Wrap (ty_def C _ te (cl C c)))
      (WF_Class C F M X _ Ty FJ_Ty_Wrap E md_ext cld_ext CT
        Context wf_class_ext' wf_object_ext' gamma c cld te CT_c
        wf_cld_ext)).
    unfold Strengthen_WF_Type_update_TList_P; intros.
    apply FJ_WF_Type_Wrap; econstructor; eauto.
  Qed.
        
  Lemma GJ_Strengthen_WF_Type_update_TList : forall delta S (WF_S : GJ_WF_Type delta S), 
    Strengthen_WF_Type_update_TList_P delta S (GJ_WF_Type_Wrap _ _ WF_S).
    unfold Strengthen_WF_Type_update_TList_P; intros; apply GJ_WF_Type_Wrap;
      inversion WF_S; subst; econstructor; eapply TLookup_Update_list; eassumption.
  Qed.

  Variable Strengthen_WF_Type_update_TList : forall delta S WF_S, Strengthen_WF_Type_update_TList_P delta S WF_S.

  Lemma GJ_map_Ty_trans_Q : forall te Xs Ys Us tys typs,
    GJ_TE_Free_Vars te Ys -> length typs = length tys -> 
    (forall X, In X Ys -> In X (Extract_TyVar typs)) ->
    GJ_TE_Trans (GJ_TE_Trans te (Extract_TyVar typs) tys) Xs Us =
    GJ_TE_Trans te (Extract_TyVar  typs) (map (fun ty0 : Ty => Ty_trans ty0 Xs Us) tys).
    destruct te; induction l; intros.
    eapply map_Ty_trans'_H3; try eassumption.
    eapply GJ_TE_Free_Vars_Wrap; apply H.
    eapply map_Ty_trans'_H4; try eassumption.
    unfold map_Ty_trans_Q'; intros.
    repeat rewrite GJ_TE_Trans_invert.
    erewrite IHl; eauto.
    apply map_Ty_trans'.
    eapply GJ_TE_Free_Vars_Wrap; apply H.
  Qed.

  Lemma GJ_wf_free_vars' : forall gamma tys (P1 : List_P1 (WF_Type gamma) tys),
    forall XNs Xs, gamma = (update_Tlist Empty XNs) -> List_P2 tys Xs Free_Vars ->
      forall X, In X (fold_right (@app _) nil Xs) -> In X (Extract_TyVar  XNs).
    subst; induction tys; intros; apply P2_if_P2' in H0; inversion H0; subst;
      simpl in H1.
    destruct H1.
    apply in_app_or in H1; destruct H1.
    inversion P1; subst; eapply wf_free_vars; try eassumption; reflexivity.
    inversion P1; subst.
    eapply IHtys; try eassumption.
    reflexivity.
    apply P2'_if_P2; assumption.
  Qed.
    
  Lemma GJ_TE_trans_app : forall te Xs Ys Ts Vs Zs,
   length Xs = length Ts -> GJ_TE_Free_Vars te Zs ->
   (forall Y : TX, In Y Zs -> In Y Xs) -> GJ_TE_Trans te Xs Ts = GJ_TE_Trans te (Xs ++ Ys) (Ts ++ Vs).
    destruct te; induction l; intros.
    eapply TE_trans_app_H1; eauto.
    eapply TE_trans_app_H2; eauto.
  Qed.
     
  Lemma GJ_exists_TE_Free_Vars : forall te , exists Xs : list TX, GJ_TE_Free_Vars te Xs.
    destruct te; induction l; intros.
    exists nil; apply (TE_FV_GTy_ext nil _ nil).
    apply P2'_if_P2; constructor.
    destruct IHl as [Xs ex_Xs]; destruct (exists_Free_Vars a) as [Xs' ex_Xs']; exists (app Xs' Xs).
    inversion ex_Xs; subst.
    assert (fold_right (@app _) nil (Xs' :: txs) = Xs' ++ fold_right (@app _) nil txs) by reflexivity.
    rewrite <- H.
    inversion ex_Xs; subst; apply (TE_FV_GTy_ext (a :: l) t (Xs' :: txs)).
    apply P2'_if_P2; apply P2_if_P2' in H2; constructor; auto.
  Qed.
    
  Definition Ty_trans_fresh_vars_P T := forall Xs Ys Zs fresh_tys Ts Vs Ws
    (len_Ys : length Ys = length fresh_tys)
    (len_fresh_tys : length fresh_tys = length Vs) 
    (len_Xs : length Xs = length Ts)
    (distinct_fresh_tys : distinct fresh_tys)
    (fresh_Xs : forall Y, In Y fresh_tys -> ~ In Y Xs),
    distinct (Xs ++ Ys) -> 
    Free_Vars T Ws -> 
    (forall Y , In Y fresh_tys -> ~ In Y Ws) ->
    List_P2' Free_Vars Ts Zs -> 
    List_P1 (fun Zs' : list _ => forall Y , In Y fresh_tys -> ~ In Y Zs') Zs ->
    Ty_trans (Ty_trans (Ty_trans T Ys (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys))
      Xs Ts) fresh_tys Vs = Ty_trans T (Xs ++ Ys) (Ts ++ Vs).

  Definition Ty_trans_fresh_vars_Q Us := forall Xs Ys Zs fresh_tys Ts Vs Ws
    (len_Ys : length Ys = length fresh_tys)
    (len_fresh_tys : length fresh_tys = length Vs) 
    (len_Xs : length Xs = length Ts)
    (distinct_fresh_tys : distinct fresh_tys)
    (fresh_Xs : forall Y, In Y fresh_tys -> ~ In Y Xs),
    distinct (Xs ++ Ys) -> 
    TE_Free_Vars Us Ws -> 
    (forall Y , In Y fresh_tys -> ~ In Y Ws) ->
    List_P2' Free_Vars Ts Zs -> 
    List_P1 (fun Zs' : list _ => forall Y , In Y fresh_tys -> ~ In Y Zs') Zs ->
    TE_trans (TE_trans (TE_trans Us Ys (map (fun Y  => Ty_Wrap (TyVar Y)) fresh_tys))
      Xs Ts) fresh_tys Vs = TE_trans Us (Xs ++ Ys) (Ts ++ Vs).  

  Lemma In_distinct : forall (A : Type) (a : A) (As As' : list A),
    distinct (As ++ As') -> In a As -> ~ In a As'.
    induction As; simpl; intros; destruct H0; destruct H; subst.
    unfold not; intros; apply H; apply in_or_app; auto.
    eauto.
  Qed.    

  Lemma distinct_app : forall (A : Type) (As As' : list A), 
    distinct (As ++ As') -> distinct (As).
    clear; induction As; simpl; intros; auto.
    destruct H; split; eauto.
    unfold not; intros; eapply H; apply in_or_app; tauto.
  Qed.
    
  Definition Ty_trans_no_op_P T := forall Xs Ys Vs, Free_Vars T Xs -> 
    (forall X, In X Ys -> ~ In X Xs) -> Ty_trans T Ys Vs = T.

  Definition Ty_trans_no_op_Q Ts := forall Xs Ys Vs, TE_Free_Vars Ts Xs -> 
    (forall X, In X Ys -> ~ In X Xs) -> TE_trans Ts Ys Vs = Ts.

  Lemma GJ_Ty_trans_no_op : forall Y, Ty_trans_no_op_P (Ty_Wrap (TyVar Y)).
    unfold Ty_trans_no_op_P; intros;
      apply GJ_Free_Vars_invert in H; inversion H; subst; apply GJ_Ty_Wrap_inject in H2;
        injection H2; intros; subst; clear H H2.
    rewrite  GJ_Ty_trans_invert.   
    generalize Vs H0; clear; induction Ys; simpl; intros; auto.
    destruct Vs; auto.
    destruct (TX_eq_dec a Y).
    elimtype False; apply (H0 Y); tauto.
    erewrite <- IHYs; simpl; auto.
  Defined.

  Lemma FJ_Ty_trans_no_op : forall te c, Ty_trans_no_op_Q te -> 
    Ty_trans_no_op_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_no_op_P; unfold Ty_trans_no_op_Q; intros; apply FJ_Free_Vars_invert in H0;
      inversion H0; subst; apply FJ_Ty_Wrap_inject in H2; injection H2; intros; subst; clear H2 H0.
    rewrite FJ_Ty_trans_invert; simpl; erewrite H; eauto.
  Defined.

  Lemma Ty_trans_no_op_H3 te : forall Xs Ys Vs, GJ_TE_Free_Vars (nil, te) Xs -> 
    (forall X, In X Ys -> ~ In X Xs) -> GJ_TE_Trans (nil, te) Ys Vs = (nil, te).
    unfold GJ_TE_Trans; simpl; auto.
  Defined.

  Lemma Ty_trans_no_op_H4 ty tys te : 
    Ty_trans_no_op_Q (GTy_ext_Wrap (tys, te)) -> 
    Ty_trans_no_op_P ty -> 
    forall Xs Ys Vs, GJ_TE_Free_Vars (ty :: tys, te) Xs -> 
    (forall X, In X Ys -> ~ In X Xs) -> GJ_TE_Trans (ty :: tys, te) Ys Vs = (ty :: tys, te).
    unfold Ty_trans_no_op_Q; unfold Ty_trans_no_op_P; unfold GJ_TE_Trans; simpl; intros.
    inversion H1; subst; apply P2_if_P2' in H6; inversion H6; subst.
    erewrite H0; try eassumption.
    assert (TE_Free_Vars (GTy_ext_Wrap (tys, te)) (fold_right (@app _) nil Bs)) by
      (apply GJ_TE_Free_Vars_Wrap; constructor; apply P2'_if_P2; assumption).
    assert (forall X : TX, In X Ys -> ~ In X (fold_right (@app _) nil Bs)) by
      (unfold not; intros; eapply H2; simpl; eauto; apply in_or_app; tauto).
    generalize (H _ Ys Vs H3 H4) as H7; intro; rewrite GJ_TE_Trans_invert in H7.
    apply GTy_ext_Wrap_inject in H7; injection H7; intros; rewrite H9.
    reflexivity.
    unfold not; intros; eapply H2; simpl; eauto; apply in_or_app; tauto.
  Defined.

  Variable Ty_trans_no_op : forall ty, Ty_trans_no_op_P ty.

   Lemma GJ_Ty_trans_fresh_vars : forall Y, Ty_trans_fresh_vars_P (Ty_Wrap (TyVar Y)).
     unfold Ty_trans_fresh_vars_P; intros until Ws.
     intro; intro; intro; intro; intro; intro.
     destruct (in_dec TX_eq_dec Y (Xs ++ Ys)) as [H1 | H1]; intros.
     apply GJ_Free_Vars_invert in H0; inversion H0; subst; apply GJ_Ty_Wrap_inject in H6;
       injection H6; intros; subst.
     destruct (in_app_or _ _ _ H1) as [In_Xs | In_Ys];
       clear H0 H1 H6.
     assert (~ In Y Ys) by (eapply In_distinct; eassumption).
    assert (Ty_trans ((TyVar Y)) Ys (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys) = (TyVar Y)).
    generalize GJ_Ty_trans_invert Ty_trans_nil fresh_tys H0; clear; induction Ys; simpl; intros; auto.
    rewrite Ty_trans_nil; reflexivity.
    rewrite GJ_Ty_trans_invert; simpl in *|-*; destruct (TX_eq_dec a Y); try tauto.
    destruct fresh_tys; simpl; auto.
    rewrite <- GJ_Ty_trans_invert; apply IHYs; tauto.
    rewrite H1.
    erewrite Ty_trans_trans_subst.
    assert (map (fun ty : Ty => Ty_trans ty fresh_tys Vs) Ts = Ts) by
      (generalize Ty_trans_no_op Zs H3 H4; clear; induction Ts; simpl; intros; auto;
        inversion H3; subst; inversion H4; subst;
          erewrite IHTs; try eassumption; erewrite Ty_trans_no_op; eauto).
    rewrite H5; erewrite Ty_trans_app.
    reflexivity.
    eassumption.
    apply GJ_Free_Vars_Wrap; repeat econstructor.
    intros Z H11; destruct H11.
    rewrite <- H6; assumption.
    destruct H6.
    assumption.
    apply GJ_Free_Vars_Wrap; repeat econstructor.
    intros Z H11; destruct H11.
    rewrite <- H5; assumption.
    destruct H5.
    eapply distinct_sym in H; assert (~ In Y Xs) by (eapply In_distinct; eauto; eassumption);
      apply distinct_app in H.
    assert (exists n, exists fresh_ty, nth_error Ys n = Some Y /\
      nth_error fresh_tys n = Some fresh_ty /\ Ty_trans (TyVar Y) Ys
      (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys) = (TyVar fresh_ty)).
    generalize GJ_Ty_trans_invert TX_eq_dec fresh_tys len_Ys In_Ys distinct_fresh_tys H H0 H2 H3; clear; induction Ys;
      simpl; intros; destruct fresh_tys; simpl in len_Ys; try discriminate; destruct In_Ys;
        injection len_Ys; subst; intros; clear len_Ys.
    exists 0; exists t; simpl; repeat split; rewrite GJ_Ty_trans_invert; simpl;
      destruct (TX_eq_dec Y Y); congruence.
    simpl in distinct_fresh_tys; destruct distinct_fresh_tys; destruct H.
    destruct (IHYs GJ_Ty_trans_invert TX_eq_dec _ H4 H1 H6 H7 H0) as [n' [fresh_ty [nth_Ys [nth_fresh_tys ty_eq]]]].
    simpl; intros; eapply H2; simpl; tauto.
    assumption.
    exists (S n'); exists fresh_ty; simpl; repeat split; try rewrite GJ_Ty_trans_invert; simpl;
      try assumption.
    rewrite GJ_Ty_trans_invert in ty_eq; simpl in ty_eq.
    destruct (TX_eq_dec a Y); subst.
    elimtype False; apply H; eapply nth_error_in; eassumption.
    simpl in ty_eq; rewrite ty_eq; auto.
    destruct H1 as [n' [fresh_ty [nth_Ys [nth_fresh_tys ty_eq]]]]; rewrite ty_eq.
    rewrite (Free_Vars_Subst (Ty_Wrap (TyVar fresh_ty)) (fresh_ty :: nil)).
    assert (Ty_trans (Ty_Wrap (TyVar Y)) (Xs ++ Ys) (Ts ++ Vs) =
      Ty_trans (Ty_Wrap (TyVar Y)) Ys Vs) as X_eq by
    (generalize GJ_Ty_trans_invert TX_eq_dec Ts len_Xs H0; clear; induction Xs; intros; destruct Ts;
      simpl in *|-*; try discriminate; auto; injection len_Xs; clear len_Xs;
        rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec a Y); intros;
          try erewrite <- IHXs with (Ts := Ts);
            try tauto; try rewrite GJ_Ty_trans_invert; try eassumption; eauto).
    rewrite X_eq.
    generalize  GJ_Ty_trans_invert TX_eq_dec n' Vs fresh_tys len_Ys len_fresh_tys nth_Ys
      nth_fresh_tys H distinct_fresh_tys;
      clear; induction Ys; intros; destruct fresh_tys; destruct Vs; destruct n'; simpl in *|-*;
        try discriminate; injection nth_Ys; injection nth_fresh_tys; injection len_Ys;
          injection len_fresh_tys; intros; clear nth_Ys nth_fresh_tys len_Ys len_fresh_tys;
            repeat rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec t fresh_ty);
              destruct (TX_eq_dec a Y); try congruence; destruct H; destruct distinct_fresh_tys.
    elimtype False; apply H5; eapply nth_error_in; subst; eassumption.
    elimtype False; apply H; eapply nth_error_in; subst; eassumption.
    repeat rewrite <- GJ_Ty_trans_invert; eapply IHYs; eauto.
    simpl; intros; destruct H1; subst.
    eapply fresh_Xs; eapply nth_error_in; eassumption.
    destruct H1.
    simpl; apply GJ_Free_Vars_Wrap; repeat constructor.
    repeat rewrite (Ty_trans_no_op _ _ _ _ H0); auto; apply GJ_Free_Vars_invert in H0; 
      inversion H0; subst; apply GJ_Ty_Wrap_inject in H6; injection H6; intros; subst;
        simpl; unfold not; intros; destruct H5; subst; eauto.
    apply H1; apply in_or_app; tauto.
    apply H1; apply in_or_app; tauto.
   Defined. 

  Lemma FJ_Ty_trans_fresh_vars : forall te c, Ty_trans_fresh_vars_Q te ->
    Ty_trans_fresh_vars_P (FJ_Ty_Wrap (ty_def _ _ te c)).
    unfold Ty_trans_fresh_vars_P; unfold Ty_trans_fresh_vars_Q; intros.
    apply FJ_Free_Vars_invert in H1;
      inversion H1; subst; apply FJ_Ty_Wrap_inject in H5; injection H5; intros; subst.
    repeat (rewrite FJ_Ty_trans_invert; simpl); erewrite H; eauto.
  Defined.

  Lemma Ty_trans_fresh_vars_H3 te : Ty_trans_fresh_vars_Q (GTy_ext_Wrap (nil, te)).
    unfold Ty_trans_fresh_vars_Q; intros; repeat (rewrite GJ_TE_Trans_invert; simpl).
    unfold GJ_TE_Trans; simpl; auto.
  Defined.

  Lemma Ty_trans_fresh_vars_H4 ty tys te :
    Ty_trans_fresh_vars_Q (GTy_ext_Wrap (tys, te)) ->
    Ty_trans_fresh_vars_P ty ->
    Ty_trans_fresh_vars_Q (GTy_ext_Wrap (ty :: tys, te)).
    unfold Ty_trans_fresh_vars_Q; unfold Ty_trans_fresh_vars_P; intros;
      repeat (rewrite GJ_TE_Trans_invert; simpl); unfold GJ_TE_Trans; simpl.
    apply GJ_TE_Free_Vars_invert in H2; inversion H2; subst; apply P2_if_P2' in H9;
      inversion H9; subst.
    erewrite H0; eauto.
    assert (TE_Free_Vars (GTy_ext_Wrap (tys, te)) (fold_right (@app _) nil Bs)) by
      (eapply GJ_TE_Free_Vars_Wrap; econstructor; apply P2'_if_P2; eauto).
    assert (forall Y : TX, In Y fresh_tys -> ~ In Y (fold_right (@app _) nil Bs)) by
      (unfold not; intros Y GX NGX; eapply H3; simpl; eauto; apply in_or_app; tauto).
    generalize (H _ _ _ _ _ _ _ len_Ys len_fresh_tys len_Xs distinct_fresh_tys fresh_Xs
    H1 H6 H7 H4 H5); intros.
    repeat (rewrite GJ_TE_Trans_invert in H10; simpl in H10).
    unfold GJ_TE_Trans in H10; simpl in H10; apply GTy_ext_Wrap_inject in H10;
      injection H10; intros map_eq; rewrite map_eq; auto.
    unfold not; intros; eapply H3; simpl; eauto; apply in_or_app; tauto.
  Defined.
   
  Lemma map_self : forall Ys tys, length Ys = length tys -> distinct Ys -> 
      tys = map (fun ty : Ty => Ty_trans ty Ys tys) (map (fun x : TX => Ty_Wrap (TyVar x)) Ys).
    induction Ys; simpl; intros; destruct tys; simpl in H; try discriminate; try injection H; 
      intros; clear H; auto.
    rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec a a); subst.
    assert (forall Xs, ~ In a Xs -> map (fun ty : Ty => Ty_trans ty (a :: Ys) (t :: tys))
      (map (fun x : TX => Ty_Wrap (TyVar x)) Xs) = map (fun ty : Ty => Ty_trans ty Ys tys)
      (map (fun x : TX => Ty_Wrap (TyVar x)) Xs)) as eq_Ys by 
    (generalize TX_eq_dec GJ_Ty_trans_invert; clear; induction Xs; simpl; intros; auto;
      repeat rewrite GJ_Ty_trans_invert; simpl; destruct (TX_eq_dec a a0); subst;
        try rewrite IHXs; tauto).
    rewrite eq_Ys; try tauto; rewrite <- (IHYs tys); tauto.
    tauto.
  Qed.

  Section Build_S0''_Section.

    Variable E_Ty_trans' : TyP_List -> list Ty -> E -> E -> Prop. 
    Variable ty_ext' : Set.
    Variable md_ext' : Set.
    Variable mty_ext' : Set.
    Variable m_call_ext' : Set.
    Variable L_WF_Ext' : Context -> cld_def_ext -> C -> Prop.  
    Variable build_context' : cld_def_ext -> md_ext' -> Context -> Context -> Prop.
    Variable mtype_build_mtye' : cld_def_ext -> ty_ext' -> Ty -> list VD -> md_ext' -> mty_ext' -> Prop.
    Variable mtype_build_tys' : cld_def_ext -> ty_ext' -> Ty -> list VD -> md_ext' -> list Ty -> list Ty -> Prop.
    Variable WF_mtype_U_map' : Context -> m_call_ext' -> mty_ext' -> Ty -> Ty -> Prop.
    Variable WF_mtype_ext' : Context -> m_call_ext' -> mty_ext' -> Prop.
    Variable WF_mtype_Us_map' : Context -> m_call_ext' -> mty_ext' -> list Ty -> list Ty -> Prop.
    Variable ce_build_cte' : cld_def_ext -> ty_ext' -> Prop.
    Variable Meth_WF_Ext' : Context -> cld_def_ext -> md_ext' -> Prop.
    Variable mtype_build_tys_len : forall ce te ty vd me tys tys',
      mtype_build_tys' ce te ty vd me tys tys' -> length tys = length tys'.
    Variable Weaken_WF_Type_app_TList : forall delta S WF_S, Weaken_WF_Type_app_TList_P delta S WF_S.
    Variable build_context'_Empty_1 : forall ce me vds gamma XNs T, 
      build_context' ce me (update_list Empty vds) gamma -> 
      WF_Type (update_Tlist gamma XNs) T -> WF_Type (update_Tlist (update_list Empty vds) XNs) T.
    Variable build_context'_Empty_2 : forall ce me vds gamma XNs S T, 
      build_context' ce me (update_list Empty vds) gamma -> 
      subtype (update_Tlist gamma XNs) S T -> subtype (update_Tlist (update_list Empty vds) XNs) S T.
    Variable build_context'_Empty_3 : forall ce me vds gamma XNs e T, 
      build_context' ce me (update_list Empty vds) gamma -> 
      E_WF (update_Tlist gamma XNs) e T -> E_WF (update_Tlist (update_list Empty vds) XNs) e T.
    Variable Ty_trans_eq_N_Trans : forall N XNs Us, 
      N_Wrap (N_Trans XNs Us N) = Ty_trans N (Extract_TyVar XNs) Us.
    Variable Lem_2_11 : forall delta e T (WF_e : E_WF delta e T) (delta_1 : Context)
      (Xs : list TX) (Ns : list N) (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) e',
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
      delta = (update_Tlist (update_list Empty vars) XNs) -> 
    List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) -> 
    List_P1 (WF_Type delta_1) Us -> 
    List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
    E_Ty_trans' XNs Us e e' ->
    exists T', E_WF (update_list delta_1 (map 
      (fun v => match v with 
                  (v, ty) => (v, Ty_trans ty Xs Us) end) vars))
    e' T' /\ subtype delta_1 T' (Ty_trans T Xs Us).
  Variable build_fresh_distinct : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> distinct Zs.
  Variable build_fresh_id : forall tys ty tys' Xs Ys Zs Zs', build_fresh tys ty tys' Xs Ys Zs -> 
    build_fresh tys ty tys' Xs Ys Zs' -> Zs = Zs'.
  Variable Ty_trans_fresh_vars : forall T, Ty_trans_fresh_vars_P T.
  Variable build_fresh_new : forall tys ty vds Ws Xs Ys Zs, List_P2' (Free_Vars) tys Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.
  Variable build_fresh_new' : forall tys ty vds Ws Xs Ys Zs, List_P2' (Free_Vars) vds Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.
  Variable build_fresh_new'' : forall tys ty vds Ws Xs Ys Zs, Free_Vars ty Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Ws.
  Variable build_fresh_new''' : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Xs.
  Variable build_fresh_new'''' : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y (Extract_TyVar Ys).
  Variable build_fresh_new''''' : forall tys ty vds Ws Xs Ys Zs,  
    List_P2' (Free_Vars) (map (fun n => (N_Wrap (@snd _ _ n))) Ys) Ws -> build_fresh tys ty vds Xs Ys Zs -> 
    List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.
  Variable WF_mtype_U_map'_id : forall delta mce0 mtye0 ty ty', 
    WF_mtype_U_map' delta mce0 mtye0 ty ty' -> ty = ty'.
  Variable WF_mtype_Us_map'_id : forall delta mce0 mtye0 tys tys', 
    WF_mtype_Us_map' delta mce0 mtye0 tys tys' -> tys = tys'.
  Variable mtype_build_tys'_id : forall ce te T vds mde tys tys',
    mtype_build_tys' ce te T vds mde tys tys' -> tys = tys'.
  Variable exists_Free_Vars_Q : forall te, exists_Free_Vars_Q te.
  Variable GJ_ty_ext_unwrap : ty_ext -> @GTy_ext ty_ext'.

  Lemma GJ_WF_class_ext_TE_trans {ce_build_cte'' L_WF_Ext''} 
    (te_eq : forall te te' : ty_def_ext, te = te') : forall gamma ce te,
    @GJ_wf_class_ext cld_def_ext ty_def_ext gamma ce te -> 
    forall delta c te' (WF_ce : GJ_definitions.L_WF_Ext L_WF_Ext'' delta ce c),
      GJ_ce_build_cte ce_build_cte'' ce te' ->      
      te = GJ_TE_Trans te' (Extract_TyVar (fst ce)) (fst te).
    intros; inversion H; subst.
    inversion H0; inversion WF_ce; subst; unfold GJ_TE_Trans; simpl in *|-*.
    rewrite <- (map_self (Extract_TyVar typs) tys); auto.
    rewrite (te_eq te te0) ; reflexivity.
    unfold Extract_TyVar; rewrite map_length; assumption.
    unfold Extract_TyVar; generalize distinct_Xs; clear; induction typs;
      simpl; auto; destruct a; simpl; intros.
    destruct distinct_Xs; split; auto.
    unfold not; intros; apply H; generalize H1; clear; induction typs; simpl; 
      auto; destruct a; simpl; intros.
    destruct g0; destruct g; destruct H1; subst; auto.
  Qed.

  Lemma GJ_Build_S0''' :
    forall (ce : @GJ_definitions.cld_ext cld_def_ext) me (gamma gamma' : Context)
      (te te' : ty_ext) (c : C)
      (vds : list VD) (S0 T0 : Ty) (delta : Context) 
      (e e' : E) (D D' : Ty) mtye mce
      (Ds Ds' : list Ty) (Vars : list (Var _ * Ty))
      (ce_WF : GJ_definitions.L_WF_Ext L_WF_Ext' gamma' ce c)
      (build_gamma' : GJ_definitions.L_build_context L_build_context' ce gamma')
      (wf_me : @GJ_Meth_WF_Ext cld_def_ext md_ext' Meth_WF_Ext' gamma ce me)
      (build_te' : GJ_ce_build_cte ce_build_cte' ce (GJ_ty_ext_unwrap te'))
      (Bound_te : forall Y Zs, TE_Free_Vars te' Zs -> In Y Zs -> In Y (Extract_TyVar (fst ce))),
      GJ_build_context build_context' ce me
      (cFJ.update_list _ Ty Context Update Empty
        ((this _, FJ_Ty_Wrap (ty_def _ ty_ext te' (cl _ c)))
          :: map (fun Tx : VD => match Tx with | vd ty x => (var _ x, ty) end) vds)) gamma ->
      E_WF gamma e S0 ->
      subtype gamma S0 T0 ->
      GJ_wf_class_ext delta ce (GJ_ty_ext_unwrap te) ->
      @mtype_build_mtye cld_def_ext ty_ext' md_ext' mty_ext' mtype_build_mtye' ce 
      (GJ_ty_ext_unwrap te) T0 vds me mtye -> 
      map_mbody m_call_ext' ty_ext' _ _ _ E_Ty_trans' ce (GJ_ty_ext_unwrap te) mce me e e' ->
      mtype_build_tys mtype_build_tys' ce (GJ_ty_ext_unwrap te) T0 vds me (T0 :: nil) (D :: nil) ->
      GJ_WF_mtype_U_map _ _ WF_mtype_U_map' delta mce mtye D D' ->
      GJ_WF_mtype_ext _ _ WF_mtype_ext' delta mce mtye ->
      GJ_WF_mtype_Us_map _ _ WF_mtype_Us_map' delta mce mtye Ds Ds' ->
      List_P1
      (fun Tx : VD => match Tx with
                        | vd ty _ => WF_Type gamma ty
                      end) vds ->
      zip
      (this _
      :: map (fun Tx : VD => match Tx with
                               | vd _ x => var _ x
                             end) vds)
      (FJ_Ty_Wrap (ty_def _ _ (TE_trans te' (Extract_TyVar (fst ce)) (fst (GJ_ty_ext_unwrap te) )) (cl _ c)) :: 
        Ds') (@pair _ _) = 
      Some Vars ->
      mtype_build_tys mtype_build_tys' ce (GJ_ty_ext_unwrap te) T0 vds me 
      (map (fun vd' : VD => match vd' with
                              | vd ty _ => ty
                            end) vds) Ds ->
      exists S0'' : Ty,
        subtype delta S0'' D' /\
        E_WF (cFJ.update_list _ Ty Context Update delta Vars) e'
        S0''.
    intros.
    subst; inversion build_te'; subst; rewrite <- H12 in *|-*; clear H12.
    inversion H; subst; clear H.
    inversion H5; subst; simpl in H20; rewrite <- H13 in *|-*; 
      generalize (mtype_build_tys_len _ _ _ _ _ _ _ H23); intros len_tys'; destruct tys'; 
        try (simpl in len_tys'; discriminate); simpl in H20; injection H20; intros; subst;
          destruct tys'; try (simpl in len_tys'; discriminate); clear len_tys' H H5 H20 H13.
    inversion H11; subst; clear H11.
    unfold GJ_WF_mtype_ext in H7.
    inversion H6; inversion H8; subst.
    inversion H2; subst.
    rename H1 into sub_S0_T0; rename H28 into sub_tys_XNs; destruct H7 as [WF_mtye0 [WF_Vs sub_Vs_Y0s0]].
    inversion H3; subst.
    rename ZQs' into YOs'.
    rename tys into Ts.
    inversion wf_me; subst; clear H8.
    inversion ce_WF; inversion build_gamma'; subst.
    repeat rewrite Extract_TyVar_Typs_Trans_eq in *|-*.
    rename typs into XNs.
    cut (length (Extract_TyVar XNs ++ Extract_TyVar YOs) = length (Ts ++ Vs)).
    intro len_XNs_YOs.
    assert (zip ((Extract_TyVar XNs) ++ (Extract_TyVar YOs))
      ((map (@snd _ _) XNs) ++ (map (@snd _ _) YOs))
      (fun x => @pair _ _ (TyVar x)) = Some (XNs ++ YOs)) as eq_XNs_Y0s by
    (clear; induction XNs; simpl;
      first [induction YOs; simpl; auto; rewrite IHYOs; destruct a; destruct g; simpl; auto |
        rewrite IHXNs; destruct a; destruct g; simpl; auto]).
    cut (List_P2 (Ts ++ Vs) (map (@snd _ _ ) XNs ++ map (@snd _ _) YOs)
      (fun U N => subtype delta U (Ty_trans (N_Wrap N)
        (Extract_TyVar XNs ++ Extract_TyVar YOs) (Ts ++ Vs)))).
    intros sub_TVs_NOs.
    assert (exists XNs', XNs = XNs') as ex_XNs' by (eexists _; reflexivity);
      destruct ex_XNs' as [XNs' eq_XNs']; revert H28; rewrite eq_XNs' at 1; intros H28.
    assert (List_P1 (fun N => WF_Type (update_Tlist Empty (XNs ++ YOs)) (N_Wrap N)) (map (@snd _ _) XNs'))
      as WF_XNs by 
    (generalize Weaken_WF_Type_app_TList H28 
      (fun XNs Ty => L_build_context'_Empty_1 ce0 gamma0 XNs Ty H33); clear; induction XNs';
        simpl; subst; constructor; inversion H28; subst;
          first [eapply Weaken_WF_Type_app_TList; auto; apply H; auto | apply IHXNs'; auto]).
    assert (exists YOs'', YOs = YOs'') as ex_YOs'' by (eexists _; reflexivity);
      destruct ex_YOs'' as [YOs'' eq_YOs'']; revert H1; rewrite eq_YOs'' at 1; intros H1.
    assert (List_P1 (fun N => WF_Type (update_Tlist Empty (XNs ++ YOs)) (N_Wrap N)) (map (@snd _ _) YOs''))
      as WF_YOs by
        (generalize H1 (fun XNs Ty => build_context'_Empty_1 _ _ _ _ XNs Ty H18)
          WF_Type_update_Tupdate Strengthen_WF_Type_update_TList; clear; 
            induction YOs''; subst; constructor; inversion H1; 
              subst; apply H in H3; auto;
                eapply Strengthen_WF_Type_update_TList; try reflexivity; eapply WF_Type_update_Tupdate;
                  eauto); rewrite <- eq_YOs'' in WF_YOs, H1; clear eq_YOs'' YOs''.
    generalize (List_P1_app _ _ _ _ WF_XNs WF_YOs); intros WF_Ns_Os; clear WF_XNs WF_YOs.
    inversion H4; subst.
    destruct (Lem_2_11 _ _ _ (build_context'_Empty_3 _ _ _ _ _ _ _ H18 H0)
      _ _ _ _ _ _ _ len_XNs_YOs eq_XNs_Y0s (refl_equal _)
      sub_TVs_NOs (List_P1_app _ _ _ _ H17 WF_Vs) WF_Ns_Os H37) as [T' [WF_e' sub_T'_T]].
    exists T'; split.
    assert (length (Extract_TyVar XNs' ++ Extract_TyVar YOs') = length (Ts ++ Vs)) as len_XNs_YOs' by
      (repeat rewrite app_length; apply length_List_P2 in sub_Vs_Y0s0; rewrite length_Tys_Trans in sub_Vs_Y0s0;
        rewrite len_map in sub_Vs_Y0s0; rewrite length_Typs_Trans in sub_Vs_Y0s0;
          unfold Extract_TyVar; repeat rewrite len_map; try congruence).
    assert (zip ((Extract_TyVar XNs') ++ (Extract_TyVar YOs'))
      ((map (@snd _ _) XNs') ++ (map (@snd _ _) YOs'))
      (fun x => @pair _ _ (TyVar x)) = Some (XNs' ++ YOs')) as eq_XNs_Y0s' by
    (clear; induction XNs'; simpl;
      first [induction YOs'; simpl; auto; rewrite IHYOs'; destruct a; destruct g; simpl; auto |
        rewrite IHXNs'; destruct a; destruct g; simpl; auto]).
    generalize (List_P1_app _ _ _ _ H17 WF_Vs); intros WF_Ts_Vs.
    revert sub_Vs_Y0s0; intro; unfold Tys_Trans in sub_Vs_Y0s0; repeat rewrite Extract_TyVar_Typs_Trans_eq in *|-*.
    assert (forall YOs, map (fun ty' : Ty => Ty_trans ty' (Extract_TyVar YOs) Vs)
      (map (fun yo => N_Wrap (snd yo))
        (Typs_Trans XNs' Ts YOs')) =
      map (fun ty' => Ty_trans (Ty_trans (N_Wrap ty') (Extract_TyVar XNs') Ts) (Extract_TyVar YOs) Vs)
      (map (@snd _ _) YOs')) as Trans_YOs'_eq by
    (generalize Ty_trans_eq_N_Trans; clear; induction YOs'; simpl; intros; auto; destruct a; 
      destruct g; simpl; rewrite IHYOs'; simpl; auto; rewrite Ty_trans_eq_N_Trans; reflexivity);
    rewrite Trans_YOs'_eq in sub_Vs_Y0s0; clear Trans_YOs'_eq.
    eapply FJ_subtype_Wrap; econstructor 2; try eassumption.
    rewrite (build_fresh_id _ _ _ _ _ _ _ H27 H24) in *|-*;
      rewrite (build_fresh_id _ _ _ _ _ _ _ H27 H24) in H27;
        rewrite (build_fresh_id _ _ _ _ _ _ _ H24 H32) in *|-*.
    destruct (exists_Free_Vars' Ts) as [Zs Free_Vars_Ts].
    generalize (build_fresh_len _ _ _ _ _ _ H24) as len_fresh_tys; intro.
    assert (forall YOs YOs' YOs'' fresh_tys fresh_tys',
      zip fresh_tys
      (map (fun (typ' : GTy * N) => N_Trans YOs' (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys')
        (@snd _ _ typ')) YOs) (fun x => pair (TyVar x)) =
      Some YOs'' -> Extract_TyVar YOs'' = fresh_tys) as Extract_TV_YOs' by 
    (clear; induction YOs; destruct fresh_tys; simpl; intros;
      try discriminate; subst; simpl; try first [injection H; intros; subst; auto; fail |
        caseEq (zip fresh_tys
          (map
            (fun typ' : GTy * N =>
              N_Trans YOs'
              (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys')
              (snd typ')) YOs) (fun x => pair (TyVar x)));
        rewrite H0 in H; simpl in H; try discriminate; injection H; intros; subst;
          simpl; erewrite IHYOs; eauto]).
    rewrite (Extract_TV_YOs' _ _ _ _ _ eq_ZQs').
    apply P2_if_P2' in Free_Vars_Ts.
    rewrite <- (WF_mtype_U_map'_id _ _ _ _ _ H); generalize (mtype_build_tys'_id _ _ _ _ _ _ _ H23); 
      intros G1; injection G1; intros; subst; clear G1.
    destruct (exists_Free_Vars t) as [Zs' FV_t].
    erewrite (Ty_trans_fresh_vars t (Extract_TyVar XNs') (Extract_TyVar YOs) _ _ _ _ _); try eassumption.
    assert (subtype (update_Tlist Empty (XNs' ++ YOs)) S0 t) as sub_S0_T0' by 
      (eapply Subtype_Update_list_id; try reflexivity; eapply subtype_update_Tupdate;
        try reflexivity; eapply build_context'_Empty_2 in sub_S0_T0; try eassumption; auto; 
          eapply sub_S0_T0).
    rewrite <- (app_context_Empty delta);
      rewrite <- (subst_context_Empty (Extract_TyVar XNs' ++ Extract_TyVar YOs) (Ts ++ Vs)).
    eapply (Type_Subst_Sub_2_5' _ _ _ sub_S0_T0' ); try eassumption.
    reflexivity.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); 
      unfold Extract_TyVar; repeat rewrite map_length; reflexivity.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); generalize len_XNs_YOs; repeat rewrite app_length;
    unfold Extract_TyVar; repeat rewrite map_length; rewrite H21; clear;
      induction Ts; simpl; intros; auto; injection len_XNs_Y0s.
    unfold Extract_TyVar; repeat rewrite map_length; auto.
    eauto.
    eauto.
    tauto.
    eauto.
    eauto.    
    injection H20; injection H19; intros; subst.
    caseEq (zip
      (map (fun Tx : VD => match Tx with
                             | vd _ x => var _ x
                           end) vds)
      (Tys_Trans (Typs_Trans XNs' Ts YOs') Vs (Tys_Trans XNs' Ts (Tys_Trans YOs
        (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys0) tys')))
      (@pair _ _)); simpl in H10; rewrite <- (WF_mtype_Us_map'_id _ _ _ _ _ H16) in *|-*;
    simpl in H10; rewrite H7 in H10; try discriminate; injection H10; intros; subst; simpl.
    simpl in WF_e'.
    destruct (exists_Free_Vars' Ts) as [Zs Free_Vars_Ts].
    apply P2_if_P2' in Free_Vars_Ts.
    destruct (exists_Free_Vars t) as [Zs' FV_t].
    assert (forall YOs YOs' YOs'' fresh_tys fresh_tys',
      zip fresh_tys
      (map (fun (typ' : GTy * N) => N_Trans YOs' (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys')
        (@snd _ _ typ')) YOs) (fun x => pair (TyVar x)) =
      Some YOs'' -> Extract_TyVar YOs'' = fresh_tys) as Extract_TV_YOs' by 
    (clear; induction YOs; destruct fresh_tys; simpl; intros;
      try discriminate; subst; simpl; try first [injection H; intros; subst; auto; fail |
        caseEq (zip fresh_tys
          (map
            (fun typ' : GTy * N =>
              N_Trans YOs'
              (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys')
              (snd typ')) YOs) (fun x => pair (TyVar x)));
        rewrite H0 in H; simpl in H; try discriminate; injection H; intros; subst;
          simpl; erewrite IHYOs; eauto]).
    rewrite (build_fresh_id _ _ _ _ _ _ _ H27 H24) in *|-*;
      rewrite (build_fresh_id _ _ _ _ _ _ _ H27 H24) in H27;
        rewrite (build_fresh_id _ _ _ _ _ _ _ H24 H32) in *|-*.
    rewrite <- (mtype_build_tys'_id _ _ _ _ _ _ _ H26) in *|-*.
    assert (forall T Zs, Free_Vars T Zs -> (forall Y, In Y fresh_tys1 -> ~ In Y Zs) -> 
      Ty_trans
      (Ty_trans (Ty_trans T (Extract_TyVar YOs) (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1))
        (Extract_TyVar XNs') Ts) fresh_tys1 Vs = 
      Ty_trans T ((Extract_TyVar XNs') ++  (Extract_TyVar YOs)) (Ts ++ Vs)).
    intros; eapply (Ty_trans_fresh_vars T); eauto.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); generalize len_XNs_YOs; repeat rewrite app_length;
      unfold Extract_TyVar; repeat rewrite map_length; rewrite H21; clear;
        induction Ts; simpl; intros; auto; injection len_XNs_Y0s.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); generalize len_XNs_YOs; repeat rewrite app_length;
      unfold Extract_TyVar; repeat rewrite map_length; rewrite H21; clear;
        induction Ts; simpl; intros; auto; injection len_XNs_Y0s.
    unfold Extract_TyVar; repeat rewrite map_length; auto.
    tauto.
    assert (forall T, In T (map (fun Tx : VD => match Tx with | vd ty _ => ty end) vds) ->
      Ty_trans
         (Ty_trans
            (Ty_trans T (Extract_TyVar YOs)
               (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1))
            (Extract_TyVar XNs') Ts) fresh_tys1 Vs =
       Ty_trans T (Extract_TyVar XNs' ++ Extract_TyVar YOs) (Ts ++ Vs)).
    intros; destruct (exists_Free_Vars_P2 (map (fun Tx : VD => match Tx with | vd ty _ => ty end) vds));
      destruct (exists_Free_Vars T) as [Zs'' FV_T]; eapply H8; eauto.
    unfold not; intros; generalize (build_fresh_new' _ _ _ _ _ _ _ H13 H32); intros.
    eapply (In_List_P1' _ _ _ H31 Zs'').
    generalize Free_Vars_id x Zs'' H11 H13 FV_T; clear; induction vds; simpl; intros; 
      destruct H11; destruct a; inversion H13; subst; simpl; eauto.
    eassumption.
    eassumption.
    assert (l = map (fun v : Var _ * Ty => let (v0, ty) := v in (v0, Ty_trans ty
      (Extract_TyVar XNs' ++ Extract_TyVar YOs) (Ts ++ Vs)))
    (map (fun Tx : VD => match Tx with | vd ty x => (var _ x, ty) end) vds)) as eq_l by
    (generalize l H7 (Extract_TV_YOs' _ _ _ _ _ eq_ZQs') H11;
      clear; induction vds; simpl; intros; try (injection H7; intros; subst; auto; fail);
        repeat rewrite Extract_TyVar_Typs_Trans_eq in *|-*;
          caseEq (zip (map (fun Tx : VD => match Tx with
                                             | vd _ x => var _ x
                                           end) vds)
          (Tys_Trans (Typs_Trans XNs' Ts YOs') Vs (Tys_Trans XNs' Ts 
            (Tys_Trans YOs (map (fun Y => Ty_Wrap (TyVar Y)) fresh_tys1)
              (map (fun vd' : VD => match vd' with
                                      | vd ty _ => ty
                                    end) vds))))
          (@pair _ _));
          rewrite H0 in H7; try discriminate; injection H7; destruct a; simpl;
            rewrite H; erewrite (H11 t); try tauto; erewrite (IHvds _ H0); auto).
    rewrite <- eq_l in WF_e'.
    revert WF_e'.
    rewrite FJ_Ty_trans_invert; simpl.
    clear Zs' FV_t.
    destruct (exists_Free_Vars_Q te') as [Zs' FV_te'].
    rewrite <- TE_trans_app with (Zs := Zs'); eauto.
      unfold Extract_TyVar; rewrite len_map; assumption.
    apply P2'_if_P2; apply List_P2'_app; apply P2_if_P2'; split; intros.
    destruct sub_tys_XNs as [In_XNs NIn_XNs]; revert In_XNs NIn_XNs; intros.
    destruct (In_XNs _ _ H7) as [b [nth_XNs sub_a_b]].
    destruct (FJ_tactics.map_nth_error _ _ _ _ _ _ nth_XNs) as [b' [nth_XNs' eq_b']]; subst.
    exists (snd b'); split.
    eapply nth_error_map; auto.
    destruct (exists_Free_Vars (snd b')) as [Bs FV_b].
    erewrite <- Ty_trans_app; eauto.
      unfold Extract_TyVar; rewrite len_map; assumption.
    generalize (In_List_P1' _ _ _ H28 b' (nth_error_in _ _ _ _ nth_XNs'));
      intro WF_b'.
    apply (L_build_context'_Empty_1 _ _ _ _ H33) in WF_b'.
    apply (wf_free_vars _ _ WF_b' _ _ (refl_equal _) FV_b).
    destruct sub_tys_XNs as [In_XNs NIn_XNs]; revert In_XNs NIn_XNs; intros.
    apply (nth_error_map' _ _ _ _ _ (map_nth_error' _ _ _ _ _ (NIn_XNs _ H7))).
    destruct sub_Vs_Y0s0 as [In_YOs' NIn_YOs']; revert In_YOs' NIn_YOs'; intros.
    destruct (In_YOs' _ _ H7) as [b [nth_YOs' sub_a_b]].
    destruct (FJ_tactics.map_nth_error _ _ _ _ _ _ nth_YOs') as [b' [nth_YOs'' eq_b']]; subst.
    assert (exists YOs'', YOs'' = YOs) as ex_YOs'' by (eexists _; reflexivity);
      destruct ex_YOs'' as [YOs'' eq_YOs'']; revert eq_ZQs'; rewrite <- eq_YOs'' at 1; intros eq_YOs'.
    assert (exists fresh_tys', fresh_tys1 = fresh_tys') as ex_FT' by (eexists _; reflexivity);
      destruct ex_FT' as [fresh_tys' eq_FT']; revert eq_YOs'; rewrite eq_FT' at 1; intros eq_YOs'.
    assert (exists b'' : N, nth_error (map (@snd _ _) YOs'') n = Some b''
      /\ b' = Ty_trans (Ty_trans b'' (Extract_TyVar YOs)
        (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1)) (Extract_TyVar XNs) Ts) as nth_YOs by 
    (generalize n YOs YOs' fresh_tys1 fresh_tys' Ty_trans_eq_N_Trans eq_YOs' nth_YOs''; clear; induction YOs'';
      destruct fresh_tys'; intros; try discriminate; injection eq_YOs'; intros;
        subst; simpl in nth_YOs''; try (destruct n; discriminate);
          caseEq ( zip fresh_tys' (map (fun typ' : GTy * N => N_Trans YOs
            (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1)
            (snd typ')) YOs'') (fun x : TX => pair (TyVar x))); rewrite H0 in H;
          try discriminate; injection H; intros; subst;
            destruct n; try (eapply (IHYOs'' n); try eassumption; subst);
              try eexists _; split; try (simpl; auto; fail); simpl in nth_YOs'';
                injection nth_YOs''; intro; subst; repeat rewrite Ty_trans_eq_N_Trans; reflexivity).
    destruct nth_YOs as [b'' [nth_YOs eq_b']]; subst.
    exists b''; split; auto.
    rewrite Extract_TyVar_Typs_Trans_eq in sub_a_b.
    destruct (exists_Free_Vars' Ts) as [Zs Free_Vars_Ts];
      apply P2_if_P2' in Free_Vars_Ts.
    assert (forall YOs YOs' YOs'' fresh_tys fresh_tys',
      zip fresh_tys
      (map (fun typ' : GTy * N => N_Trans YOs' (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys')
        (snd typ')) YOs) (fun x : TX => pair (TyVar x)) =
      Some YOs'' -> Extract_TyVar YOs'' = fresh_tys) as Extract_TV_YOs' by 
    (clear; induction YOs; destruct fresh_tys; simpl; intros;
      try discriminate; subst; simpl; try (injection H; intros; subst; auto; fail);
        caseEq (zip fresh_tys
          (map
            (fun typ' : GTy * N =>
              N_Trans YOs'
              (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys')
              (snd typ')) YOs) (fun x => pair (TyVar x)));
        rewrite H0 in H; simpl in H; try discriminate; injection H; intros; subst;
          simpl; erewrite IHYOs; eauto).
    rewrite (Extract_TV_YOs' _ _ _ _ _ eq_YOs') in sub_a_b; auto.
    destruct (exists_Free_Vars (N_Wrap b'')) as [Ws FV_b''].
    erewrite (Ty_trans_fresh_vars b'' (Extract_TyVar XNs) (Extract_TyVar YOs)
      Zs fresh_tys' Ts Vs Ws) in sub_a_b; auto.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); 
      unfold Extract_TyVar; repeat rewrite map_length; reflexivity.
    rewrite <- (build_fresh_len _ _ _ _ _ _ H32); generalize len_XNs_YOs; repeat rewrite app_length;
      unfold Extract_TyVar; repeat rewrite map_length; rewrite H21; clear;
        induction Ts; simpl; intros; auto; injection len_XNs_Y0s.
    unfold Extract_TyVar; repeat rewrite map_length; auto.
    eauto.
    eauto.
    tauto.
    destruct (exists_Free_Vars_P2 (map (fun n => (N_Wrap (@snd _ _ n))) YOs)).
    unfold not; intros; generalize (build_fresh_new''''' _ _ _ _ _ _ _ H8 H32); intros.
    eapply (In_List_P1' _ _ _ H29 Ws).
    generalize x Free_Vars_id FV_b'' H8 (nth_error_in _ _ _ _ nth_YOs); clear;
      induction YOs; simpl; intros; destruct H; inversion H8; subst.
    simpl; left; eauto.
    simpl; right; eauto.
    eassumption.
    eassumption.
    intros; eapply build_fresh_new; eauto.
    destruct sub_Vs_Y0s0 as [In_YOs' NIn_YOs']; revert In_YOs' NIn_YOs'; intros.
    assert (exists YOs'', YOs'' = YOs) as ex_YOs'' by (eexists _; reflexivity);
      destruct ex_YOs'' as [YOs'' eq_YOs'']; revert eq_ZQs'; rewrite <- eq_YOs'' at 1; intros eq_YOs'.
    assert (exists YOs''', YOs''' = YOs') as ex_YOs''' by (eexists _; reflexivity);
      destruct ex_YOs''' as [YOs''' eq_YOs'''];
        generalize (NIn_YOs' _ H7) as NIn_YOs''; rewrite <- eq_YOs''' at 1; intros NIn_YOs''.
    assert (exists fresh_tys', fresh_tys1 = fresh_tys') as ex_FT' by (eexists _; reflexivity);
      destruct ex_FT' as [fresh_tys' eq_FT']; revert eq_YOs'; rewrite eq_FT' at 1; intros eq_YOs'.
    rewrite <- eq_YOs''.
    generalize n YOs YOs' YOs''' fresh_tys1 fresh_tys' eq_YOs' NIn_YOs''; clear; induction YOs'';
      destruct fresh_tys'; intros; try discriminate; injection eq_YOs'; intros;
        subst; simpl in NIn_YOs''; try (destruct n; auto; fail);
          caseEq (zip fresh_tys' (map (fun typ' : GTy * N => N_Trans YOs
            (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1)
            (snd typ')) YOs'') (fun x : TX => pair (TyVar x))); rewrite H0 in H;
          try discriminate; injection H; intros; subst;
            destruct n; simpl in NIn_YOs''; try discriminate;
              simpl; eapply IHYOs''; try eassumption.
    repeat rewrite app_length; unfold Extract_TyVar; repeat rewrite map_length.
    rewrite H21; generalize (length_List_P2 _ _ _ _ _ sub_Vs_Y0s0) eq_ZQs'; clear; intros.
    unfold Tys_Trans in H; unfold Typs_Trans in H; repeat rewrite map_length in H.
    assert (exists YOs'', YOs'' = YOs) as ex_YOs'' by (eexists _; reflexivity);
      destruct ex_YOs'' as [YOs'' eq_YOs'']; revert eq_ZQs'; rewrite <- eq_YOs'' at 1; intros eq_YOs'.
    assert (exists fresh_tys', fresh_tys1 = fresh_tys') as ex_FT' by (eexists _; reflexivity);
      destruct ex_FT' as [fresh_tys' eq_FT']; revert eq_YOs'; rewrite eq_FT' at 1; intros eq_YOs'.
    assert (length YOs'' = length YOs') as len_YOs by
      (generalize YOs' YOs fresh_tys1 fresh_tys' eq_YOs'; clear; induction YOs'';
        destruct fresh_tys'; simpl; intros; try discriminate;
          try (injection eq_YOs'; intros; subst; auto; fail);
            caseEq (zip fresh_tys' (map (fun typ' : GTy * N =>
              N_Trans YOs (map (fun Y : TX => Ty_Wrap (TyVar Y)) fresh_tys1)
              (snd typ')) YOs'') (fun x : TX => pair (TyVar x))); rewrite H in eq_YOs';
            try discriminate; injection eq_YOs'; intros; subst;
              rewrite (IHYOs'' _ _ _ _ H); reflexivity); congruence.
  Qed.

  Variable mtype_build_mtye : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> mty_def_ext -> Prop.  
  Variable GJ_cld_ext_unwrap : cld_ext -> @GJ_definitions.cld_ext cld_def_ext.
  Variable build_cte_Free_Vars : forall ce te', ce_build_cte ce te' -> 
    forall Y Zs, TE_Free_Vars te' Zs -> In Y Zs -> In Y (Extract_TyVar (fst (GJ_cld_ext_unwrap ce))).
  Variable WF_class_ext_TE_trans : forall gamma delta c ce te te', ce_build_cte ce te' -> 
    L_WF_Ext gamma ce c -> wf_class_ext' delta ce te ->
    te = TE_trans te' (Extract_TyVar (fst (GJ_cld_ext_unwrap ce))) (fst (GJ_ty_ext_unwrap te)).
  Variable map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop.
  Variable mtype_build_tys : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> list Ty -> list Ty -> Prop.
  Variable Build_S0''' : forall (ce : cld_ext) (me : md_ext) (gamma gamma' : Context)
    (te te' : ty_ext) (c : C)
    (vds : list VD) (S0 T0 : Ty) (delta : Context) 
    (e e' : E) (D D' : Ty) (mtye : mty_def_ext) (mce : m_call_ext)
    (Ds Ds' : list Ty) (Vars : list (Var _ * Ty))
    (ce_WF : L_WF_Ext gamma' ce c)
    (build_gamma' : L_build_context ce gamma')
    (wf_me : Meth_WF_Ext gamma ce me)
    (build_te' : ce_build_cte ce te')
    (Bound_te : forall Y Zs, TE_Free_Vars te' Zs -> In Y Zs -> In Y (Extract_TyVar (fst (GJ_cld_ext_unwrap ce)))),
    Meth_build_context ce me
    (cFJ.update_list _ Ty Context Update Empty
      ((this _, FJ_Ty_Wrap (ty_def _ ty_ext te' (cl _ c)))
        :: map (fun Tx : VD => match Tx with | vd ty x => (var _ x, ty) end) vds)) gamma ->
    E_WF gamma e S0 ->
    subtype gamma S0 T0 ->
    wf_class_ext' delta ce te ->
    mtype_build_mtye ce te T0 vds me mtye -> 
    map_mbody ce te mce me e e' ->
    mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) ->
    WF_mtype_U_map delta mce mtye D D' ->
    WF_mtype_ext delta mce mtye ->
    WF_mtype_Us_map delta mce mtye Ds Ds' ->
    List_P1 (fun Tx : VD => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
    zip (this _ :: map (fun Tx : VD => match Tx with | vd _ x => var _ x end) vds)
    (FJ_Ty_Wrap (ty_def _ _ (TE_trans te' (Extract_TyVar (fst (GJ_cld_ext_unwrap ce))) (fst (GJ_ty_ext_unwrap te)))
      (cl _ c)) :: Ds') (@pair _ _) =  Some Vars ->
    mtype_build_tys ce te T0 vds me 
    (map (fun vd' : VD => match vd' with | vd ty _ => ty end) vds) Ds ->
    exists S0'' : Ty,
      subtype delta S0'' D' /\ E_WF (cFJ.update_list _ Ty Context Update delta Vars) e' S0''.
  
  Lemma Build_S0'' : forall (ce : cld_ext) (me : md_ext) (gamma gamma' : Context)
    (te te' : ty_ext) (c : C)
    (vds : list VD) (S0 T0 : Ty) (delta : Context) 
    (e e' : E) (D D' : Ty) (mtye : mty_def_ext) (mce : m_call_ext)
    (Ds Ds' : list Ty) (Vars : list (Var _ * Ty))
    (ce_WF : L_WF_Ext gamma' ce c)
    (build_gamma' : L_build_context ce gamma')
    (wf_me : Meth_WF_Ext gamma ce me)
    (build_te' : ce_build_cte ce te'),
    Meth_build_context ce me
    (cFJ.update_list _ Ty Context Update Empty
      ((this _, FJ_Ty_Wrap (ty_def _ ty_ext te' (cl _ c)))
        :: map (fun Tx : VD => match Tx with | vd ty x => (var _ x, ty) end) vds)) gamma ->
    E_WF gamma e S0 ->
    subtype gamma S0 T0 ->
    wf_class_ext' delta ce te ->
    mtype_build_mtye ce te T0 vds me mtye -> 
    map_mbody ce te mce me e e' ->
    mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) ->
    WF_mtype_U_map delta mce mtye D D' ->
    WF_mtype_ext delta mce mtye ->
    WF_mtype_Us_map delta mce mtye Ds Ds' ->
    List_P1 (fun Tx : VD => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
    zip (this _ :: map (fun Tx : VD => match Tx with | vd _ x => var _ x end) vds)
    (FJ_Ty_Wrap (ty_def _ _ te (cl _ c)) :: Ds') (@pair _ _) =  Some Vars ->
    mtype_build_tys ce te T0 vds me 
    (map (fun vd' : VD => match vd' with | vd ty _ => ty end) vds) Ds ->
    exists S0'' : Ty,
      subtype delta S0'' D' /\ E_WF (cFJ.update_list _ Ty Context Update delta Vars) e' S0''.
    intros; eapply Build_S0'''; try eassumption.
    intros; eapply build_cte_Free_Vars; eauto.
    erewrite <- (WF_class_ext_TE_trans _ _ _ _ _ _ build_te'); try eassumption.
  Qed.

  End Build_S0''_Section.

  Section Lemma_2_7_sec. 

    Variable (GJ_WF_Type_invert : forall gamma ty, WF_Type gamma (Ty_Wrap ty) -> GJ_WF_Type gamma ty).
    
    Definition ex_WF_Bound'_P S :=
      forall delta (WF_S : WF_Type delta S), exists S', Bound' delta S (N_Wrap S').
    
    Lemma FJ_ex_WF_Bound' : forall te c, ex_WF_Bound'_P (FJ_Ty_Wrap (ty_def _ _ te c)).
      unfold ex_WF_Bound'_P; intros; eexists _; apply N_Bound'_Wrap; constructor.
    Qed.
    
    Lemma GJ_ex_WF_Bound' : forall Y, ex_WF_Bound'_P (Ty_Wrap (TyVar Y)).
      unfold ex_WF_Bound'_P; intros; apply GJ_WF_Type_invert in WF_S; inversion WF_S; subst;
        apply GJ_Ty_Wrap_inject in H; injection H; intros; subst; eexists _; 
          apply GJ_Bound'_Wrap; constructor; eassumption.
    Qed.

    Definition Lem_2_7_P T :=
      forall (delta delta_1 : Context) (Xs : list TX) (Ns : list N) 
        (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) T',
        length Xs = length Us -> 
        zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
        delta = (update_Tlist (update_list Empty vars) XNs) -> 
        List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) -> 
        List_P1 (WF_Type delta_1) Us -> 
        List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
        Bound' (update_Tlist (update_list Empty vars) XNs) T T' ->
        exists T'', Bound' delta_1 (Ty_trans T Xs Us) T'' /\
          subtype delta_1 T'' (Ty_trans T' Xs Us).

    Variable Strengthen_Bound' : forall S, Strengthen_Bound'_P S.
    Variable N_Bound'_Empty : forall S T, Bound' Empty S T -> N_Bound Empty S T.
    Variable FJ_NTy_trans_invert : forall ty txs tys, Ty_trans (FJ_N_Ty_Wrap ty) txs tys = FJ_Ty_Trans ty txs tys.
    Variable ex_WF_Bound' : forall S, ex_WF_Bound'_P S.

    Lemma Bound'_Trans : forall (b : N) delta Xs Us, Bound' delta (Ty_trans b Xs Us) (Ty_trans b Xs Us).
      intros; rewrite <- Ty_trans_eq_NTy_trans; apply N_Bound'_Wrap; constructor.
    Qed.

   Lemma FJ_Lem_2_7 : forall te c, Lem_2_7_P (FJ_Ty_Wrap (ty_def _ _ te c)).
     unfold Lem_2_7_P; intros; apply N_Bound'_invert in H5.
       rewrite FJ_Ty_trans_invert; simpl; inversion H5; subst; apply N_Wrap_inject in H8;
         injection H8; intros; subst; eexists _; split.
       apply N_Bound'_Wrap; econstructor.
       rewrite FJ_NTy_trans_invert; simpl; apply FJ_subtype_Wrap; constructor.
   Qed.

   Lemma GJ_Lem_2_7 : forall Y, Lem_2_7_P (Ty_Wrap (TyVar Y)).
     unfold Lem_2_7_P; intros; destruct (GJ_Bound'_invert' _ _ _ H5) as [n [T'_eq Bound_Y]];
       subst.
     inversion Bound_Y; subst; apply GJ_Ty_Wrap_inject in H1; injection H1; intros; subst; clear H1 H5.
     assert (exists i, exists n', nth_error XNs i = Some (TyVar Y, n') /\ nth_error Xs i = Some Y /\
     nth_error Ns i = Some n' /\ TLookup (update_Tlist (update_list Empty vars) XNs) Y n'
     /\ exists U, nth_error Us i = Some U /\ GTy_trans (TyVar Y) Xs Us = U).
     generalize Ns XNs Us TLookup_TUpdate_eq TLookup_TUpdate_neq TLookup_TUpdate_neq' TLookup_Empty TX_eq_dec
       TLookup_id H7 H0 H; clear; induction Xs; destruct Ns; destruct Us; simpl; intros;
         try discriminate; injection H0; intros; subst; clear H0; simpl in H7.
     apply TLookup_Update_list in H7; apply TLookup_Empty in H7; elimtype False; assumption.
     caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); rewrite H0 in H1; try discriminate; 
       injection H1; intros; subst; clear H1; simpl in H7; injection H; clear H; intro H.
     destruct (TX_eq_dec Y a); subst.
     exists 0; exists n; simpl; repeat split; auto.
     rewrite (TLookup_id _ _ _ _ H7 (TLookup_TUpdate_eq _ _ _)); reflexivity.
     rewrite (TLookup_id _ _ _ _ H7 (TLookup_TUpdate_eq _ _ _)); reflexivity.
     destruct (TX_eq_dec a a); try (elimtype False; auto; fail); exists t; split; reflexivity.
     apply TLookup_TUpdate_neq' in H7; auto.
     destruct (IHXs Ns l Us) as [i [n' [nth_XNs [nth_Xs [nth_Ns [TLookup_Y [U [nth_U Trans_Y]]]]]]]];
       try assumption.
     exists (S i); exists n'; simpl; repeat split; auto.
     exists U; destruct (TX_eq_dec a Y); try (elimtype False; auto; fail); split; auto.
     destruct H1 as [i [n' [nth_XNs [nth_Xs [nth_Ns [TLookup_Y [U [nth_U Trans_Y]]]]]]]].
     rewrite (TLookup_id _ _ _ _ H7 TLookup_Y) in *|-*; clear H7.
     rewrite GJ_Ty_trans_invert; rewrite Trans_Y; clear Trans_Y.
     destruct H2 as [In_U _]; destruct (In_U _ _ nth_U) as [b [nth_Ns' sub_U_b]]; rewrite nth_Ns in nth_Ns'; 
       injection nth_Ns'; intros; subst; clear nth_Ns'.
     destruct (ex_WF_Bound' _ _ (In_List_P1' _ _ _ H3 _ (nth_error_in _ _ _ _ nth_U))) as [U' Bound_U].
     exists U'; split; auto.
     eapply sub_Bound'.
     apply sub_U_b.
     apply Bound'_Trans.
     assumption.
   Qed.

   End Lemma_2_7_sec. 
   
   Section Lemma_2_11_sec.
     
    Variables 
      (mbody_m_call_map : TyP_List -> list Ty  -> m_call_ext -> m_call_ext -> Prop)
      (mbody_new_map : TyP_List -> list Ty -> ty_ext -> ty_ext -> Prop)
      (m_call_ext' : Set)
      (Lem_2_7' : forall T (delta delta_1 : Context) (Xs : list TX) (Ns : list N)
          (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) T',
          length Xs = length Us ->
          zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
          delta = (update_Tlist (update_list Empty vars) XNs) ->
          List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) ->
          List_P1 (WF_Type delta_1) Us ->
          List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
          WF_fields_map (update_Tlist (update_list Empty vars) XNs) T T' ->
          exists T'', WF_fields_map delta_1 (Ty_trans T Xs Us) T'' /\
          subtype delta_1 T'' (Ty_trans T' Xs Us))
      (Bound_N : forall delta ty ty', Bound' delta ty ty' -> exists n, ty' = N_Wrap n).
    Variable E_Ty_trans' : TyP_List -> list Ty -> E -> E -> Prop. 

    Definition Lem_2_11_P delta e T (WF_e : E_WF delta e T) :=
      forall (delta_1 : Context)
        (Xs : list TX) (Ns : list N) (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) e',
        length Xs = length Us -> 
        zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
        delta = (update_Tlist (update_list Empty vars) XNs) -> 
        List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) -> 
        List_P1 (WF_Type delta_1) Us -> 
        List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
        E_Ty_trans' XNs Us e e' ->
        exists T', E_WF (update_list delta_1 (map 
          (fun v => match v with 
                      (v, ty) => (v, Ty_trans ty Xs Us) end) vars))
        e' T' /\ subtype delta_1 T' (Ty_trans T Xs Us).

    Definition Lem_2_11_Q delta es Ts (WF_es : List_P2' (E_WF delta) es Ts) :=
      forall (delta_1 : Context)
        (Xs : list TX) (Ns : list N) (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) es',
        length Xs = length Us -> 
        zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
        delta = (update_Tlist (update_list Empty vars) XNs) -> 
        List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) -> 
        List_P1 (WF_Type delta_1) Us -> 
        List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
        List_P2' (E_Ty_trans' XNs Us) es es' -> 
        exists Ts', List_P2' (E_WF (update_list delta_1 (map 
          (fun v => match v with 
                      (v, ty) => (v, Ty_trans ty Xs Us) end) vars)))
        es' Ts' /\ List_P2' (subtype delta_1) Ts' (map (fun T => Ty_trans T Xs Us) Ts).

    Variable (map_e_invert : forall XNs Us e e', 
      E_Ty_trans' XNs Us (FJ_E_Wrap e) e' -> 
      E_Ty_Trans _ _ FJ_E_Wrap mbody_m_call_map mbody_new_map E_Ty_trans' XNs Us (FJ_E_Wrap e) e') 
      (FJ_E_Wrap_inject : forall e e', FJ_E_Wrap e = FJ_E_Wrap e' -> e = e')
      (lookup_TUpdate : forall gamma X N x ty, lookup (TUpdate gamma X N) x ty -> lookup gamma x ty)
      (lookup_TUpdate' : forall gamma X N x ty, lookup gamma x ty -> lookup (TUpdate gamma X N) x ty)
      (lookup_update_eq : forall gamma X ty, lookup (Update gamma X ty) X ty) 
      (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
        lookup (Update gamma Y ty') X ty)
      (lookup_update_neq' : forall gamma Y X ty ty', lookup (Update gamma Y ty') X ty -> X <> Y -> 
        lookup gamma X ty)
      (lookup_Empty : forall X ty, ~ lookup Empty X ty)
      (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty')
      (x_eq_dec : forall x y : X, {x = y} + {x <> y})
      (WF_fields_map_sub : forall X delta Y, WF_fields_map delta X Y -> subtype delta X Y)
      (Lem_2_8 : forall delta S T (sub_S_T : subtype delta S T) T' fds', 
        WF_fields_map delta T T' -> fields Empty T' fds' -> exists S', 
          WF_fields_map delta S S'  /\ exists fds, fields Empty S' fds /\ 
            (forall fd' n, nth_error fds' n = Some fd' -> nth_error fds n = Some fd'))
      (Strengthen_WF_fields_map : forall S delta vars T, WF_fields_map delta S T -> WF_fields_map (update_list delta vars) S T).

    Lemma lookup_update_Tlist : forall XNs gamma x ty, lookup (update_Tlist gamma XNs) x ty -> lookup gamma x ty.
      induction XNs; simpl; intros; auto; destruct a; destruct g; apply lookup_TUpdate in H; auto.
    Qed.
      
    Lemma lookup_update_Tlist' : forall XNs gamma x ty, lookup gamma x ty -> lookup (update_Tlist gamma XNs) x ty.
      induction XNs; simpl; intros; auto; destruct a; destruct g; apply lookup_TUpdate'; auto.
    Qed.

    Lemma FJ_Lem_2_11_H1 : forall gamma x ty lookup_x, 
      Lem_2_11_P _ _ _ (FJ_E_WF_Wrap _ _ _ (T_Var _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gamma x ty lookup_x)).
      unfold Lem_2_11_P; intros. 
      generalize (map_e_invert _ _ _ _ H5); intros map_e; clear H5;
        inversion map_e; subst; try (apply FJ_E_Wrap_inject in H5; discriminate).
      apply FJ_E_Wrap_inject in H8; injection H8; intros; subst; clear H8;
        exists (Ty_trans ty Xs Us); split.
      apply FJ_E_WF_Wrap; constructor.
      apply lookup_update_Tlist in lookup_x; generalize lookup_update_eq lookup_update_neq lookup_update_neq' 
        lookup_x x_eq_dec lookup_Empty lookup_id; clear; induction vars; simpl; intros.
      elimtype False; eapply lookup_Empty; eassumption.
      destruct a; destruct v; destruct x;
        try (apply lookup_update_neq; try congruence; apply IHvars; 
          auto; apply lookup_update_neq' in lookup_x; congruence).
      destruct (x_eq_dec x x0); subst.
      rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)); apply lookup_update_eq.
      apply lookup_update_neq; try congruence; apply IHvars; auto; apply lookup_update_neq' in lookup_x; congruence.
      rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)); apply lookup_update_eq.
      apply FJ_subtype_Wrap; constructor.
    Defined.

    Definition Ty_trans_fields_P delta S fds (fields_S : fields delta S fds) :=
      forall Xs Us, delta = Empty -> fields Empty (Ty_trans S Xs Us) 
        (map (fun fd' : cFJ.FD F Ty =>
          match fd' with
            | fd ty0 f0 => fd F Ty (Ty_trans ty0 Xs Us) f0
          end) fds).

    Variables (fields_build_te' : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
      (fields_build_tys' : ty_ext -> cld_ext -> list Ty -> list Ty -> Prop)
      (obj_TE_trans_fields_build_te' : forall gamma ce te te'' te' Xs Us,
        L_build_context ce gamma -> wf_object_ext' gamma te'' ->
        fields_build_te' ce te te'' te' -> 
        fields_build_te' ce (TE_trans te Xs Us) te'' (TE_trans te' Xs Us))
      (class_TE_trans_fields_build_te' : forall gamma ce ce' te te'' te' Xs Us,
        L_build_context ce gamma -> wf_class_ext' gamma ce' te'' ->
        fields_build_te' ce te te'' te' -> 
        fields_build_te' ce (TE_trans te Xs Us) te'' (TE_trans te' Xs Us))
      (TE_trans_fields_build_tys' : forall gamma ce te te' te'' Xs Us tys tys', 
        L_build_context ce gamma -> List_P1 (WF_Type gamma) tys' -> 
        fields_build_te' ce te te' te'' ->
        fields_build_tys' te ce tys' tys -> 
        fields_build_tys' (TE_trans te Xs Us) ce tys'
        (map (fun ty : Ty => Ty_trans ty Xs Us) tys)).

    Lemma GJ_obj_TE_trans_fields_build_te' : forall
      (fields_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
      gamma (ce : @GJ_definitions.cld_ext cld_def_ext) (te te'' te' : @GTy_ext ty_def_ext) Xs Us,
      GJ_definitions.L_build_context L_build_context' ce gamma -> GJ_wf_object_ext gamma te'' -> 
      fields_build_te fields_build_te' ce te te'' te' -> 
      fields_build_te fields_build_te' ce (GJ_TE_Trans te Xs Us) te'' (GJ_TE_Trans te' Xs Us).
      intros; inversion H1; inversion H0; subst; unfold GJ_TE_Trans; simpl.
      injection H9; intros; subst; simpl.
      econstructor.
      assumption.
      rewrite len_map; assumption.
    Qed.

    Lemma GJ_class_TE_trans_fields_build_te' : forall 
      (fields_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
      gamma (ce ce' : @GJ_definitions.cld_ext cld_def_ext) (te te'' te' : @GTy_ext ty_def_ext) Xs Us,
      GJ_definitions.L_build_context L_build_context' ce gamma -> 
      GJ_wf_class_ext gamma ce' te'' -> 
      fields_build_te fields_build_te' ce te te'' te' -> 
      fields_build_te fields_build_te' ce (GJ_TE_Trans te Xs Us) te'' (GJ_TE_Trans te' Xs Us).
      intros; inversion H; inversion H0; inversion H1; subst; unfold GJ_TE_Trans; simpl.
      injection H15; injection H13; intros; subst; clear H13 H15.
      assert (List_P1 (WF_Type (update_Tlist Empty XNs)) tys) as WF_tys by
        (generalize L_build_context'_Empty_1 H2 H5; clear; induction tys; intros; constructor;
          inversion H5; eauto).
      destruct (exists_Free_Vars_P2 tys) as [Ys' FV_tys].
      apply P2'_if_P2 in FV_tys.
      generalize (GJ_wf_free_vars' _ _ WF_tys _ _ (refl_equal _) FV_tys) as Bound_tys; intro.
      assert (GJ_TE_Free_Vars (tys, te'0) (fold_right (@app _) nil Ys')) by
        (generalize FV_tys; clear; intros; constructor; auto).
      generalize (GJ_map_Ty_trans_Q (tys, te'0) Xs _ Us tys0 XNs H3).
      unfold GJ_TE_Trans; simpl; intros.
      unfold Tys_Trans.
      rewrite H4; auto.
      constructor; auto.
      rewrite len_map; assumption.
    Qed.

    Lemma FJ_WF_fields_build_tys : forall gamma ce te tys tys', List_P1 (WF_Type gamma) tys -> 
      FJ_fields_build_tys _ ce te tys tys' -> List_P1 (WF_Type gamma) tys'.
      intros; inversion H0; subst; assumption.
    Qed.

    Lemma GJ_TE_trans_fields_build_tys' : forall (fields_build_tys' : ty_def_ext -> cld_def_ext -> list Ty -> list Ty -> Prop)
      (fields_build_te' : cld_def_ext -> ty_def_ext -> ty_def_ext -> ty_def_ext -> Prop)
      (WF_fields_build_tys' : forall gamma ce te tys tys', List_P1 (WF_Type gamma) tys -> 
        fields_build_tys' ce te tys tys' -> List_P1 (WF_Type gamma) tys')
      gamma (ce : @GJ_definitions.cld_ext cld_def_ext) (te te' te'' : @GTy_ext ty_def_ext) Xs Us tys tys',
      GJ_definitions.L_build_context L_build_context' ce gamma -> List_P1 (WF_Type gamma) tys' ->
      fields_build_te fields_build_te' ce te te' te'' -> 
      fields_build_tys fields_build_tys' te ce tys' tys -> 
      fields_build_tys fields_build_tys' (GJ_TE_Trans te Xs Us) ce tys'
      (map (fun ty : Ty => Ty_trans ty Xs Us) tys).
      intros; inversion H; inversion H1; inversion H2; subst; unfold GJ_TE_Trans; simpl.
      injection H8; injection H13; injection H14; intros; subst; simpl.
      assert (List_P1 (WF_Type (update_Tlist Empty XNs)) tys') as WF_tys by
        (generalize L_build_context'_Empty_1 H0 H3; clear; induction tys'; intros; constructor;
          inversion H0; eauto).
      generalize (WF_fields_build_tys' _ _ _ _ _ WF_tys H12); intros WF_tys'1.
      destruct (exists_Free_Vars_P2 tys'1) as [Ys' FV_tys].
      apply P2'_if_P2 in FV_tys.
      generalize (GJ_wf_free_vars' _ _ WF_tys'1 _ _ (refl_equal _) FV_tys) as Bound_tys; intro.
      assert (GJ_TE_Free_Vars (tys'1, te'0) (fold_right (@app _) nil Ys')) by
        (generalize FV_tys; clear; intros; constructor; auto).
      generalize (GJ_map_Ty_trans_Q (tys'1, te'0) Xs _ Us tys0 XNs H4 H7 Bound_tys).
      unfold GJ_TE_Trans; simpl; intros G1; injection G1; intros.
      unfold Tys_Trans.
      rewrite H5; auto.
      constructor; auto.
    Qed.

    Definition FJ_fields := cFJ.FJ_fields _ _ _ _ _ Ty FJ_Ty_Wrap _ _ _ CT Context fields 
      fields_build_te' fields_build_tys'.

    Variables (FJ_fields_Wrap : forall gamma ty fds, FJ_fields gamma ty fds -> fields gamma ty fds).
    
    Lemma map_app : forall A B (f : A -> B) As As', map f (As ++ As') = (map f As) ++ (map f As').
      clear; induction As; simpl; intros; congruence.
    Qed.

    Lemma Ty_trans_fields_H1 : forall te gamma, 
      Ty_trans_fields_P _ _ _ (FJ_fields_Wrap _ _ _ (fields_Obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ te gamma)).
      unfold Ty_trans_fields_P; intros; subst; rewrite FJ_Ty_trans_invert; simpl.
      apply FJ_fields_Wrap; constructor.
    Qed.

    Variable (FJ_WF_Type_invert : forall gamma ty, WF_Type gamma (FJ_Ty_Wrap ty) -> 
      FJ_WF_Type gamma (FJ_Ty_Wrap ty))
    (Ty_trans_fields : forall delta S fds fields_S, Ty_trans_fields_P delta S fds fields_S).

    Lemma Ty_trans_fields_H2: forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
      Ty_trans_fields_P _ _ _ par_fds -> 
      Ty_trans_fields_P _ _ _ (FJ_fields_Wrap _ _ _ (fields_cl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
        gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys)).
      unfold Ty_trans_fields_P; intros; subst; rewrite FJ_Ty_trans_invert; simpl.
      generalize (H Xs Us (refl_equal _)); clear H; intros fields_d.
      rewrite map_app; apply FJ_fields_Wrap.
      assert (map
        (fun fd' : cFJ.FD F Ty =>
         match fd' with
         | fd ty0 f0 => fd F Ty (Ty_trans ty0 Xs Us) f0
         end) (Zip_Fields F Ty tys (snd (Unzip_Fields F Ty c_fds))) = 
        Zip_Fields F Ty (map (fun ty => (Ty_trans ty Xs Us)) tys) (snd (Unzip_Fields F Ty c_fds))).
      clear; generalize c_fds; induction tys; destruct c_fds; simpl; intros; auto.
      destruct c_fds; simpl; auto; destruct f; simpl; rewrite IHtys; reflexivity.
      destruct c_fds0; simpl; auto; destruct f0; simpl; rewrite IHtys; reflexivity.
      rewrite H.      
      rewrite FJ_Ty_trans_invert in fields_d; simpl in fields_d.
      generalize (WF_CT _ _ c_eq); intros WF_c; inversion WF_c; subst.
      assert (List_P1 (WF_Type gamma) (fst (Unzip_Fields F Ty c_fds))) by 
        (generalize H13; clear; induction c_fds; simpl; try econstructor;
          destruct a; intros; inversion H13; subst; simpl; econstructor; auto).
      apply FJ_WF_Type_invert in H14; inversion H14; apply FJ_Ty_Wrap_inject in H1; injection H1; intros; subst.
      econstructor; try eassumption.
      eapply obj_TE_trans_fields_build_te'; try eassumption.
      eapply TE_trans_fields_build_tys'; try eassumption.
      econstructor; try eassumption.
      eapply class_TE_trans_fields_build_te'; try eassumption.
      eapply TE_trans_fields_build_tys'; try eassumption.
    Defined.
    
    Variable (Trans_WF_fields_map : forall ty delta delta' ty' Xs Us, 
      WF_fields_map delta ty ty' -> WF_fields_map delta' (Ty_trans ty' Xs Us) (Ty_trans ty' Xs Us)).

    Definition Trans_WF_fields_map_P S := forall delta delta' S' Xs Us, 
      Bound' delta S S' -> Bound' delta' (Ty_trans S' Xs Us) (Ty_trans S' Xs Us).
    
    Lemma FJ_Trans_WF_fields_map : forall te c, Trans_WF_fields_map_P (FJ_Ty_Wrap (ty_def _ _ te c)).
      unfold Trans_WF_fields_map_P; intros; apply N_Bound'_invert in H; inversion H.
      apply N_Wrap_inject in H2; injection H1; intros; subst.
      rewrite <- Ty_trans_eq_NTy_trans; apply N_Bound'_Wrap; constructor.
    Qed.

    Lemma GJ_Trans_WF_fields_map : forall Y, Trans_WF_fields_map_P (Ty_Wrap (TyVar Y)).
      unfold Trans_WF_fields_map_P; intros; destruct (GJ_Bound'_invert' _ _ _ H) as [n' [eq_n' _]]; subst.
      rewrite <- Ty_trans_eq_NTy_trans; apply N_Bound'_Wrap; constructor.
    Qed.

    Lemma FJ_Lem_2_11_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, 
      Lem_2_11_P _ _ _ WF_e ->
      Lem_2_11_P _ _ _ (FJ_E_WF_Wrap _ _ _ (T_Field _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  
        gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
      unfold Lem_2_11_P; intros. 
      exists (Ty_trans ty'' Xs Us); split; try (apply FJ_subtype_Wrap; constructor).
      generalize (map_e_invert _ _ _ _ H6); intros map_e; clear H6;
        inversion map_e; subst; first [apply FJ_E_Wrap_inject in H9 | apply FJ_E_Wrap_inject in H6];
          try discriminate.
      injection H6; intros; subst; clear H6.
      destruct (H _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 H9) as [S_0 [WF_e'0 sub_S_0]].
      cut (WF_fields_map delta_1 (Ty_trans ty' Xs Us) (Ty_trans ty' Xs Us)).
      cut (exists fds'', fields Empty (Ty_trans ty' Xs Us) fds'' /\ fds'' = 
        map (fun fd' => match fd' with fd ty f => fd _ _ (Ty_trans ty Xs Us) f end) fds'); intros.
      destruct H2 as [fds'' [fields_ty' fds''_eq]].
    destruct (Lem_2_7' _ _ _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 ty_map) as [T'' [map_ty_T' sub_T''_S_0]].
    generalize (WF_fields_map_sub _ _ _ map_ty_T'); intros sub_ty_T''.
    assert (subtype delta_1 S_0 (Ty_trans ty' Xs Us)) by repeat (apply FJ_subtype_Wrap; econstructor 2; try eassumption).
    destruct (Lem_2_8 _ _ _ H2 _ _ H6 fields_ty') as [S_0' [Bound_S_0 [fds''' [fields_S_0' sub_S_0']]]].
    apply FJ_E_WF_Wrap; eapply T_Field with (i := i).
    eassumption.
    eapply Strengthen_WF_fields_map; eassumption.
    eassumption.
    eapply sub_S_0'.
    generalize i fds' nth_fds fds''_eq; clear; induction fds''; destruct i; destruct fds'; simpl; intros; try discriminate.
    destruct f0; injection fds''_eq; injection nth_fds; intros; subst; auto.
    injection fds''_eq; intros; eauto.
    generalize (Ty_trans_fields _ _ _ fds_ty' Xs Us (refl_equal _)); intros fds_trans_ty'.
    eexists _; split; auto.
    assumption.
    eapply Trans_WF_fields_map; eassumption.
  Defined.

  Variable mbody_new_map_TE_Trans : forall XNs Xs Ns Us te te', 
    zip Xs Ns (fun x : TX => pair (TyVar x)) = Some XNs -> 
    mbody_new_map XNs Us te te' -> te' = TE_trans te Xs Us.
  Variable WF_Type_update_list_id : forall gamma ty WF_ty, WF_Type_update_list_id_P gamma ty WF_ty.
  Variable update_list_WF_mtype_ty_0_map : forall S delta vars S', WF_mtype_ty_0_map delta S S' -> 
    WF_mtype_ty_0_map (update_list delta vars) S S'.
  Variable update_list_WF_mtype_U_map : forall delta vars mce mtye U U', 
    WF_mtype_U_map delta mce mtye U U' -> 
    WF_mtype_U_map (update_list delta vars) mce mtye U U'.
  Variable update_list_WF_mtype_Us_map : forall delta vars mce mtye Us Us', 
    WF_mtype_Us_map delta mce mtye Us Us' -> 
    WF_mtype_Us_map (update_list delta vars) mce mtye Us Us'.
  Variable update_list_WF_mtype_ext : forall delta vars mce mtye, WF_mtype_ext delta mce mtye -> 
    WF_mtype_ext (update_list delta vars) mce mtye.

  Lemma FJ_Lem_2_11_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
    Lem_2_11_Q _ _ _ WF_es -> 
    Lem_2_11_P _ _ _ (FJ_E_WF_Wrap _ _ _ (T_New  _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds)).
    unfold Lem_2_11_Q; unfold Lem_2_11_P; intros.
    generalize (map_e_invert _ _ _ _ H6); intros map_e; clear H6;
      inversion map_e; subst; first [apply FJ_E_Wrap_inject in H6 | apply FJ_E_Wrap_inject in H9];
        try discriminate; injection H6; intros; subst; clear H6.
    rewrite (mbody_new_map_TE_Trans _ _ _ _ _ _ H1 H10) in *|-*.
    exists (FJ_Ty_Wrap (ty_def C ty_ext (TE_trans te Xs Us) cl)); split.
    generalize (Ty_trans_fields _ _ _ fds_cl Xs Us (refl_equal _));
      rewrite FJ_Ty_trans_invert; simpl; intros fds_cl'.
    destruct (H _ _ _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5 H7) as 
      [Ts' [WF_es' sub_Ts'_Ss]].
    apply FJ_E_WF_Wrap; econstructor; try eassumption.
    apply (fun WF_ty => WF_Type_update_Tupdate _ _ WF_ty _ _ _ (refl_equal _)) in WF_cl.
    apply (fun WF_ty => WF_Type_update_list_id _ _ WF_ty _ _ (refl_equal _)) in WF_cl.
    generalize (Type_Subst_WF_2_6' _ _ WF_cl _ _ _ _ _ H0 H1 (refl_equal _) H3 H5 H4);
      clear WF_cl; intros WF_cl.
    rewrite subst_context_Empty in WF_cl; rewrite FJ_Ty_trans_invert in WF_cl;
      simpl in WF_cl; apply WF_Type_update_list_id'; rewrite app_context_Empty in WF_cl; 
        assumption.
    apply P2_if_P2'; apply P2'_if_P2 in sub_Ts'_Ss; apply P2'_if_P2 in sub_fds;
      destruct sub_Ts'_Ss as [fnd_Ts' nfnd_Ts']; destruct sub_fds as [fnd_Ss nfnd_Ss];
        split; intros.
    destruct (fnd_Ts' _ _ H2) as [S' [nth_Ss' sub_a_S']].
    assert (exists S, nth_error Ss n = Some S /\ S' = Ty_trans S Xs Us) as nth_Ss by
      (generalize n nth_Ss'; clear; induction Ss; destruct n; simpl; 
        intros; try discriminate; auto; injection nth_Ss'; exists a; split; auto).
    clear nth_Ss'; destruct nth_Ss as [S [nth_Ss S'_eq]]; subst.
    destruct (fnd_Ss _ _ nth_Ss) as [fd' [nth_fds sub_fd'_S]].
    destruct fd'; exists (fd _ _ (Ty_trans t Xs Us) f); split.
    apply (nth_error_map _ _ (fun fd' : cFJ.FD F Ty => 
      match fd' with fd ty0 f0 => fd F Ty (Ty_trans ty0 Xs Us) f0 end) _ _ _ nth_fds); auto.
    generalize (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_fd'_S _ _ _ (refl_equal _)) _ _ (refl_equal _)); 
    clear sub_fd'_S; intro sub_fd'_S.
    generalize (Type_Subst_Sub_2_5' _ _ _ sub_fd'_S _ _ _ _ _ H0 H1 (refl_equal _) H3 H4 H5);
      intros sub_fd'_S'.
    apply subtype_update_list_id'; rewrite subst_context_Empty in sub_fd'_S'; 
      rewrite app_context_Empty in sub_fd'_S'; apply FJ_subtype_Wrap; 
        econstructor; try eassumption.
    apply nfnd_Ts' in H2.
    assert (nth_error Ss n = None) as nth_Ss by 
      (generalize n H2; clear; induction Ss; destruct n; simpl; intros; 
        try discriminate; auto).
    apply nfnd_Ss in nth_Ss.
    apply nth_error_map'; assumption.
    apply FJ_subtype_Wrap; rewrite FJ_Ty_trans_invert; simpl; constructor.
  Defined.

  Lemma FJ_Lem_2_11_H5 : forall gamma, 
    Lem_2_11_Q gamma nil nil (nil_P2' (E_WF gamma)).
    unfold Lem_2_11_Q; intros.
    inversion H5; subst; exists nil; split; constructor.
  Defined.
    
  Lemma FJ_Lem_2_11_H6 : forall gamma e es ty tys WF_e WF_es,
    Lem_2_11_P gamma e ty WF_e -> 
    Lem_2_11_Q gamma es tys WF_es -> 
    Lem_2_11_Q _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
    unfold Lem_2_11_Q; unfold Lem_2_11_P; intros; inversion H7; subst.
    destruct (H _ _ _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6 H10) as [T' [WF_b sub_b_ty]].
    destruct (H0 _ _ _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6 H12) as [Ts' [WF_bs sub_bs_Ts]].
    exists (T' :: Ts'); split; constructor; auto.
  Defined.

  Definition Ty_trans_mtype_P delta m S mty' (mtype_S : mtype delta m S mty') :=
    forall (gamma delta_1 : Context) (Xs : list TX) (Ns : list N)
      (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) 
      mtye mce mce' T Ts T' Ts',
      delta = Empty -> mty' = mty _ _  mtye Ts T -> 
      length Xs = length Us ->
      zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
      gamma = (update_Tlist (update_list Empty vars) XNs) ->
      List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) ->
      List_P1 (WF_Type delta_1) Us ->
      List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
      WF_mtype_Us_map gamma mce mtye Ts Ts' -> WF_mtype_U_map gamma mce mtye T T' -> 
      WF_mtype_ext gamma mce mtye -> mbody_m_call_map XNs Us mce mce' -> 
      exists mtye', exists Vs, exists V, 
        mtype Empty m (Ty_trans S Xs Us) (mty _ _ mtye' Vs V) /\
        WF_mtype_ext delta_1 mce' mtye' /\
        WF_mtype_Us_map delta_1 mce' mtye' Vs (Tys_Trans XNs Us Ts') /\
        WF_mtype_U_map delta_1 mce' mtye' V (Ty_trans T' Xs Us).

  Variable mtype_build_tys : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> list Ty -> list Ty -> Prop.
  Variable mtype_build_mtye : cld_ext -> ty_ext -> Ty -> list (cFJ.VD X Ty) -> md_ext -> mty_def_ext -> Prop.
  Variable FJ_mtype_Wrap : forall delta m S mty', 
    FJ_mtype _ _ _ _ _ _ FJ_Ty_Wrap _ _ _ _ CT _ mtype mtype_build_te'' 
      mtype_build_tys mtype_build_mtye delta m S mty' -> mtype delta m S mty'.
  Variable Ty_trans_eq_N_Trans : forall N XNs Us, 
    N_Wrap (N_Trans XNs Us N) = Ty_trans N (Extract_TyVar XNs) Us.
  Variable Ty_trans_fresh_vars : forall T, Ty_trans_fresh_vars_P T.
    Lemma Extract_zip : forall Zs (Qs : list N) ZQs, 
      zip Zs Qs (fun x => pair (TyVar x)) = Some ZQs -> Extract_TyVar ZQs = Zs. 
      clear; induction Zs; destruct Qs; simpl; intros; try discriminate;
        injection H; intros; subst; auto; caseEq (zip Zs Qs (fun x => pair (TyVar x))); 
          rename H1 into eq_XNs; rewrite eq_XNs in H0; try discriminate; injection H0; intros; subst;
            simpl; erewrite IHZs; eauto.
    Qed.
      
    Lemma Extract_map : forall C Zs (Qs : list N) ZQs (f : N -> C),
      zip Zs Qs (fun x => pair (TyVar x)) = Some ZQs ->
      zip Zs (map (fun typ'0 => f (snd typ'0)) ZQs) (fun x => pair (TyVar x)) = 
      Some (map (fun typ'0  => (fst typ'0, f (snd typ'0))) ZQs).
      clear; induction Zs; destruct Qs; simpl; intros; try discriminate;
        injection H; intros; subst; auto; caseEq (zip Zs Qs (fun x => pair (TyVar x))); 
          rename H1 into eq_XNs; rewrite eq_XNs in H0; try discriminate; injection H0; intros; subst;
            simpl; erewrite IHZs; eauto.
    Qed.

    Variable build_context' : cld_def_ext -> md_def_ext -> Context -> Context -> Prop.
    Variable build_context'_Empty_1 : forall ce mde gamma gamma' XNs T, 
      build_context' ce mde gamma gamma' -> 
      WF_Type (update_Tlist gamma' XNs) T -> WF_Type (update_Tlist Empty XNs) T.

  Lemma length_zip : forall (B : Type) (As : list TX) (Bs : list B) (Cs : list (GTy * B)),
    zip As Bs (fun X => pair (TyVar X)) = Some Cs -> length As = length Bs /\ length Cs = length Bs.
    induction As; destruct Bs; destruct Cs; simpl; intros; try discriminate; first [split; auto; fail |
      caseEq (zip As Bs (fun X => pair (TyVar X))); rewrite H0 in H; try discriminate; injection H;
        intros; subst; destruct (IHAs _ _ H0); split; congruence].
  Qed.

  Variable build_fresh_distinct : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> distinct Zs.
  Variable build_fresh_id : forall tys ty tys' Xs Ys Zs Zs', build_fresh tys ty tys' Xs Ys Zs -> 
    build_fresh tys ty tys' Xs Ys Zs' -> Zs = Zs'.
  Variable build_fresh_new : forall tys ty vds Ws Xs Ys Zs, List_P2' (Free_Vars) tys Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.
  Variable build_fresh_new' : forall tys ty vds Ws Xs Ys Zs, List_P2' (Free_Vars) vds Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.
  Variable build_fresh_new'' : forall tys ty vds Ws Xs Ys Zs, Free_Vars ty Ws -> 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Ws.
  Variable build_fresh_new''' : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y Xs.
  Variable build_fresh_new'''' : forall tys ty vds Xs Ys Zs, 
    build_fresh tys ty vds Xs Ys Zs -> forall Y, In Y Zs -> ~ In Y (Extract_TyVar Ys).
  Variable build_fresh_new''''' : forall tys ty vds Ws Xs Ys Zs,  
    List_P2' (Free_Vars) (map (fun n => (N_Wrap (@snd _ _ n))) Ys) Ws -> build_fresh tys ty vds Xs Ys Zs -> 
    List_P1 (fun Zs' => forall Y, In Y Zs -> ~ In Y Zs') Ws.

  Lemma Tys_trans_fresh_vars : forall ZQs Vs XNs Ts YOs tys Zs Ws
    (len_Ys : length YOs = length (Extract_TyVar ZQs))
    (len_fresh_tys : length (Extract_TyVar ZQs) = length Vs) 
    (len_Xs : length XNs = length Ts)
    (distinct_fresh_tys : distinct (Extract_TyVar ZQs))
    (fresh_Xs : forall Y, In Y (Extract_TyVar ZQs) -> ~ In Y (Extract_TyVar XNs)),
    distinct ((Extract_TyVar XNs) ++ (Extract_TyVar YOs)) -> 
    List_P2' Free_Vars tys Ws ->
    List_P1 (fun Zs' => forall Y, In Y (Extract_TyVar ZQs) -> ~ In Y Zs') Ws ->
    List_P2' Free_Vars Ts Zs ->
    List_P1 (fun Zs' => forall Y, In Y (Extract_TyVar ZQs) -> ~ In Y Zs') Zs ->
    Tys_Trans ZQs Vs (Tys_Trans XNs Ts (Tys_Trans YOs (map (fun Y => Ty_Wrap (TyVar Y))
      (Extract_TyVar ZQs)) tys)) = Tys_Trans (XNs ++ YOs) (Ts ++ Vs) tys.
    unfold Tys_Trans; intros until Ws; rewrite map_map; 
      revert ZQs Vs XNs Ts YOs Zs Ws; induction tys; simpl; intros.
    reflexivity.
    inversion H0; subst; erewrite Ty_trans_fresh_vars; try erewrite IHtys;
      try eassumption.
    unfold Extract_TyVar; repeat rewrite map_app; reflexivity.    
    inversion H1; subst; auto.
    unfold Extract_TyVar at 1; rewrite map_length; assumption.
    unfold Extract_TyVar at 1; rewrite map_length; assumption.
    inversion H1; auto.
  Qed.    

  Variable Lem_2_7'' : forall T (delta delta_1 : Context) (Xs : list TX) (Ns : list N)
      (Us : list Ty) (vars : list ((Var X) * Ty)) (XNs : TyP_List) T',
      length Xs = length Us ->
      zip Xs Ns (fun x => @pair _ _ (TyVar x)) = Some XNs ->
      delta = (update_Tlist (update_list Empty vars) XNs) ->
      List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (N_Wrap N) Xs Us)) ->
      List_P1 (WF_Type delta_1) Us ->
      List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (N_Wrap N)) Ns ->
      WF_mtype_ty_0_map (update_Tlist (update_list Empty vars) XNs) T T' ->
      exists T'', WF_mtype_ty_0_map delta_1 (Ty_trans T Xs Us) T'' /\
        subtype delta_1 T'' (Ty_trans T' Xs Us).
  Variable WF_mtype_map_sub : forall delta S S', WF_mtype_ty_0_map delta S S' -> subtype delta S S'.
  Variable WF_mtype_ty_0_map_total : forall delta S T, subtype delta S T -> forall T',
      WF_mtype_ty_0_map delta T T' ->  exists S', WF_mtype_ty_0_map delta S S'.
  Variable sub_wf_mtype_ty_0_map : forall delta S T (sub_S_T : subtype delta S T) S' T', 
      WF_mtype_ty_0_map delta T T' -> WF_mtype_ty_0_map delta S S' -> subtype delta S' T'.
  Variable Ty_trans_mtype : forall delta m S mty' mtype_S, Ty_trans_mtype_P delta m S mty' mtype_S.
  Variable Lem_2_9 : forall delta S T (sub_S_T : subtype delta S T) S' T' m mtye Us Us' U U' mce,  
      WF_mtype_ty_0_map delta T T' -> mtype Empty m T' (mty _ _ mtye Us U) -> 
    WF_mtype_U_map delta mce mtye U U' -> 
    WF_mtype_Us_map delta mce mtye Us Us' -> 
    WF_mtype_ext delta mce mtye -> 
    WF_mtype_ty_0_map delta S S' -> 
    exists V, exists Vs, exists mtye',
      mtype Empty m S' (mty _ _ mtye' Vs V) /\ 
      exists V', WF_mtype_U_map delta mce mtye' V V' /\
        WF_mtype_Us_map delta mce mtye' Vs Us' /\
        subtype delta V' U' /\
        WF_mtype_ext delta mce mtye'.
  Variable Trans_WF_mtype_map : forall ty delta delta' ty' Xs Us, 
    WF_mtype_ty_0_map delta ty ty' -> WF_mtype_ty_0_map delta' (Ty_trans ty' Xs Us) (Ty_trans ty' Xs Us).
  
  Lemma FJ_Lem_2_11_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es 
    WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye, 
    Lem_2_11_P _ _ _ WF_e_0 -> Lem_2_11_Q _ _ _ WF_es -> 
    Lem_2_11_P _ _ _ (FJ_E_WF_Wrap _ _ _ (T_Invk  _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ gamma e_0 ty_0 ty_0' U U' m mtye 
      mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
    unfold Lem_2_11_P at 2; intros.
    generalize (map_e_invert _ _ _ _ H7); intros map_e; clear H7;
      inversion map_e; subst; first [apply FJ_E_Wrap_inject in H7 | apply FJ_E_Wrap_inject in H10];
        try discriminate; injection H7; intros; subst; clear H7.
    rename ty_0 into T_0.
    destruct (H _ _ _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6 H8) as [S_0 [WF_e'0 sub_S_0_T_0]].
    destruct (H0 _ _ _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6 H9) as [Ss' [WF_e's sub_Ss'_Ss]].
    clear H H0 H8 H9.
    destruct (Lem_2_7'' _ _ _ _ _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6 ty_0_map) as
      [T_0' [map_T_0 sub_T_0']].
    destruct (WF_mtype_ty_0_map_total _ _ _ sub_S_0_T_0 _ map_T_0) as [S_0' map_S_0].
    generalize (sub_wf_mtype_ty_0_map _ _ _ sub_S_0_T_0 _ _ map_T_0 map_S_0) 
      as sub_S_0'_T_0'; intros.
    assert (subtype delta_1 S_0 (Ty_trans ty_0' Xs Us0)) by
      (apply WF_mtype_map_sub in map_T_0; repeat apply FJ_subtype_Wrap; 
        econstructor; try eassumption; apply FJ_subtype_Wrap; econstructor;
          eassumption).
    destruct (Ty_trans_mtype _ _ _ _ mtype_m _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
      (refl_equal _) (refl_equal _) H1 H2 (refl_equal _) H4 H5 H6 map_Us map_U 
      WF_mtye H12) as [mtye' [Vs [V [mtype_ty_0' [WF_mtye' [map_Vs map_V]]]]]].
    generalize (Trans_WF_mtype_map _ _ delta_1 _ Xs Us0 ty_0_map) as map_ty_0'; intro.
    destruct (Lem_2_9 _ _ _ H _ _ _ _ _ _ _ _ _ map_ty_0' mtype_ty_0'
      map_V map_Vs WF_mtye' map_S_0) as [W [Ws [mtye'' [mtype_S_0' [W' [map_W [map_Ws [sub_W_V WF_mce''_mtye'']]]]]]]].
    exists W'; split; auto.
    apply FJ_E_WF_Wrap; econstructor; try eassumption.
    apply update_list_WF_mtype_ty_0_map; assumption.
    apply update_list_WF_mtype_Us_map; eassumption.
    apply update_list_WF_mtype_U_map; assumption.
    apply P2_if_P2'; apply P2'_if_P2 in sub_Ss'_Ss; apply P2'_if_P2 in sub_Ss_Us'; 
      destruct sub_Ss'_Ss as [fnd_Ss' nfnd_Ss']; destruct sub_Ss_Us' as [fnd_Ss nfnd_Ss];
        split; intros.
    apply fnd_Ss' in H0; destruct H0 as [S' [nth_Ss'' sub_a_S']].
    assert (exists S, nth_error Ss n = Some S /\ S' = Ty_trans S Xs Us0) as nth_Ss by
      (generalize n nth_Ss''; clear; induction Ss; destruct n; simpl; 
        intros; try discriminate; auto; injection nth_Ss''; exists a; split; auto).
    destruct nth_Ss as [S [nth_Ss S'_eq]]; subst.
    apply fnd_Ss in nth_Ss; destruct nth_Ss as [U'' [nth_Us'' sub_S_U'']].
    exists (Ty_trans U'' Xs Us0); split.
    assert (Extract_TyVar XNs = Xs) as eq_Xs by 
      (generalize XNs Ns H2; clear; induction Xs; destruct Ns; destruct XNs; simpl; intros; 
        try discriminate; simpl; auto;
          caseEq (zip Xs Ns (fun x : TX => pair (TyVar x))); rewrite H in H2; 
            try discriminate; destruct p; simpl in *|-*;
              injection H2; intros; subst; rewrite (IHXs _ _ H); auto).
    unfold Tys_Trans; rewrite eq_Xs.
    apply (nth_error_map _ _ (fun ty' : Ty => Ty_trans ty' Xs Us0) _ _ _ nth_Us'').
    generalize (Subtype_Update_list_id _ _ _ 
      (subtype_update_Tupdate _ _ _ sub_S_U'' _ _ _ (refl_equal _)) _ _ (refl_equal _)); 
    clear sub_S_U''; intro sub_S_U''.
    generalize (Type_Subst_Sub_2_5' _ _ _ sub_S_U'' _ _ _ _ _ H1 H2 (refl_equal _) H4 H5 H6);
      clear sub_S_U''; intros sub_S_U''.
    apply subtype_update_list_id'; rewrite subst_context_Empty in sub_S_U''; 
      rewrite app_context_Empty in sub_S_U''; apply FJ_subtype_Wrap; 
        econstructor; try eassumption.
    apply nfnd_Ss' in H0.
    assert (nth_error Ss n = None) as nth_Ss by 
      (generalize n H0; clear; induction Ss; destruct n; simpl; intros; 
        try discriminate; auto).
    apply nfnd_Ss in nth_Ss.
    apply nth_error_map'; assumption.
    apply update_list_WF_mtype_ext; assumption.
  Defined.

  Definition FJ_Lem_2_11 := FJ_FJ_E_WF_rect' _ _ _ _ _ _ FJ_Ty_Wrap 
    _ _ FJ_E_Wrap _ _ subtype WF_Type fields mtype E_WF lookup WF_fields_map
    WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF_Wrap
    _ _ FJ_Lem_2_11_H1 FJ_Lem_2_11_H2 FJ_Lem_2_11_H3 FJ_Lem_2_11_H4 FJ_Lem_2_11_H5 FJ_Lem_2_11_H6.

  End Lemma_2_11_sec.

  Variable m_call_ext' : Set.
  Variable mb_ext : Set.
  Variable build_mb_ext' : cld_def_ext -> ty_def_ext -> m_call_ext' -> md_def_ext -> mb_ext -> Prop.

  Definition build_mb_ext 
    (ce : @GJ_definitions.cld_ext cld_def_ext) (te : @GTy_ext ty_def_ext) (mce : @MCall_ext m_call_ext')
    (mde : @MD_ext md_def_ext) (mbe : mb_ext) := build_mb_ext' (snd ce) (snd te) (snd mce) (snd mde) mbe.

  Lemma build_mb_ext_tot 
    (mtype_build_tys' : cld_def_ext -> ty_def_ext -> Ty -> list VD -> md_def_ext -> list Ty -> list Ty -> Prop) : 
    forall (build_mb_ext_tot' : forall ce te mce mde ty vds tys tys', 
      mtype_build_tys' ce te ty vds mde tys tys' -> exists mb, build_mb_ext' ce te mce mde mb)
    (ce : @GJ_definitions.cld_ext cld_def_ext)
    (te : @GTy_ext ty_def_ext) (mce : @MCall_ext m_call_ext') (mde : @MD_ext md_def_ext) 
    (ty : Ty) (vds : list (cFJ.VD _ Ty)) (tys tys' : list Ty),
    mtype_build_tys mtype_build_tys' ce te ty vds mde tys tys' ->
    exists mb : mb_ext, build_mb_ext ce te mce mde mb.
    intros; inversion H; subst; destruct mce.
    destruct (build_mb_ext_tot' _ _ m _ _ _ _ _ H1) as [mb build_mb].
    exists mb; assumption.
  Qed.

End Preservation.

End GJ_definitions.
