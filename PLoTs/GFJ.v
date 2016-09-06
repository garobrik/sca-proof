Require Import cFJ.
Require Import Generic.
Require Import FJ_tactics.
Require Import List.
Require Import Arith.
Require Import Omega.

Definition CL := cFJ.CL nat.

Inductive Ty : Set :=
  Base_Ty : cFJ.FJ_Ty nat (@GTy_ext Ty unit) -> Ty
| Gty : GTy nat -> Ty.

Definition ty_ext := @GTy_ext Ty unit.
Definition N := cFJ.FJ_Ty nat (@GTy_ext Ty unit).
Definition md_ext := @MD_ext nat N unit.
Definition mb_ext := FJ_mb_ext.
Definition mty_ext := @mty_ext nat N unit.
Definition cld_ext := @cld_ext nat N unit. 
Definition m_call_ext := @MCall_ext Ty unit.

Definition N_Wrap : N -> Ty := Base_Ty.
Coercion N_Wrap : N >-> Ty.

Inductive E : Set :=
  Base_E : FJ_E nat nat nat nat ty_ext E m_call_ext -> E.

Definition TyP_List := Generic.TyP_List nat N.

Definition FD := cFJ.FD nat Ty.
Definition MD := cFJ.MD nat nat Ty E md_ext.
Definition MTy := cFJ.Mty Ty mty_ext.
Definition MB := cFJ.MB nat E mb_ext.

Definition L := cFJ.L nat nat nat nat ty_ext Ty E md_ext cld_ext.

Parameter (CT : nat -> option L).

Fixpoint Ty_trans ty txs tys : Ty :=
  match ty with 
    | Base_Ty ty' => Generic.FJ_Ty_Trans _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id (GJ_TE_Trans _ _ Ty_trans _) ty' txs tys
    | Gty ty' => GTy_trans _ eq_nat_dec _ Gty ty' txs tys
  end.

Definition build_te := @GJ_build_te _ _ N Ty_trans _ _ FJ_build_te.

Variable (Context : Set)
  (TLookup : Context -> nat -> N -> Prop)
  (Empty : Context)
  (build_fresh : list Ty -> Ty -> list Ty -> list nat -> TyP_List -> list nat -> Prop).

Inductive subtype : Context -> Ty -> Ty -> Prop :=
  Base_sub : forall gamma ty ty', cFJ.FJ_subtype nat nat nat nat _ Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E md_ext cld_ext CT Context subtype build_te gamma ty ty' -> subtype gamma ty ty'
| GJ_sub : forall gamma ty ty', Generic.GJ_subtype _ _ Gty N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ TLookup gamma ty ty' -> subtype gamma ty ty'.

Definition wf_object_ext := @GJ_wf_object_ext Ty Context unit.

Definition wf_class_ext' WF_Type := @GJ_wf_class_ext nat Ty N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) Context subtype Ty_trans WF_Type unit unit.

Inductive WF_Type : Context -> Ty -> Prop :=
  Base_WF_Type : forall gamma ty, cFJ.FJ_WF_Type _ _ _ _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) 
    _ _ _ CT Context (wf_class_ext' WF_Type) wf_object_ext gamma ty -> WF_Type gamma ty
| GJ_WF_Type : forall gamma ty, GJ_WF_Type _ _ Gty _ _ TLookup gamma ty -> WF_Type gamma ty.

Definition wf_class_ext := wf_class_ext' WF_Type.

Definition fields_build_te (ce : cld_ext) (te te' te'' : ty_ext) := 
  Generic.fields_build_te nat Ty _ Ty_trans FJ_fields_build_te ce te te' te''.

Definition fields_build_tys (te : ty_ext) (ce : cld_ext) (tys tys' : list Ty) :=
  Generic.fields_build_tys nat Ty _ Ty_trans (FJ_fields_build_tys Ty) te ce tys tys'.

Inductive fields : Context -> Ty -> list FD -> Prop :=
  FJ_fields : forall gamma ty fds, cFJ.FJ_fields _ _ _ _ _ Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ _
    CT Context fields fields_build_te fields_build_tys gamma ty fds -> fields gamma ty fds.

Definition mtype_build_te (ce : cld_ext) (te te' te'' : ty_ext) :=
  Generic.mtype_build_te nat Ty _ Ty_trans id_map_2 ce te te' te''.

Definition VD := VD Ty nat.

Definition mtype_build_tys (ce : cld_ext) (te : ty_ext) (ty : Ty) (vds : list VD) (mce : md_ext) (tys tys' : list Ty) :=
  Generic.mtype_build_tys _ _ Gty _ Ty_trans _ build_fresh id_map_5 ce te ty vds mce tys tys'.

Definition N_Trans typs Us ty : N := 
  match ty with 
    ty_def te c => ty_def nat ty_ext ((GJ_TE_Trans _ _ Ty_trans _) te (Extract_TyVar nat N typs) Us) c
  end.

Definition mtype_build_mtye (ce : cld_ext) (te : ty_ext) (ty : Ty) (vds : list VD) (me : md_ext) (mtye : mty_ext) :=
  Generic.mtype_build_mtye nat Ty Gty N _ build_fresh N_Trans 
  (fun ce te me ty vds (mtye : unit) => True) ce te ty vds me mtye.

Inductive mtype : Context -> nat -> Ty -> MTy -> Prop :=
  FJ_mtype : forall gamma m ty mty, cFJ.FJ_mtype _ _ _ _ _ Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ _ _ CT Context mtype mtype_build_te 
    mtype_build_tys mtype_build_mtye gamma m ty mty -> mtype gamma m ty mty.

Definition mbody_build_te (ce : cld_ext) (te te' te'' : ty_ext) :=
  Generic.mbody_build_te _ Ty _ Ty_trans id_map_2 ce te te' te''.

Definition mbody_m_call_map (XNs : TyP_List) (Us : list Ty) (mce mce': m_call_ext) :=
  Generic.GJ_mbody_m_call_map nat Ty N Ty_trans _ XNs Us mce mce'.

Definition mbody_new_map (XNs : TyP_List) (Us : list Ty) (mce mce': m_call_ext) :=
  Generic.GJ_mbody_new_map nat Ty N Ty_trans _ XNs Us mce mce'. 

Inductive E_Ty_Trans : TyP_List -> list Ty -> E -> E -> Prop :=
| Base_E_Ty_Trans : forall XNs Us e e', Generic.E_Ty_Trans _ _ _ _ _ _ _ _ _ _ Base_E mbody_m_call_map
  mbody_new_map E_Ty_Trans XNs Us e e' -> E_Ty_Trans XNs Us e e'.

Definition map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop :=
  Generic.map_mbody _ _ _ _ _ _ _ _ E_Ty_Trans.

Definition build_mb_ext (ce : cld_ext) (te : ty_ext) (mce : m_call_ext) (mde : md_ext) := 
  Generic.build_mb_ext _ _ _ _ _ _ _ _ FJ_build_mb_ext ce te mce mde.

Inductive mbody : Context -> m_call_ext -> nat -> Ty -> MB -> Prop :=
  FJ_mbody : forall gamma Vs m ct mb, cFJ.mbody _ _ _ _ _ Ty Base_Ty E _ _ _ CT _ mbody_build_te 
    mb_ext build_mb_ext map_mbody gamma Vs m ct mb -> mbody gamma Vs m ct mb.

Inductive Bound : Context -> Ty -> Ty -> Prop :=
  GJ_Bound : forall gamma ty ty', Generic.GJ_Bound nat _ Gty N _ TLookup gamma ty ty' -> Bound gamma ty ty'
| FJ_Bound : forall gamma ty ty', N_Bound _ _ N_Wrap _ gamma ty ty' -> Bound gamma ty ty'.

Definition WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop := 
  GJ_WF_mtype_Us_map _ _ _ _ Ty_trans _ _ (FJ_WF_mtype_Us_map Ty Context).

Definition WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop :=
  GJ_WF_mtype_U_map _ _ _ _ Ty_trans _ _ (FJ_WF_mtype_U_map Ty Context).

Definition WF_mtype_ext (gamma : Context) (mce : m_call_ext) (mtye : mty_ext) :=
  GJ_WF_mtype_ext _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ subtype Ty_trans WF_Type _ _ (FJ_WF_mtype_ext Context) gamma mce mtye.

Variable (lookup : Context -> Var nat -> Ty -> Prop).

Inductive E_WF : Context -> E -> Ty -> Prop :=
| FJ_E_WF : forall gamma e ty, 
    cFJ.FJ_E_WF _ _ _ _ _ Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id) _ _ 
    Base_E mty_ext Context subtype WF_Type fields mtype E_WF lookup Bound Bound WF_mtype_Us_map 
    WF_mtype_U_map WF_mtype_ext Empty gamma e ty -> E_WF gamma e ty.

Variable (Update : Context -> Var nat -> Ty -> Context)
  (TUpdate : Context -> nat -> N -> Context).

Definition ce_build_cte : cld_ext -> ty_ext -> Prop :=
  Generic.GJ_ce_build_cte _ Ty Gty _ (fun (ce te : unit) => True).

Definition Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop :=
  Generic.GJ_build_context _ N Context TUpdate id_map_2.

Definition Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop :=
  Generic.GJ_Meth_WF_Ext _ _ N N_Wrap Context WF_Type (fun gamma ce mde => True).

Inductive L_build_context' : unit -> Context -> Prop :=
  L_bld' : L_build_context' tt Empty.

Definition L_build_context := Generic.L_build_context nat N _ TUpdate L_build_context'.

Definition override := @Generic.override nat Ty Gty nat N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) Context Empty 
  subtype Ty_trans WF_Type nat nat build_fresh N_Trans TUpdate Update
  unit Bound unit unit unit unit FJ_build_te (FJ_WF_mtype_Us_map Ty Context) (FJ_WF_mtype_U_map Ty Context)
  (FJ_WF_mtype_ext Context) (fun ce te me ty vds (mtye : unit) => True) L_build_context' 
  id_map_5 id_map_2 (fun gamma ce mde => True) (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) mtype.

Inductive Meth_WF : nat -> MD -> Prop :=
  FJ_Meth_WF : forall c md, cFJ.Meth_WF _ _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E _ _ CT Context subtype WF_Type 
    E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override c md -> Meth_WF c md.

Definition L_WF_Ext (gamma : Context) (ce : cld_ext) := 
  Generic.L_WF_Ext nat Ty nat N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ WF_Type (fun _ _ _ => True) gamma ce.

Definition L_WF : L -> Prop :=
  cFJ.L_WF _ _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ _ CT _ subtype WF_Type 
  fields E_WF Empty Update ce_build_cte Meth_build_context Meth_WF_Ext override
  L_WF_Ext L_build_context.

Fixpoint trans (e : E) (Vars : list (Var nat)) (Es : list E) : E :=
  match e with 
    | Base_E fj_e => cFJ.FJ_E_trans _ _ _ _ _ _ _ Base_E trans eq_nat_dec fj_e Vars Es
  end.

Inductive Reduce : E -> E -> Prop :=
| FJ_S_Reduce : forall e e', FJ_Reduce _ _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _
  Base_E _ _ CT _ fields mbody_build_te mb_ext build_mb_ext map_mbody
  Empty trans e e' -> Reduce e e'
| FJ_C_Reduce : forall e e', FJ_Congruence_Reduce _ _ _ _ ty_ext E _ Base_E Reduce 
  Congruence_List_Reduce e e' -> Reduce e e'
with Congruence_List_Reduce : list E -> list E -> Prop :=
| FJ_Reduce_List : forall es es', Reduce_List _ Reduce Congruence_List_Reduce es es' -> Congruence_List_Reduce es es'.

Section WF_Proofs.

  Definition update_list := cFJ.update_list nat Ty Context Update.

  Definition update_Tlist := Generic.update_Tlist nat N _ TUpdate.

  Definition N_trans ty Xs Us : N := 
    match ty with 
      ty_def te c => ty_def nat ty_ext ((GJ_TE_Trans _ _ Ty_trans _) te Xs Us) c
    end.

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
      CT c = Some l ->
      cFJ.L_WF nat nat nat nat ty_ext Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E md_ext cld_ext CT
      Context subtype WF_Type fields E_WF Empty Update ce_build_cte
      Meth_build_context Meth_WF_Ext override L_WF_Ext
      L_build_context l).

  Definition Fields_eq_def gamma ty fds (fields_fds : fields gamma ty fds) := 
    forall gamma' fds', fields gamma' ty fds' -> fds = fds'.
  
  Lemma Base_inject : forall ty ty', Base_Ty ty = Base_Ty ty' -> ty = ty'.
    intros ty ty' H; injection H; auto.
  Qed.
  
  Lemma fields_invert : forall (gamma : Context) (ty : cFJ.FJ_Ty nat ty_ext)
    (fds : list (cFJ.FD nat Ty)),
    fields gamma (Base_Ty ty) fds ->
    cFJ.FJ_fields nat nat nat nat ty_ext Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E md_ext
    cld_ext CT Context fields fields_build_te fields_build_tys gamma
    (Base_Ty ty) fds.
    intros gamma ty fds fields_fds; inversion fields_fds; subst; assumption.
  Qed.

  Definition fields_build_te_id := Generic.fields_build_te_id nat Ty N Ty_trans _ FJ_fields_build_te_id.
  Definition fields_build_tys_id := Generic.fields_build_tys_id nat Ty N Ty_trans _ (FJ_fields_build_tys_id Ty).

  Fixpoint Fields_eq gamma ty fds (fields_fds : fields gamma ty fds) : Fields_eq_def _ _ _ fields_fds :=
    match fields_fds return Fields_eq_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => cFJ.FJ_Fields_eq _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields Base_inject fields_invert
      fields_build_te_id fields_build_tys_id _ _ _ FJ_case Fields_eq
    end.

  Definition fds_distinct_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall cl1 cl2 f m n fds',
      map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
      nth_error fds' m = Some (fd nat Ty cl1 f) -> nth_error fds n = Some (fd nat Ty cl2 f) -> m = n.

  Definition Fields_Build_tys_len := Generic.Fields_Build_tys_len nat Ty N Ty_trans _ (FJ_Fields_Build_tys_len Ty).

  Lemma Ty_Wrap_discriminate : forall ty ty', Base_Ty ty <> Gty ty'.
    congruence.
  Qed.

  Definition WF_fields_map_id'  gamma ty ty' (bound : Bound gamma ty ty') :
    forall (tye : GTy_ext Ty) (c : cFJ.CL nat),
      ty = ((Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (ty_def nat (GTy_ext Ty) tye c)) ->
      exists tye' : GTy_ext Ty, ty' =  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (ty_def nat (GTy_ext Ty) tye' c) :=
        match bound in Bound gamma ty ty' return (forall (tye : GTy_ext Ty) (c : cFJ.CL nat),
          ty = ((Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (ty_def nat (GTy_ext Ty) tye c)) ->
          exists tye' : GTy_ext Ty, ty' =  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (ty_def nat (GTy_ext Ty) tye' c)) with 
          | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_WF_fields_map_id' nat Ty _ Gty _ _ N_Wrap
            id _ TLookup Ty_Wrap_discriminate gamma' ty'' ty''' GJ_bound'
          | FJ_Bound gamma' ty'' ty''' FJ_bound' => N_WF_fields_map_id' _ _ _ _ N_Wrap id _ 
            gamma' ty'' ty''' FJ_bound'
        end.

  Definition WF_fields_map_id_def gamma cl' fds (fields_fds : fields gamma cl' fds) :=
    forall tye c tye' fds' fds'', cl' = Base_Ty (ty_def nat ty_ext tye c) -> fds'' = fds -> 
      fields gamma (Base_Ty (ty_def nat ty_ext tye' c)) fds' -> 
      map (fun fd' => match fd' with fd _ f => f end) fds' = 
      map (fun fd' => match fd' with fd _ f => f end) fds.
  
  Fixpoint WF_fields_map_id gamma ty fds (fields_fds : fields gamma ty fds) :
    WF_fields_map_id_def _ _ _ fields_fds :=
    match fields_fds return WF_fields_map_id_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fields_map_id _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields Base_inject fields_invert
      Fields_Build_tys_len  _ _ _ FJ_case WF_fields_map_id
    end.

  Definition parent_fields_names_eq_def := 
    cFJ.parent_fields_names_eq_P _ nat _ _ Base_Ty Context fields.

  Fixpoint parent_fields_names_eq gamma ty fds (fields_fds : fields gamma ty fds) : 
    parent_fields_names_eq_def _ _ _ fields_fds :=
    match fields_fds return parent_fields_names_eq_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_parent_fields_names_eq _ _ _ _ _ Ty _ _ _ _ CT Context
      fields fields_build_te fields_build_tys FJ_fields Base_inject fields_invert 
      Fields_Build_tys_len _ _ _ FJ_case parent_fields_names_eq
    end.

  Fixpoint fds_distinct gamma ty fds (fields_fds : fields gamma ty fds) : fds_distinct_def _ _ _ fields_fds :=
    match fields_fds return fds_distinct_def _ _ _ fields_fds with
      FJ_fields gamma ty fds FJ_case => FJ_fds_distinct _ _ _ _ _ Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ _ CT Context
      subtype WF_Type fields fields_build_te fields_build_tys FJ_fields E_WF Empty Update
      ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
      WF_CT parent_fields_names_eq Fields_Build_tys_len _ _ _ FJ_case fds_distinct
    end.

  Definition Weakening_def e ty gamma (WF_e : E_WF gamma e ty) :=
    forall gamma' vars, gamma = (update_list Empty vars) -> E_WF (update_list gamma' vars) e ty.

  Fixpoint Weaken_Subtype_update_list gamma S T (sub_S_T : subtype gamma S T) : 
    Weaken_Subtype_update_list_P nat _ _ subtype Empty Update _ _ _ sub_S_T :=
    match sub_S_T return Weaken_Subtype_update_list_P nat _ _ subtype Empty Update _ _ _ sub_S_T with
      | Base_sub gamma S' T' sub_S_T' => FJ_Weaken_Subtype_update_list _ _ _ _ _ _ 
        _ _ _ _ CT _ subtype build_te Base_sub Empty Update _ _ _ sub_S_T' Weaken_Subtype_update_list
      | GJ_sub gamma S' T' sub_S_T' => GJ_Weaken_Subtype_update_list _ _ Gty N _ _ Empty TLookup
        subtype GJ_sub nat Update TLookup_Update TLookup_Empty _ _ _ sub_S_T'
    end.

  Definition Weaken_WF_Object_Ext := Generic.Weaken_WF_Object_Ext _ _ Empty _ Update unit.

  Section Ty_recursion.

    Variables
      (P : Ty -> Type)
      (Q : ty_ext -> Type).

    Hypotheses
      (H1 : forall X, P (Gty (TyVar _ X)))
      (H2 : forall te cl, Q te -> P ((Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (ty_def _ _ te cl)))
      (H3 : forall te, Q (nil, te))
      (H4 : forall ty tys te, Q (tys, te) -> P ty -> Q (ty :: tys, te)).

    Fixpoint ty_rect (ty : Ty) : P ty :=
      match ty with
        | Gty (TyVar X) => H1 X
        | Base_Ty (ty_def (tys, te) c) => H2 (tys, te) c (
          (fix tys_rect tys : Q (tys, te) :=
            match tys return Q (tys, te) with
              | nil => H3 te
              | ty :: tys' => H4 ty tys' te (tys_rect tys') (ty_rect ty)
            end) tys)
      end.

  End Ty_recursion.
  
  Section wf_class_ext_recursion.
    
    Definition map_List_P1 := fun (A : Type) (P Q : A -> Prop) (Map_P : forall a, P a -> Q a) => 
      fix map (As : list A) (PAs : List_P1 P As) : List_P1 Q As :=
      match PAs in (List_P1 _ As'') return List_P1 Q As'' with
        Nil => Nil Q
        | Cons_a a As' Pa PAs' => Cons_a Q a As' (Map_P a Pa) (map As' PAs')
      end.

    Variables (P : forall gamma ty, WF_Type gamma ty -> Prop)
      (Q' : forall gamma cld ty,
        @GJ_wf_class_ext nat Ty  N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) Context subtype
        Ty_trans WF_Type unit unit gamma cld ty -> Prop)
      (Q'_P1 : forall gamma tys, List_P1 (WF_Type gamma) tys -> Prop)
      (Q'_len : forall (typs : TyP_List) (tys : list Ty), length typs = length tys -> Prop)
      (Q'_P2 : forall tys tys' delta, List_P2 tys tys' (subtype delta) -> Prop).
    
    Hypothesis (H1 : forall gamma ce tys typs te P1 len P2, 
      Q'_P1 gamma tys P1 -> 
      Q' _ _ _ (@Generic.wf_class_ext nat Ty N _ Context subtype
        Ty_trans WF_Type unit unit ce gamma typs tys te
        P1 len P2))
    (H2 : forall gamma, Q'_P1 gamma _ (Nil (WF_Type gamma)))
    (H3 : forall gamma ty tys P_ty P_tys, P _ _ P_ty -> Q'_P1 _ tys P_tys -> 
      Q'_P1 gamma _ (Cons_a _ ty tys P_ty P_tys)).
    
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

    Variable (H4 : forall gamma ty (wf_ty : (Generic.GJ_WF_Type nat Ty Gty N Context TLookup gamma ty)), P gamma ty (GJ_WF_Type _ _ wf_ty)).

    Fixpoint WF_Type_rect' H1 H2 gamma ty wf_ty : P gamma ty wf_ty := 
      match wf_ty return P _ _ wf_ty with 
        | Base_WF_Type gamma' ty' wf_ty' => 
          FJ_WF_Type_rect' nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
          wf_class_ext wf_object_ext WF_Type Base_WF_Type P Q' H1 H2
          (wf_class_ext_rect (WF_Type_rect' H1 H2)) gamma' ty' wf_ty' 
        | GJ_WF_Type gamma ty wf_ty => H4 _ _ wf_ty
      end.

  End wf_class_ext_recursion.   

  Fixpoint Weaken_WF_Type_update_list gamma ty (WF_ty : WF_Type gamma ty) :
    FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty :=
    match WF_ty in WF_Type gamma ty return FJ_Weaken_WF_Type_update_list_P _ _ _ WF_Type Empty Update gamma ty WF_ty with 
      | Base_WF_Type gamma' ty' wf_ty' => 
        FJ_Weaken_WF_Type_update_list nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type Base_WF_Type Empty Update Weaken_WF_Object_Ext
        (Weaken_WF_Type_update_list_ext nat Ty N _ _ Empty subtype Ty_trans WF_Type
          _ _ _ _ Weaken_Subtype_update_list Weaken_WF_Type_update_list) gamma' ty' wf_ty'
      | GJ_WF_Type gamma' ty' wf_ty' => 
        GJ_Weaken_WF_Type_update_list _ _ _ _ _ _ _ _ GJ_WF_Type nat Update
        TLookup_Update TLookup_Update' TLookup_Empty _ _ wf_ty'
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
  Definition WF_fields_map := FJ_WF_fields_map Ty Context.

  Definition Weaken_WF_fields_map gamma ty ty' (bound : Bound gamma ty ty') :=
    match bound in Bound gamma ty ty' return (forall (gamma' : Context) (vars : list (Var nat * Ty)),
      gamma = Generic.update_list Ty Context nat Update Empty vars ->
      Bound (Generic.update_list Ty Context nat Update gamma' vars) ty ty')
      with 
      | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_Weaken_WF_fields_map nat Ty Gty _ N_Wrap
        _ Empty TLookup _ Update TLookup_Update TLookup_Update' TLookup_Empty Bound GJ_Bound
        gamma' ty'' ty''' GJ_bound'
      | FJ_Bound gamma' ty'' ty''' FJ_bound' => FJ_Weaken_WF_fields_map Ty _ N_Wrap _ Empty _ 
        Update Bound FJ_Bound gamma' ty'' ty''' FJ_bound'
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
    Generic.Weaken_WF_mtype_ext nat Ty N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ Empty subtype Ty_trans
    WF_Type _ Update Weaken_Subtype_update_list Weaken_WF_Type_update_list unit unit
    (FJ_WF_mtype_ext Context) (FJ_Weaken_WF_mtype_ext _ _ _ Empty Update).
  
  Lemma Ty_eq_dec : forall (S T : Ty), {S = T} + {S <> T}.
    intro; apply (ty_rect (fun S => forall T, {S = T} + {S <> T})
      (fun Ss => forall Ts, {Ss = Ts} + {Ss <> Ts})); intros;
    try (destruct T; try (right; congruence); unfold Generic.FJ_Ty_Wrap; unfold id).
    destruct g; destruct (eq_nat_dec X n); subst; first [left; congruence | right; congruence].
    destruct f; destruct c; destruct cl; destruct (H g); subst; 
      try first [left; reflexivity | right; congruence];
        destruct (eq_nat_dec n n0); subst; first [left; reflexivity | right; congruence].
    right; congruence.
    destruct Ts; destruct l; destruct u; destruct te; first [left; reflexivity | right; congruence].
    destruct Ts; destruct l; destruct u; destruct te; try (right; congruence).
    destruct (H (l, tt)) as [tys_eq | tys_neq]; destruct (H0 t) as [ty_eq | ty_neq];
      try injection tys_eq; intros; subst; first [left; reflexivity | right; congruence].
  Qed.

  Variable (subtype_dec : forall gamma S T, subtype gamma S T \/ ~ subtype gamma S T).

  Fixpoint Weakening gamma e ty (WF_e : E_WF gamma e ty) : Weakening_def _ _ _ WF_e :=
    match WF_e return Weakening_def _ _ _ WF_e with
      | FJ_E_WF gamma e ty FJ_case => FJ_Weakening _ _ _ _ _ _ _ _ _ Base_E _ _
        subtype WF_Type fields mtype
        E_WF lookup Bound Bound WF_mtype_Us_map WF_mtype_U_map
        WF_mtype_ext Empty FJ_E_WF Update eq_nat_dec lookup_update_eq
        lookup_update_neq lookup_update_neq' lookup_Empty lookup_id Weaken_WF_fields_map'
        Weaken_WF_fields_map' Weaken_WF_mtype_Us_map Weaken_WF_mtype_U_map
        Weaken_Subtype_update_list Weaken_WF_mtype_ext Weaken_WF_Type_update_list _ _ _ 
        FJ_case Weakening
    end.

  Lemma E_trans_Wrap : forall e vars es', 
    trans (Base_E e) vars es' = cFJ.FJ_E_trans _ _ _ _ _ _ _ Base_E trans eq_nat_dec e vars es'.
    simpl; reflexivity.
  Qed.
  
  Definition WF_mtype_ty_0_map_Weaken_update_list delta T T' (Bnd : Bound delta T T') :=
    match Bnd in (Bound delta T T') return (forall delta' vars, delta = update_list delta' vars -> 
      Bound delta' T T') with
      | GJ_Bound delta T T' GJ_Bound' => Generic.GJ_Bound_Weaken_update_list _ _ Gty _ N_Wrap _ TLookup _ Update
        TLookup_Update Bound GJ_Bound delta T T' GJ_Bound'
      | FJ_Bound delta T T' FJ_Bound' => Generic.N_Bound_Weaken_update_list _ _ N_Wrap _ _ Update Bound FJ_Bound
        delta T T' FJ_Bound'
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
      | Base_sub gamma' S' T' sub_S_T' => 
        FJ_Bound_total _ _ _ _ _ _ _ subtype _ _ _ _ Bound FJ_Bound _ _ CT 
        build_te Base_sub WF_mtype_ty_0_map_total gamma' S' T' sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Bound_total _ _ _ _ _ _ TLookup subtype GJ_sub Bound GJ_Bound gamma' S' T' sub_S_T'
    end.
  
  Fixpoint Subtype_Update_list_id gamma S T (sub_S_T : subtype gamma S T) := 
    match sub_S_T with
      | Base_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Update_list_id _ _ _ _ _ _ _ _ _ _ CT _ subtype build_te
        Base_sub Update gamma' S' T' sub_S_T' Subtype_Update_list_id
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Subtype_Update_list_id _ _ Gty N _ _ TLookup _ GJ_sub _ Update
        TLookup_Update gamma' S' T' sub_S_T'
    end.
  
  Definition WF_Object_ext_Update_Vars_id := 
    GJ_WF_Object_ext_Update_Vars_id _ _ _ Update unit.
  
  Fixpoint WF_Type_update_list_id gamma ty (WF_ty : WF_Type gamma ty) :
    cFJ.WF_Type_update_list_id_P _ _ _ WF_Type Update gamma ty WF_ty :=
    match WF_ty in WF_Type gamma ty return cFJ.WF_Type_update_list_id_P _ _ _ WF_Type Update gamma ty WF_ty with 
      | Base_WF_Type gamma' ty' wf_ty' => 
        FJ_WF_Type_update_list_id nat nat nat nat ty_ext Ty _ E md_ext cld_ext CT Context 
        wf_class_ext wf_object_ext WF_Type Base_WF_Type Update WF_Object_ext_Update_Vars_id
        (WF_Type_update_list_id_ext nat Ty N _ _ subtype Ty_trans WF_Type
          nat Update _ _  Subtype_Update_list_id WF_Type_update_list_id) gamma' ty' wf_ty'
      | GJ_WF_Type gamma' ty' wf_ty' => 
        GJ_WF_Type_update_list_id _ _ Gty N _ TLookup WF_Type GJ_WF_Type _ Update 
        TLookup_Update _ _ wf_ty'
    end.
  
  Definition WF_fields_map_tot := FJ_WF_fields_map_tot _ _ _ Base_Ty Context.
   
  Definition fields_build_tys_tot := GJ_fields_build_tys_tot nat Ty N Ty_trans 
    FJ_build_te (FJ_fields_build_tys Ty) (cFJ.FJ_fields_build_tys_tot Ty).
    
  Fixpoint fields_id gamma ty fds (ty_fields : fields gamma ty fds) := 
    match ty_fields with 
      | FJ_fields gamma' ty' fds' FJ_ty'_fields =>
        FJ_fields_id _ _ _ _ _ _ _ _ _ _ CT Context fields fields_build_te 
        fields_build_tys FJ_fields Base_inject fields_invert  
        fields_build_te_id fields_build_tys_id  gamma' ty' fds' FJ_ty'_fields fields_id
    end.
  
  Definition WF_mtype_ext_update_list_id := FJ_WF_mtype_ext_update_list_id _ _ _ Update.
  
  Definition WF_mtype_ty_0_map_tot := FJ_WF_mtype_ty_0_map_tot Ty Context.
  
  Definition WF_mtype_ty_0_map_cl_id := 
    FJ_WF_mtype_ty_0_map_cl_id _ _ _ Base_Ty Context Base_inject.
  
  Definition WF_mtype_ty_0_map_cl_id' := 
    FJ_WF_mtype_ty_0_map_cl_id' _ _ _ Base_Ty Context. 
  
  Definition m_eq_dec := eq_nat_dec.
    
  Definition WF_mtype_Us_map_len := FJ_WF_mtype_Us_map_len Ty Context.
  
  Definition mtype_build_tys_len := FJ_mtype_build_tys_len nat Ty.
  
  Definition methods_build_te_id := FJ_methods_build_te_id.
  
  Definition WF_Type_par_Lem_P := WF_Type_par_Lem_P _ _ _ _ ty_ext Ty Base_Ty _ _ _ CT Context 
    wf_object_ext WF_Type mtype_build_te L_build_context.
  
  Fixpoint WF_Type_par_Lem gamma ty (WF_ty : WF_Type gamma ty) :=
    match WF_ty return WF_Type_par_Lem_P _ _ WF_ty with 
      | Base_WF_Type gamma ty WF_base => 
        FJ_WF_Type_par_Lem _ _ _ _ _ _ _ _ _ _ CT Context wf_class_ext
        wf_object_ext WF_Type Base_WF_Type mtype_build_te
        L_build_context Base_inject 
        (fun g g0 te0 te' te'' ce _ _ _ _ _ mty wf_obj _ _ => 
          WF_Obj_ext_Lem _ _ _ _ Ty_trans _ _ FJ_mtype_build_te g g0 te0 te' te'' ce wf_obj mty)  gamma ty WF_base
      | GJ_WF_Type gamma ty WF_ty => (fun g te0 te' te'' ce _ _ _ _ _ _ mty wf_obj _ => 
        WF_Obj_ext_Lem _ _ _ _ Ty_trans _ _ FJ_mtype_build_te gamma g te0 te' te'' ce wf_obj mty)
    end.
  
  Definition WF_Type_par_Lem_P' := 
    cFJ.WF_Type_par_Lem_P' _ _ _ _ ty_ext Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E _ _ CT Context wf_class_ext
    WF_Type mtype_build_te L_build_context.
  
  Fixpoint Weakening_2_1_1 delta S T (sub_S_T : subtype delta S T) : 
    (Weakening_2_1_1_P _ _ subtype app_context _ _ _ sub_S_T) :=
    match sub_S_T return (Weakening_2_1_1_P _ _ subtype app_context _ _ _ sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => 
        Weakening_2_1_1_FJ Ty ty_ext nat N Base_Ty id _ subtype _ _ _ app_context
        E _ _ CT build_te Base_sub Weakening_2_1_1 delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => Weakening_2_1_1_GJ _ _ Gty _ _ _ TLookup
        subtype GJ_sub app_context TLookup_app delta S' T' sub_S_T'
    end.
  
  Definition Weakening_2_1_2 :=
    WF_Type_rect' (Weakening_2_1_2_P _ _ WF_Type app_context) 
    (Weakening_2_1_2_Q _ _ _ _ _ subtype Ty_trans WF_Type
      app_context _ _)
    (Weakening_2_1_2_P1 _ _ WF_Type app_context)
    (Weakening_2_1_2_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type app_context _ _ Weakening_2_1_1)
    (Weakening_2_1_2_ext_H2 _ _ WF_Type app_context)
    (Weakening_2_1_2_ext_H3 _ _ WF_Type app_context)
    (GJ_Weakening_2_1_2 _ _ Gty _ _ TLookup WF_Type GJ_WF_Type app_context TLookup_app)
    (FJ_Weakening_2_1_2_H1 _ _ _ _ _ _ _ WF_Type nat nat nat app_context E _ _ CT
      wf_class_ext wf_object_ext (Weakening_2_1_2_obj_ext _ _ app_context _) Base_WF_Type)
    (FJ_Weakening_2_1_2_H2 _ _ _ _ _ _ _ WF_Type _ _ _ app_context E _ _ CT wf_class_ext
      wf_object_ext Base_WF_Type).
  
  Definition WF_Bound_app_Weaken := GJ_WF_Bound_app_Weaken _ _ Gty _
    _ TLookup app_context TLookup_app.

  Definition WF_mtype_Us_map_app_Weaken := 
    GJ_WF_mtype_Us_map_app_Weaken _ _ N Context Ty_trans _ app_context _ _
    (FJ_WF_mtype_Us_map_app_Weaken _ _ app_context).
  
  Definition WF_mtype_U_map_app_Weaken := 
    GJ_WF_mtype_U_map_app_Weaken _ _ N Context Ty_trans _ app_context _ _
    (FJ_WF_mtype_U_map_app_Weaken _ _ app_context).
  
  Definition WF_mtype_ext_app_Weaken := 
    GJ_WF_mtype_ext_app_Weaken _ _ _ Base_Ty _ 
    subtype Ty_trans WF_Type _ app_context
    Weakening_2_1_1 Weakening_2_1_2 _ _ (FJ_WF_mtype_ext_app_Weaken _ app_context).

  Definition WF_Bound_app_Weaken' (gamma : Context) (ty ty' : Ty) (Bnd : Bound gamma ty ty') :=
    match Bnd in (Bound gamma ty ty') return (forall gamma', Bound (app_context gamma gamma') ty ty') with
      | GJ_Bound gamma' ty'' ty''' GJ_bound' => GJ_WF_Bound_app_Weaken' _ _ Gty _ N_Wrap _ TLookup
        app_context TLookup_app Bound GJ_Bound gamma' ty'' ty''' GJ_bound'
      | FJ_Bound gamma' ty'' ty''' FJ_bound' => N_WF_Bound_app_Weaken' _ _ N_Wrap _ app_context
        Bound FJ_Bound gamma' ty'' ty''' FJ_bound'
    end.
  
  Fixpoint Weakening_2_1_3_1 delta e T (WF_e : E_WF delta e T) :
    Generic.Weakening_2_1_3_1_P Ty Context app_context E E_WF delta e T WF_e :=
    match WF_e in E_WF delta e T return Generic.Weakening_2_1_3_1_P _ _ app_context _ E_WF delta e T WF_e with 
      | FJ_E_WF gamma e ty FJ_case => Generic.Weakening_2_1_3_1 _ _ _ N Base_Ty _ _ Empty subtype
        WF_Type _ fields _ _ _ mtype app_context _ Weakening_2_1_1
        Weakening_2_1_2 _ Base_E E_WF lookup Bound WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Bound Lookup_app FJ_E_WF 
        (fun g g' ty ty' bnd => WF_Bound_app_Weaken' g ty ty' bnd g')
        (fun g g' ty ty' bnd => WF_Bound_app_Weaken' g ty ty' bnd g') WF_mtype_Us_map_app_Weaken
        WF_mtype_U_map_app_Weaken WF_mtype_ext_app_Weaken Weakening_2_1_3_1 gamma e ty FJ_case
    end.
  
  Inductive Free_Vars : Ty -> list nat -> Prop :=
  | GJ_Free_Vars' : forall ty txs, GJ_Free_Vars _ _ Gty ty txs -> Free_Vars ty txs
  | FJ_Free_Vars' : forall ty txs, FJ_Free_Vars _ _ _ nat N Base_Ty id 
    (GJ_TE_Free_Vars _ _ _ Free_Vars) ty txs -> Free_Vars ty txs.
  
  Definition TE_Free_Vars := (GJ_TE_Free_Vars _ _ unit Free_Vars).
  
  Lemma GJ_Free_Vars_invert : forall ty txs, Free_Vars (Gty ty) txs -> GJ_Free_Vars _ _ Gty (Gty ty) txs.
    intros; inversion H; subst; first [apply H0 | inversion H0].
  Qed.
  
  Lemma FJ_Free_Vars_invert : forall ty txs, Free_Vars (Base_Ty ty) txs -> 
    FJ_Free_Vars _ _ _ nat N Base_Ty id (GJ_TE_Free_Vars _ _ _ Free_Vars) (Base_Ty ty) txs.
    intros; inversion H; subst; first [apply H0 | inversion H0].
  Qed.
  
  Lemma GJ_Ty_Wrap_inject : forall ty ty', Gty ty = Gty ty' -> ty = ty'.
    intros; congruence.
  Qed.
  
  Lemma FJ_Ty_Wrap_inject : forall ty ty', Base_Ty ty = Base_Ty ty' -> ty = ty'.
    intros; congruence.
  Qed.
  
  Lemma GTy_ext_Wrap_inject : forall (te te' : ty_ext) , id te = id te' -> te = te'.
    unfold id; auto.
  Qed.
  
  Definition TE_trans := (GJ_TE_Trans _ _ Ty_trans unit).
  
  Lemma GJ_TE_Trans_invert : forall (te : GTy_ext Ty) (Ys : list nat)
    (Us : list Ty), TE_trans (id te) Ys Us = id (GJ_TE_Trans nat Ty Ty_trans _ te Ys Us).
    reflexivity.
  Qed.

  Lemma FJ_Ty_trans_invert : forall (ty : cFJ.FJ_Ty nat ty_ext) txs tys,
    Ty_trans ( (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) ty) txs tys = 
    Generic.FJ_Ty_Trans _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id TE_trans ty txs tys.
    reflexivity.
  Qed.

  Lemma GJ_Ty_trans_invert : 
    forall ty Xs Us, Ty_trans (Gty ty) Xs Us = GTy_trans nat eq_nat_dec Ty Gty ty Xs Us.
    reflexivity.
  Qed.

  Definition Ty_trans_nil :=
    ty_rect (Ty_trans_nil_P _ _ Ty_trans)
    (TE_trans_nil_P _ _ _ TE_trans)
    (GJ_Ty_trans_nil _ eq_nat_dec _ Gty _ GJ_Ty_trans_invert)
    (FJ_Ty_trans_nil _ _ _ _ N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id Ty_trans TE_trans 
      FJ_Ty_trans_invert)
    (TE_trans_nil_H1 _ _ _ _ _ id _ GJ_TE_Trans_invert)
    (TE_trans_nil_H2 _ _ _ _ _ id _ (fun _ _ => id) GJ_TE_Trans_invert).

  Definition Ty_trans_nil' :=
    ty_rect (Ty_trans_nil'_P _ _ Ty_trans)
    (TE_trans_nil'_P _ _ _ TE_trans)
    (GJ_Ty_trans_nil' _ eq_nat_dec _ Gty _ GJ_Ty_trans_invert)
    (FJ_Ty_trans_nil' _ _ _ _ N _ _ Ty_trans TE_trans 
      FJ_Ty_trans_invert)
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
  
  Definition Free_Vars_Subst :=
    ty_rect Free_Vars_Subst_P Free_Vars_Subst_Q 
    (Free_Vars_Subst_H1 _ eq_nat_dec _ Gty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject)
    (Free_Vars_Subst_H2 _ _ _ _ _ _ _ FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert TE_trans)
    (Free_Vars_Subst_H3 _ _ _ Ty_trans _ TE_Free_Vars id)
    (Free_Vars_Subst_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert 
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).
  
  Definition map_Ty_trans_P := map_Ty_trans_P _ _ N Ty_trans Free_Vars.
  
  Definition map_Ty_trans_Q := map_Ty_trans_Q _ _ _ N Ty_trans TE_Free_Vars TE_trans.
  
  Definition NIn_Ty_trans : forall X Xs Us, ~In X Xs -> Ty_trans (Gty (TyVar _ X)) Xs Us = Gty (TyVar _ X) :=
    GNIn_Ty_trans _ eq_nat_dec Ty Gty _ _ Empty build_fresh TUpdate.
    
  Definition Ty_trans_FJ ty Xs Us : Ty_trans (Base_Ty ty) Xs Us =
    FJ_Ty_Trans _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id TE_trans ty Xs Us :=
    refl_equal _.

  Definition map_Ty_trans :=
    ty_rect map_Ty_trans_P map_Ty_trans_Q
    (map_Ty_trans_H1 _ eq_nat_dec _ Gty _ Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject NIn_Ty_trans)
    (map_Ty_trans_H2 _ _ _ _ _ _ _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars 
      FJ_Free_Vars_invert TE_trans Ty_trans_FJ)
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
    (map_Ty_trans'_H2 _ _ _ _ _ _ _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars 
      FJ_Free_Vars_invert TE_trans Ty_trans_FJ)
    (map_Ty_trans'_H3 _ _ _ _ Ty_trans _ TE_Free_Vars id)
    (map_Ty_trans'_H4 _ _ _ _ Ty_trans _ Free_Vars TE_Free_Vars (fun x => x) GJ_TE_Free_Vars_invert 
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).
  
  Definition wf_free_vars_P := wf_free_vars_P _ _ _ _ Empty WF_Type TUpdate Free_Vars.

  Definition wf_free_vars_Q := wf_free_vars_Q _ _ _ N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ Empty subtype
    Ty_trans WF_Type TUpdate unit unit TE_Free_Vars id.
  
  Definition wf_free_vars_Q_P1 := wf_free_vars_Q_P1 _ _ _ _ Empty WF_Type TUpdate Free_Vars.
  
  Variables (TLookup_TUpdate_eq : forall (gamma : Context) (X : _) (ty : _), TLookup (TUpdate gamma X ty) X ty)
    (TLookup_TUpdate_neq' : forall (gamma : Context) (Y X : _) (ty ty' : _),
      TLookup (TUpdate gamma Y ty') X ty -> X <> Y -> TLookup gamma X ty)
    (TLookup_id : forall (gamma : Context) (X : _) (ty ty' : _),
      TLookup gamma X ty -> TLookup gamma X ty' -> ty = ty').
  
  Definition wf_free_vars_ext := wf_free_vars_ext _ _ _ N Base_Ty _ Empty subtype
    Ty_trans WF_Type TUpdate cld_ext _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert.
  
  Definition wf_free_vars :=
    WF_Type_rect' wf_free_vars_P wf_free_vars_Q wf_free_vars_Q_P1
    (wf_free_vars_ext_H1 _ _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate
      _ _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_invert)
    (wf_free_vars_ext_H2 _ _ _ _ Empty WF_Type TUpdate Free_Vars)
    (wf_free_vars_ext_H3 _ _ _ _ Empty WF_Type TUpdate Free_Vars)
    (GJ_wf_free_vars _ eq_nat_dec _ Gty _ _ Empty TLookup WF_Type
      GJ_WF_Type TUpdate TLookup_Empty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject
      TLookup_TUpdate_eq TLookup_TUpdate_neq' TLookup_id)
    (FJ_wf_free_vars_H1 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ FJ_Ty_Wrap_inject md_ext 
      cld_ext CT wf_class_ext wf_object_ext Base_WF_Type Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert (GJ_TE_Free_Vars_obj _ _ _ _ Free_Vars))
    (FJ_wf_free_vars_H2 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ FJ_Ty_Wrap_inject
      _ _ CT wf_class_ext wf_object_ext Base_WF_Type Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert).
  
  Definition exists_Free_Vars :=
    ty_rect (exists_Free_Vars_P nat Ty Free_Vars) (exists_Free_Vars_Q nat _ TE_Free_Vars)
    (exists_Free_Vars_H1 _ _ Gty _ GJ_Free_Vars')
    (exists_Free_Vars_H2 _ _ _ _ _ _ _ _ _ FJ_Free_Vars')
    (exists_Free_Vars_H3 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id))
    (exists_Free_Vars_H4 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id) (fun _ _ => id)).
  
  Lemma L_build_context'_Empty_1 : forall (ce : FJ_cld_ext)  (gamma : Context)
    (XNs : Generic.TyP_List nat N) (T : Ty),
    L_build_context' ce gamma ->
    WF_Type (update_Tlist gamma XNs) T ->
    WF_Type (update_Tlist Empty XNs) T.
    intros; inversion H; subst; assumption.
  Qed.
    
  Definition Type_Subst_Sub_2_5_P := 
    Type_Subst_Sub_2_5_P nat Ty N Base_Ty Context TLookup
    subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.
  
  Lemma Ty_trans_eq_NTy_trans (N0 : N) (Xs : list _) (Us : list Ty) :
    N_Wrap (N_trans N0 Xs Us) = Ty_trans (N_Wrap N0) Xs Us.
    intros; destruct N0; reflexivity.
  Qed.
  
  Lemma N_Wrap_inject : forall n n' : N, Base_Ty n = Base_Ty n' -> n = n'.
    intros; injection H; auto.
  Qed.
  
  Lemma FJ_WF_Type_Wrap_invert : forall delta S, WF_Type delta ( (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) S) ->
    cFJ.FJ_WF_Type _ _ _ _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ _ CT Context 
    (wf_class_ext' WF_Type) wf_object_ext delta ( (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) S).
    intros; inversion H; subst; try eapply H0.
    inversion H0.
  Qed.

  Fixpoint Type_Subst_Sub_2_5 delta S T (sub_S_T : subtype delta S T) : 
    Type_Subst_Sub_2_5_P delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return (Type_Subst_Sub_2_5_P delta S T sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => Type_Subst_Sub_2_5_FJ _ _ _ _ N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id
        _ Empty TLookup subtype Ty_trans
        WF_Type _ fields _ _ TUpdate app_context Update _ FJ_Ty_Wrap_inject _ _ CT
        build_te Base_sub wf_class_ext wf_object_ext E_WF Free_Vars TE_trans FJ_Ty_trans_invert 
        exists_Free_Vars N_trans subst_context
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
        FJ_WF_Type_Wrap_invert WF_CT (@GJ_Type_Subst_Sub_2_5_TE _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
          _ Empty subtype Ty_trans WF_Type TUpdate _ _ Free_Vars exists_Free_Vars
          N_trans wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 
          _)
        (@GJ_Type_Subst_Sub_2_5_TE' _ _ _ _ _ subtype Ty_trans _ _ _ _ _ _ _)
        Type_Subst_Sub_2_5 delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => Type_Subst_Sub_2_5_GJ _ eq_nat_dec _ Gty _ _ _ TLookup subtype
        GJ_sub Ty_trans WF_Type TUpdate app_context TLookup_app Weakening_2_1_1
        Free_Vars GJ_Free_Vars' GJ_Ty_trans_invert Ty_trans_nil NIn_Ty_trans exists_Free_Vars N_Wrap_inject N_trans
        subst_context TLookup_subst map_Ty_trans TLookup_dec TLookup_unique TLookup_app'
        TLookup_app'' TLookup_update_eq TLookup_update_neq' Free_Vars_Subst Ty_trans_eq_NTy_trans delta S' T' sub_S_T'
    end.
  
  Definition Type_Subst_WF_2_6_P := Type_Subst_WF_2_6_P _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
    _ TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.
  
  Definition cld_typs (ce' : cld_ext) :=
    match ce' with (typs, _) => typs end.
  
  Definition Type_Subst_WF_2_6_Q := Type_Subst_WF_2_6_Q _ _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
    _ TLookup subtype WF_Type TUpdate app_context _ wf_class_ext Free_Vars TE_trans N_trans subst_context cld_typs.
  
  Definition Type_Subst_WF_2_6_P1 := Type_Subst_WF_2_6_P1 _ _ _  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ 
    TLookup subtype Ty_trans WF_Type TUpdate app_context Free_Vars N_trans subst_context.
      
  Definition Ty_trans_trans_subst :=
    ty_rect (Ty_trans_trans_subst_P _ _ Ty_trans Free_Vars)
  (Ty_trans_trans_subst_Q _ _ _ Ty_trans TE_Free_Vars TE_trans)
  (fun n => (GJ_Ty_trans_trans_subst _ eq_nat_dec _ Gty _ Ty_trans build_fresh
    Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert (TyVar _ n)))
  (FJ_Ty_trans_trans_subst _ _ _ _ _ _ _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert
    TE_trans FJ_Ty_trans_invert)
  (Ty_trans_trans_subst_H3 _ _ _ Ty_trans _ Free_Vars id GTy_ext_Wrap_inject)
  (Ty_trans_trans_subst_H4 _ _ _ _ Ty_trans build_fresh _ 
    Free_Vars TE_Free_Vars id (fun _ _ => id) TE_trans
    GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Definition L_WF_bound : forall cld : cFJ.L _ _ _ _ ty_ext Ty E md_ext cld_ext,
    L_WF cld ->
    exists Ys : list (list _),
      List_P2'
      (fun typ : GTy _ * _ =>
        Free_Vars ( (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (snd typ))) 
      (cld_typs (cld_ce _ _ _ _ _ _ _ _ _ cld)) Ys /\
      (forall Y : _,
        In Y (fold_right (@app _) nil Ys) ->
        In Y (Extract_TyVar _ _ (cld_typs (cld_ce _ _ _ _ _ _ _ _ _ cld)))).
    intros; inversion H; subst; simpl.
    eapply (GJ_L_WF_bound _ _ _ _ _ _ Empty WF_Type TUpdate _ Free_Vars exists_Free_Vars
      wf_free_vars L_build_context' L_build_context'_Empty_1 _ _ _ _ H0 H8).
  Qed.

  Definition Type_Subst_WF_2_6 :=
    WF_Type_rect' Type_Subst_WF_2_6_P Type_Subst_WF_2_6_Q Type_Subst_WF_2_6_P1
    (Type_Subst_WF_2_6_ext_H1 _ _ N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
      _ TLookup subtype Ty_trans WF_Type TUpdate app_context unit unit
      Free_Vars N_trans subst_context Type_Subst_Sub_2_5 Ty_trans_trans_subst)
    (Type_Subst_WF_2_6_ext_H2 _ _ _ _ _ TLookup subtype Ty_trans WF_Type TUpdate app_context
      Free_Vars N_trans subst_context)
    (Type_Subst_WF_2_6_ext_H3 _ _ _ _ _ TLookup subtype Ty_trans WF_Type TUpdate app_context
      Free_Vars N_trans  subst_context)
    (GJ_Type_Subst_WF_2_6 _ eq_nat_dec _ Gty _ _ _ TLookup subtype
      Ty_trans WF_Type GJ_WF_Type TUpdate app_context TLookup_app Weakening_2_1_2
      Free_Vars GJ_Ty_trans_invert Ty_trans_nil Ty_trans_nil' N_trans subst_context
      TLookup_subst TLookup_dec TLookup_app' TLookup_app''
       TLookup_update_neq')
    (FJ_Type_Subst_WF_2_6_H1 _ _ _ _ _ _ _ _ TLookup subtype Ty_trans
      WF_Type _ _ _ TUpdate app_context _ _ _ CT wf_class_ext wf_object_ext
      Base_WF_Type Free_Vars TE_trans FJ_Ty_trans_invert N_trans subst_context 
      (GJ_Type_Subst_WF_2_6_obj_ext _ _ _ Ty_trans app_context _ subst_context))
    (FJ_Type_Subst_WF_2_6_H2 _ _ _ _ _ _ _ _ Empty TLookup subtype Ty_trans
      WF_Type _ fields _ _ TUpdate app_context Update _ _ _ CT wf_class_ext 
      wf_object_ext Base_WF_Type E_WF Free_Vars TE_trans FJ_Ty_trans_invert N_trans subst_context 
      _ _ _ _ _ override WF_CT cld_typs L_WF_bound).
    
  Variable (subst_context_Empty : forall Xs Us, subst_context Empty Xs Us = Empty)
    (app_context_Empty : forall gamma, app_context gamma Empty = gamma).
  
  Fixpoint Ty_rename ty n : Ty :=
    match ty with 
      | Base_Ty ty' => FJ_Ty_rename _ _ _ _ N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id (GJ_TE_rename nat _ unit Ty_rename) ty' n
      | Gty ty' => GJ_Ty_rename _ _ Gty plus ty' n
    end.
  
  Definition TE_rename := GJ_TE_rename nat _ unit Ty_rename.
  
  Definition NTy_rename n n' : N :=
    match n with 
      ty_def te c => ty_def _ _ (TE_rename te n') c
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
  
  Definition GJ_Ty_rename_invert ty Y : Ty_rename (Gty ty) Y = GJ_Ty_rename _ _ Gty plus ty Y :=
    refl_equal _.
  
  Definition Ty_rename_Ty_trans :=
    ty_rect (Ty_rename_Ty_trans_P _ _ Ty_trans plus Ty_rename)
    (Ty_rename_Ty_trans_Q _ _ _ TE_trans plus Ty_rename TE_rename)
    (GJ_Ty_rename_Ty_trans _ eq_nat_dec _ Gty Ty_trans GJ_Ty_trans_invert Ty_trans_nil' 
      plus Ty_rename rename_X_eq GJ_Ty_rename_invert)
    (FJ_Ty_rename_Ty_trans _ _ _ _ _ _ _ Ty_trans TE_trans FJ_Ty_trans_invert plus Ty_rename
    TE_rename (fun _ _ => refl_equal _))
    (Ty_rename_Ty_trans_H3 _ _ Ty_trans _ plus Ty_rename)
    (Ty_rename_Ty_trans_H4 _ _ _ Ty_trans _ id TE_trans GTy_ext_Wrap_inject 
      GJ_TE_Trans_invert plus Ty_rename TE_rename (fun _ _ => refl_equal _)).     
  
  Definition FV_subst_tot := ty_rect (FV_subst_tot_P _ _ Ty_trans Free_Vars)
    (FV_subst_tot_Q _ _ _ Free_Vars TE_Free_Vars TE_trans)
    (GJ_FV_subst_tot _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_FV_subst_tot _ _ _ _ _ _ _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars'
      FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (FV_subst_tot_H3 _ _ Ty_trans _ Free_Vars)
    (FV_subst_tot_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id (fun _ _ => id) 
      (fun _ _  => id) TE_trans GJ_TE_Trans_invert). 
  
  Definition Ty_rename_eq_Ty_trans := ty_rect 
    (Ty_rename_eq_Ty_trans_P _ _ Gty Ty_trans Free_Vars plus Ty_rename)
    (Ty_rename_eq_Ty_trans_Q _ _ _ Gty TE_Free_Vars TE_trans plus TE_rename)
    (GJ_Ty_rename_eq_Ty_trans _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert plus Ty_rename GJ_Ty_rename_invert)
    (FJ_Ty_rename_eq_Ty_trans _ _ _ Gty _ _ _ _ Ty_trans FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars
      FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert plus Ty_rename
      TE_rename (fun _ _ => refl_equal _))
    (Ty_rename_eq_Ty_trans_H3 _ _ Gty Ty_trans _ Free_Vars plus Ty_rename)
    (Ty_rename_eq_Ty_trans_H4 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id (fun _ _ => id)
      TE_trans (fun _ _ => id) (fun _ _ _ => refl_equal _) plus Ty_rename TE_rename (fun _ _ => refl_equal _)).
  
  Lemma Ty_rename_eq_NTy_rename : forall (n : N) (X : _), Ty_rename (N_Wrap n) X = N_Wrap (NTy_rename n X).
    destruct n; simpl; reflexivity.
  Qed.

  Fixpoint Ty_rename_subtype delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in (subtype delta S T) return (Ty_rename_subtype_P _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => FJ_Ty_rename_subtype nat Ty ty_ext nat N  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id Context Empty
        subtype WF_Type nat fields nat nat Update E FJ_Ty_Wrap_inject md_ext cld_ext CT
        build_te Base_sub wf_class_ext wf_object_ext E_WF 
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext 
        L_build_context override FJ_WF_Type_Wrap_invert WF_CT Ty_rename
        TE_rename rename_context (fun _ _ => refl_equal _) 
        (GJ_rename_build_te nat Ty Gty nat N _ Context Empty subtype Ty_trans
          WF_Type TUpdate unit unit Free_Vars exists_Free_Vars wf_free_vars
          L_build_context' L_build_context'_Empty_1 Ty_trans_trans_subst plus
          Ty_rename Ty_rename_eq_Ty_trans FV_subst_tot)
        (GJ_rename_build_te_obj _ _ _ _ _ _ Ty_trans WF_Type TUpdate
          _ _ _ Ty_rename) Ty_rename_subtype delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Ty_rename_subtype _ _ Gty _ _ _ TLookup subtype 
        GJ_sub plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename rename_context 
        TLookup_rename_context GJ_Ty_rename_invert delta S' T' sub_S_T'
    end.
  
  Definition Free_Vars_id := ty_rect
    (Free_Vars_id_P _ _ Free_Vars) (Free_Vars_id_Q _ _ TE_Free_Vars)
    (GJ_Free_Vars_id _ _ Gty Free_Vars GJ_Free_Vars_invert GJ_Ty_Wrap_inject)
    (FJ_Free_Vars_id _ _ _ _ _ _ _ FJ_Ty_Wrap_inject Free_Vars TE_Free_Vars FJ_Free_Vars_invert)
    (Free_Vars_id_H3 _ _ _ Free_Vars)
    (Free_Vars_id_H4 _ _ _ _ Free_Vars TE_Free_Vars id (fun _ _ => id)).
    
  Definition Ty_rename_WF_Type := WF_Type_rect' 
    (Ty_rename_WF_Type_P _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_Q _ _ _ _ _ _ _ wf_class_ext Free_Vars cld_typs TE_rename 
      rename_context)
    (Ty_rename_WF_Type_P1 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext_H1 _ _ Gty _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
      _ subtype Ty_trans WF_Type _ _ Free_Vars
      exists_Free_Vars Ty_trans_trans_subst plus Ty_rename rename_context Ty_rename_eq_Ty_trans FV_subst_tot
      Ty_rename_subtype Free_Vars_id)
    (Ty_rename_WF_Type_ext_H2 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext_H3 _ _ _ WF_Type Ty_rename rename_context)
    (GJ_Ty_rename_WF_Type _ _ Gty _ _ TLookup WF_Type GJ_WF_Type plus Ty_rename _ rename_context 
      TLookup_rename_context GJ_Ty_rename_invert)
    (FJ_Ty_rename_WF_Type_H1 _ _ _ _ _ _ _ _ WF_Type _ _ _ _ _ _ CT wf_class_ext
      wf_object_ext Base_WF_Type Ty_rename TE_rename rename_context (fun _ _ => refl_equal _)
      (GJ_Ty_rename_WF_object _ _ _ _ Ty_rename rename_context))
    (FJ_Ty_rename_WF_Type_H2 _ _ _ _ _ _ _ _ Empty subtype WF_Type _ fields _ _ Update
      _ _ _ CT wf_class_ext wf_object_ext Base_WF_Type E_WF Free_Vars
      ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
      WF_CT cld_typs L_WF_bound Ty_rename TE_rename rename_context (fun _ _ => refl_equal _)).
  
  Fixpoint subtype_context_shuffle delta S T (sub_S_T : subtype delta S T) {struct sub_S_T} :=
    match sub_S_T in subtype delta S T return 
      (subtype_context_shuffle_P _ _ _ _ TLookup subtype app_context delta S T sub_S_T) with
      | Base_sub gamma S' T' sub_S_T' => FJ_subtype_context_shuffle _ _ _ _ _ _ _ _ TLookup
        subtype _ _ _ app_context _ _ _ CT build_te Base_sub subtype_context_shuffle
        _ _ _ sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_subtype_context_shuffle _ _ Gty _ _ _ 
        TLookup subtype GJ_sub app_context TLookup_app TLookup_dec
        TLookup_unique TLookup_app' TLookup_app'' _ _ _ sub_S_T'
    end.
    
  Definition WF_context_shuffle := WF_Type_rect' 
    (WF_context_shuffle_P _ _ _ _ TLookup WF_Type app_context)
    (WF_context_shuffle_Q _ _ _ _  TLookup app_context _ wf_class_ext)
    (WF_context_shuffle_P1 _ _ _ _ TLookup WF_Type app_context)
    (WF_context_shuffle_ext_H1 _ _ _ _ _ TLookup subtype Ty_trans WF_Type
      app_context _ _ subtype_context_shuffle)
    (WF_context_shuffle_ext_H2 _ _ _ _ TLookup WF_Type app_context)
    (WF_context_shuffle_ext_H3 _ _ _ _ TLookup WF_Type app_context)
    (GJ_WF_context_shuffle _ _ Gty _ _ TLookup WF_Type GJ_WF_Type app_context
      TLookup_app TLookup_dec TLookup_app' TLookup_app'')
    (FJ_WF_context_shuffle_H1 _ _ _ _ _ _ _ _ TLookup WF_Type _ _ _ app_context _
      _ _ CT wf_class_ext wf_object_ext Base_WF_Type 
      (GJ_WF_context_shuffle_obj_ext _ _ app_context _))
    (FJ_WF_context_shuffle_H2 _ _ _ _ _ _ _ _ TLookup WF_Type _ _ _ app_context _ _ _ CT
      wf_class_ext wf_object_ext Base_WF_Type).
    
  Definition FJ_Ty_rename_invert (ty : cFJ.FJ_Ty nat ty_ext) Y : 
    Ty_rename (Base_Ty ty) Y = FJ_Ty_rename _ _ _ _ _ _ _ _ ty Y := refl_equal _.
  
  Lemma rename_X_inject : forall X Y n, plus X n = plus Y n -> X = Y.
    clear; intros; omega.
  Qed.
    
  Definition FJ_Ty_Wrap_eq ty :=
    match ty return (Ty_rename_FJ_Ty_Wrap_eq_P _ _ _ _ _ N_Wrap id Ty_rename
      TE_rename ty) with
      | Base_Ty (ty_def te c) => FJ_Ty_rename_FJ_Ty_Wrap_eq _ _ _ _ _ N_Wrap _ FJ_Ty_Wrap_inject 
        Ty_rename TE_rename FJ_Ty_rename_invert te c
      | Gty (TyVar X) => GJ_Ty_rename_FJ_Ty_Wrap_eq _ _ _ Gty _ _ N_Wrap _ Ty_Wrap_discriminate 
        plus Ty_rename TE_rename GJ_Ty_rename_invert X 
    end.

  Definition Ty_rename_GJ_Ty_Wrap_eq ty :=
    match ty return (Ty_rename_GJ_Ty_Wrap_eq_P _ _ Gty Ty_rename ty) with
      | Base_Ty (ty_def te c) => FJ_Ty_rename_GJ_Ty_Wrap_eq _ _ _ Gty _ _ N_Wrap _ 
        Ty_Wrap_discriminate Ty_rename TE_rename FJ_Ty_rename_invert te c
      | Gty (TyVar X) => GJ_Ty_rename_GJ_Ty_Wrap_eq _ _ Gty plus Ty_rename 
        GJ_Ty_rename_invert X 
    end.

  Definition Ty_rename_inject := ty_rect
    (Ty_rename_inject_P _ _ Ty_rename)
    (Ty_rename_inject_Q _ _ TE_rename)
    (GJ_Ty_rename_inject _ _ Gty GJ_Ty_Wrap_inject plus Ty_rename rename_X_inject (fun _ _ => refl_equal _)
      Ty_rename_GJ_Ty_Wrap_eq)
    (FJ_Ty_rename_inject _ _ _ _ _ _ id Ty_rename TE_rename FJ_Ty_rename_invert FJ_Ty_Wrap_eq)
    (Ty_rename_inject_H3 _ _ _ Ty_rename)
    (Ty_rename_inject_H4 _ _ _ _ id GTy_ext_Wrap_inject Ty_rename
      TE_rename (fun _ _ => refl_equal _)).
  
  Fixpoint ex_Ty_rename_subtype delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in subtype delta S T return
      (ex_Ty_rename_subtype_P_r _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | Base_sub gamma S' T' sub_S_T' => FJ_ex_Ty_rename_subtype_P_r _ _ _ _ _ Base_Ty id
        _ Empty subtype WF_Type _ fields _ _ Update _ FJ_Ty_Wrap_inject _ _ CT build_te
        Base_sub wf_class_ext wf_object_ext E_WF _ _ _ _ _ 
        override FJ_WF_Type_Wrap_invert WF_CT Ty_rename TE_rename rename_context
        FJ_Ty_rename_invert FJ_Ty_Wrap_eq
        (GJ_TE_rename_build_te _ _ Gty _ _ _ _ Empty subtype Ty_trans WF_Type
          TUpdate _ _ Free_Vars exists_Free_Vars wf_free_vars _ L_build_context'_Empty_1
          Ty_trans_trans_subst plus Ty_rename Ty_rename_eq_Ty_trans FV_subst_tot)
        (GJ_TE_rename_build_obj_te _ _ _ _ Ty_trans _ _ Ty_rename)
        ex_Ty_rename_subtype gamma S' T' sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_ex_Ty_rename_subtype_P_r 
        _ _ Gty _ _ _ TLookup subtype GJ_sub plus Ty_rename NTy_rename
        Ty_rename_eq_NTy_rename rename_context TLookup_rename_context' gamma S' T' sub_S_T'
    end.
  
  Fixpoint Ty_rename_subtype' delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T in subtype delta S T return 
      (Ty_rename_subtype_P' _ _ _ subtype Ty_rename rename_context delta S T sub_S_T) with
      | Base_sub gamma S' T' sub_S_T' => FJ_Ty_rename_subtype' _ _ _ _ _ Base_Ty id _ 
        Empty subtype WF_Type _ fields _ _ Update _ FJ_Ty_Wrap_inject _ _ CT build_te Base_sub
        wf_class_ext wf_object_ext E_WF _ _ _ _ _ override
        FJ_WF_Type_Wrap_invert WF_CT Ty_rename TE_rename rename_context 
        FJ_Ty_Wrap_eq Ty_rename_inject 
        (GJ_TE_rename_build_te' _ _ Gty nat _ _ _ Empty subtype
          Ty_trans WF_Type TUpdate unit unit Free_Vars exists_Free_Vars
          wf_free_vars L_build_context' L_build_context'_Empty_1 Ty_trans_trans_subst plus Ty_rename 
          Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_inject)
        (GJ_TE_rename_build_obj_te' _ _ _ _ Ty_trans _ _ Ty_rename)
        ex_Ty_rename_subtype
        Ty_rename_subtype' _ _ _ sub_S_T'
      | GJ_sub gamma S' T' sub_S_T' => GJ_Ty_rename_subtype' _ _ Gty _ _ _ TLookup
        subtype GJ_sub GJ_Ty_Wrap_inject plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename
        rename_X_inject rename_context TLookup_rename_context' GJ_Ty_rename_invert 
        Ty_rename_GJ_Ty_Wrap_eq Ty_rename_inject _ _ _ sub_S_T'
    end.
  
  Definition Ty_rename_WF_Type' := WF_Type_rect' 
    (Ty_rename_WF_Type'_P _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type'_Q _ _ _ _ Base_Ty _ _ wf_class_ext Free_Vars cld_typs
      TE_rename rename_context)
    (Ty_rename_WF_Type'_P1 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext'_H1 _ _ Gty _ _ _ subtype Ty_trans WF_Type
      _ _ Free_Vars exists_Free_Vars Ty_trans_trans_subst plus Ty_rename
      rename_context Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype'
      Free_Vars_id)
    (Ty_rename_WF_Type_ext'_H2 _ _ _ WF_Type Ty_rename rename_context)
    (Ty_rename_WF_Type_ext'_H3 _ _ _ WF_Type Ty_rename rename_context)
    (GJ_Ty_rename_WF_Type' _ _ Gty _ _ TLookup WF_Type GJ_WF_Type
      GJ_Ty_Wrap_inject plus Ty_rename NTy_rename rename_X_inject rename_context
      TLookup_rename_context' GJ_Ty_rename_invert Ty_rename_GJ_Ty_Wrap_eq)
    (FJ_Ty_rename_WF_Type'_H1 _ _ _ _ _ _ id _ WF_Type _ _ _ _ _ _ CT
      wf_class_ext wf_object_ext Base_WF_Type Ty_rename TE_rename rename_context
      FJ_Ty_Wrap_eq 
      (GJ_Ty_rename_WF_object' _ _ _ _ Ty_rename rename_context))
    (FJ_Ty_rename_WF_Type'_H2 _ _ _ _ _ _ id _ Empty subtype WF_Type _ fields
      _ _ Update _ _ _ CT wf_class_ext wf_object_ext Base_WF_Type E_WF Free_Vars
      _ _ _ _ _ _ WF_CT cld_typs L_WF_bound Ty_rename TE_rename rename_context
      FJ_Ty_Wrap_eq).
  
  Definition sub_Free_Vars_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall delta S' T' Xs Us n, 
      gamma = rename_context delta n ->
      S = Ty_trans S' Xs (map (fun ty : Ty => Ty_rename ty n) Us) ->
      T = Ty_trans T' Xs (map (fun ty : Ty => Ty_rename ty n) Us) ->
      subtype (rename_context delta n) (Ty_rename (Ty_trans S' Xs Us) n)
      (Ty_rename (Ty_trans T' Xs Us) n).

  Definition Type_Subst_Sub_2_5_P' gamma S T (sub_S_T : subtype gamma S T) :=
    forall (delta_1  : Context) (Xs : list _)
      (Ns : list N) (Us : list Ty) (XNs : TyP_List),
      length Xs = length Us -> 
      zip Xs Ns (fun x => @pair _ _ (TyVar _ x)) = Some XNs ->
      gamma = (update_Tlist Empty XNs) -> 
      List_P2 Us Ns (fun U N => subtype delta_1 U (Ty_trans (Base_Ty N) Xs Us)) -> 
      List_P1 (WF_Type delta_1) Us -> 
      List_P1 (fun N => WF_Type (update_Tlist Empty XNs) (Base_Ty N)) Ns ->
      subtype (app_context delta_1 (subst_context Empty Xs Us)) 
      (Ty_trans S Xs Us) (Ty_trans T Xs Us).
  
  Variable (Finite_Context : forall gamma : Context, exists n,
    forall X ty ty' Ys, TLookup gamma X ty -> Free_Vars (Ty_rename ty' n) Ys -> ~ In X Ys).

  Fixpoint Type_Subst_Sub_2_5' delta S T (sub_S_T : subtype delta S T) : 
    Type_Subst_Sub_2_5_P' delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return (Type_Subst_Sub_2_5_P' delta S T sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => 
        FJ_Type_Subst_Sub_2_5' _ _ _ _ N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
        _ _ Empty subtype Ty_trans
        WF_Type _ fields _ _ TUpdate app_context Update _ FJ_Ty_Wrap_inject _ _ CT
        build_te Base_sub wf_class_ext wf_object_ext E_WF Free_Vars TE_trans FJ_Ty_trans_invert
        exists_Free_Vars N_trans subst_context
        ce_build_cte Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
        FJ_WF_Type_Wrap_invert WF_CT (@GJ_Type_Subst_Sub_2_5_TE _ _ _(Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
          _ Empty subtype Ty_trans WF_Type TUpdate _ _  Free_Vars exists_Free_Vars
          N_trans wf_free_vars map_Ty_trans' _ L_build_context'_Empty_1 
          _)
        (@GJ_Type_Subst_Sub_2_5_TE' _ _ _ _ _ subtype Ty_trans _ _ _ _ _ _ _)
        Ty_trans_eq_NTy_trans Type_Subst_Sub_2_5' delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Type_Subst_Sub_2_5' _ eq_nat_dec _ Gty _ _ _ Empty TLookup subtype
        GJ_sub Ty_trans WF_Type GJ_WF_Type TUpdate app_context Free_Vars
        GJ_Free_Vars' GJ_Ty_trans_invert TLookup_TUpdate_eq TLookup_TUpdate_neq' wf_free_vars subst_context 
        TLookup_unique  Ty_rename subst_context_Empty app_context_Empty Finite_Context
        delta S' T' sub_S_T'
    end.

  Definition Free_Vars_Ty_Rename := ty_rect
    (Free_Vars_Ty_Rename_P _ _ Free_Vars plus Ty_rename)
    (Free_Vars_TE_Rename_P _ _ TE_Free_Vars plus TE_rename)
    (GJ_Free_Vars_Ty_Rename _ _ Gty Free_Vars GJ_Free_Vars_invert
      GJ_Ty_Wrap_inject plus Ty_rename GJ_Ty_rename_invert)
    (FJ_Free_Vars_Ty_Rename _ _ _ _ _ _ _ FJ_Ty_Wrap_inject _ TE_Free_Vars FJ_Free_Vars_invert _
    Ty_rename TE_rename FJ_Ty_rename_invert)
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
           CT c = Some (cld nat nat nat nat ty_ext Ty E md_ext cld_ext ce c' d fds k' mds) ->
           c = c').

  Lemma L_build_context'_Empty_2 : forall (ce : _) (gamma : Context)
    (XNs : Generic.TyP_List _ _) (S T : Ty),
    L_build_context' ce gamma ->
    subtype (Generic.update_Tlist _ _ Context TUpdate gamma XNs) S T ->
    subtype (Generic.update_Tlist _ _ Context TUpdate Empty XNs) S T.
    intros; inversion H; subst.
    assumption.
  Qed.

  Definition WF_cld_ext_Lem := Generic.WF_cld_ext_Lem _ _ _ _ _ _ _ _ Empty subtype
    WF_Type _ fields _ _ Update _ _ _ CT wf_class_ext E_WF Free_Vars ce_build_cte
    Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context override
    WF_CT cld_typs L_WF_bound _ 
    (GJ_WF_cld_ext_Lem' _ eq_nat_dec _ Gty nat _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ Empty TLookup subtype
    Ty_trans WF_Type TUpdate app_context _ _ Weakening_2_1_2 Free_Vars
    GJ_Free_Vars' exists_Free_Vars N_trans wf_free_vars subst_context map_Ty_trans'
    _ L_build_context'_Empty_1 L_build_context'_Empty_2 TLookup_update_eq
    TLookup_update_neq TLookup_update_neq' Ty_trans_eq_NTy_trans Ty_trans_trans_subst
    plus Ty_rename NTy_rename Ty_rename_eq_NTy_rename rename_context TLookup_rename_context'
    GJ_Ty_rename_invert Ty_rename_eq_Ty_trans FV_subst_tot Ty_rename_subtype
    subst_context_Empty app_context_Empty Finite_Context Ty_rename_WF_Type Ty_rename_WF_Type'
    Type_Subst_Sub_2_5' WF_context_shuffle Free_Vars_Ty_Rename Type_Subst_WF_2_6 
    id_map_2).
  
  Definition WF_Type_par_Lem' delta ty (WF_ty : WF_Type delta ty) :
    WF_Type_par_Lem_P' delta ty WF_ty := 
    match WF_ty in (WF_Type delta ty) return WF_Type_par_Lem_P' delta ty WF_ty with 
      | Base_WF_Type gamma ty WF_base => 
        FJ_WF_Type_par_Lem' _ _ _ _ _ _ _
        _ _ _ CT Context wf_class_ext wf_object_ext WF_Type Base_WF_Type
        mtype_build_te L_build_context Base_inject
        WF_cld_ext_Lem
        gamma ty WF_base
      | GJ_WF_Type gamma ty WF_ty => GJ_WF_Type_par_Lem' _ _ _ _ _ _ _ _
        _ _ _ GJ_WF_Type _ _ _ _  Ty_Wrap_discriminate _ _ CT wf_class_ext L_build_context
        _ _ _ WF_ty
    end.

   Definition WF_Type_par delta ty (WF_ty : WF_Type delta ty) := 
     match WF_ty in (WF_Type delta ty) return 
       cFJ.WF_Type_par_P _ _ _ _ ty_ext Ty Base_Ty E _ _ CT _ WF_Type mtype_build_te
       L_build_context delta ty WF_ty with 
       | Base_WF_Type gamma ty WF_base => 
         FJ_WF_Type_par _ _ _ _ _ _ _ _ _ _ CT Context 
         wf_class_ext wf_object_ext WF_Type Base_WF_Type mtype_build_te
         L_build_context Base_inject WF_Type_par_Lem WF_Type_par_Lem' gamma ty WF_base
       | GJ_WF_Type delta ty WF_ty => GJ_WF_Type_par _ _ _ Gty _ _ N_Wrap id _ 
         TLookup WF_Type GJ_WF_Type _ _ _ _ Ty_Wrap_discriminate _ _ CT L_build_context 
         _ delta ty WF_ty
     end.
  
  Definition WF_fields_map_id''' : forall ty (gamma : Context) (ty' ty'' : Ty),
    WF_fields_map gamma ty ty' -> WF_fields_map gamma ty ty'' -> ty' = ty'' :=
    FJ_WF_fields_map_id'' Ty Context.

  Lemma N_Bound'_invert : forall (delta : Context) (n : N) (ty : Ty),
    Bound delta (N_Wrap n) ty ->
    N_Bound Ty N N_Wrap Context delta (N_Wrap n) ty.
    intros; inversion H; inversion H0; subst; assumption.
  Qed.

  Lemma GJ_Bound'_invert : forall (delta : Context) (n : GTy _) (ty : N),
    Bound delta (Gty n) (N_Wrap ty) ->
    Generic.GJ_Bound _ Ty Gty N Context TLookup delta (Gty n) ty.
    intros; inversion H; subst; try assumption; inversion H0.
  Qed.

  Lemma GJ_Bound'_invert' : forall (delta : Context) (Y : GTy _) (ty : Ty),
    Bound delta (Gty Y) ty -> exists n, ty = N_Wrap n /\ 
      Generic.GJ_Bound nat _ Gty N _ TLookup delta (Gty Y) n.
    intros; inversion H; inversion H0; subst; exists ty'; split; auto.
  Qed.

  Definition GJ_Bound_ty : forall (delta : Context) (ty : GTy _) (ty' : Ty),
    Bound delta (Gty ty) ty' -> exists n : N, ty' = N_Wrap n :=
      Generic.GJ_Bound_ty _ _ Gty _ N_Wrap _ TLookup Bound GJ_Bound'_invert'.

  Definition Bound_id' ty :=
    match ty return Bound'_id_P _ _ Bound ty with 
      | Base_Ty ty' => FJ_Bound'_id _ _ _ _ _ id _ Bound N_Wrap_inject N_Bound'_invert ty'
      | Gty ty' => GJ_Bound'_id _ _ Gty _ _ _ TLookup Bound GJ_Ty_Wrap_inject TLookup_id
        GJ_Bound'_invert' ty'
    end.

  Definition Bound_id gamma ty ty' (Bnd : Bound gamma ty ty') :=
    match Bnd in (Bound gamma ty ty') return (forall ty'', Bound gamma ty ty'' -> ty' = ty'') with
      | GJ_Bound _ _ _ Bnd' => GJ_Bound_id _ _ Gty _ _ _ TLookup Bound
        GJ_Ty_Wrap_inject TLookup_unique GJ_Bound'_invert GJ_Bound'_invert' _ _ _ Bnd'
      | FJ_Bound _ _ _ Bnd' => N_Bound_id _ _ _ _ Bound N_Bound'_invert _ _ _ Bnd'
    end.

  Lemma N_Bound'_invert' : forall (delta : Context) (n : N) (ty : Ty),
    Bound delta (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id n) ty ->
    N_Bound Ty N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) Context delta
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id n) ty.
    intros; inversion H; inversion H0; subst.
    unfold Generic.FJ_Ty_Wrap; unfold id; constructor.
  Qed.

  Definition bld_te_eq_fields_build_te := Generic.bld_te_eq_fields_build_te nat Ty N Ty_trans _ _
    cFJ.FJ_bld_te_eq_fields_build_te.

  Definition WF_mtype_ty_0_map_refl := Generic.GJ_WF_mtype_ty_0_map_refl _ _ _ _ N_Wrap id _ 
    Bound FJ_Bound.

  Fixpoint Lem_2_8' delta S T sub_S_T : 
    cFJ.Lem_2_8_P nat Ty Context subtype fields Bound Empty delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return 
      (cFJ.Lem_2_8_P nat Ty Context subtype fields Bound Empty delta S T sub_S_T) with
      | Base_sub gamma' S' T' sub_S_T' =>
        FJ_Lem_2_8 nat nat nat nat ty_ext Ty _ E _ _
        CT Context subtype build_te Base_sub fields fields_build_te
        fields_build_tys FJ_fields Bound Empty 
        (Bound_tot _ _ _ _ _ _ _ Bound FJ_Bound) fields_build_tys_tot Bound_id'
        (fun gamma ty => FJ_Bound _ _ _ (N_bound _ _ N_Wrap _ gamma ty))
        bld_te_eq_fields_build_te gamma' S' T' sub_S_T' Lem_2_8'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Lem_2_8 _ _ Gty N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ Empty TLookup 
        subtype GJ_sub _ fields Bound GJ_Bound N_Wrap_inject N_Bound'_invert'
        gamma' S' T' sub_S_T'
    end.
      
  Variable build_fresh_id : forall tys ty tys' Xs Ys Xs' Xs'', build_fresh tys ty tys' Xs Ys Xs' -> 
    build_fresh tys ty tys' Xs Ys Xs'' -> Xs' = Xs''.

  Definition build_V' gamma1 m ty mde' Ws W (H : override gamma1 m ty mde' Ws W) := H.
    
  Definition WF_Bound_id delta S T T' (Bound_S : Bound delta S T) :=
    match Bound_S in Bound delta S T return Bound delta S T' -> T = T' with
      | GJ_Bound delta' S' T'' Bound_S' => GJ_Bound_id _ _ Gty _ N_Wrap _ 
        TLookup Bound GJ_Ty_Wrap_inject TLookup_unique GJ_Bound'_invert
        GJ_Bound'_invert' _ _ _ Bound_S' T'
      | FJ_Bound delta' S' T'' Bound_S' => N_Bound_id _ _ N_Wrap _ Bound
        N_Bound'_invert _ _ _ Bound_S' T'
    end.

  Definition In_m_mds_dec := cFJ.In_m_mds_dec _ nat Ty E md_ext eq_nat_dec.
  
  Definition WF_mtype_ty_0_map_TLookup := GJ_WF_mtype_ty_0_map_TLookup _ _ Gty _ 
    N_Wrap _ TLookup Bound GJ_Bound.

  Variable build_fresh_len : forall tys ty vds Xs Ws Ys, 
    build_fresh tys ty vds Xs Ws Ys -> length Ws = length Ys.

  Variable build_fresh_tot : forall tys ty tys' Xs Ys, exists Xs', build_fresh tys ty tys' Xs Ys Xs'.

  Definition mtype_build_mtye_tot := Generic.mtype_build_mtye_tot _ _ Gty _ Ty_trans _ _ 
    build_fresh N_Trans _ _ _ build_fresh_tot build_fresh_len _ _ (FJ_mtype_build_mtye_tot nat Ty). 

  Definition mtype_build_tys_tot := Generic.mtype_build_tys_tot _ _ Gty _ Ty_trans _ build_fresh
    N_Trans _ _ _ build_fresh_tot build_fresh_len _ _ (FJ_mtype_build_tys_tot nat Ty).

  Lemma N_Wrap_inject' : forall n n' : N, 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) n = (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) n' -> n = n'.
    intros; injection H; auto.
  Qed.

  Definition Bound'_id (S : Ty) : Bound'_id_P _ _ Bound S :=
    match S return Bound'_id_P _ _ Bound S with 
      | Gty ty => GJ_Bound'_id _ _ Gty _ _ _ TLookup Bound GJ_Ty_Wrap_inject 
        TLookup_id GJ_Bound'_invert' ty
      | Base_Ty ty => FJ_Bound'_id _ _ _ _ _ id _ Bound N_Wrap_inject N_Bound'_invert ty
    end.

  Definition WF_mtype_ty_0_map_id := Bound'_id.

  Definition build_te_build_mtye_te'' := 
    Generic.GJ_build_te_build_mtye_te'' _ _ N Ty_trans _ _ FJ_mtype_build_te FJ_build_te
    FJ_build_te_build_mtye_te''.

  Definition build_te_build_ty_0_id := Generic.build_te_build_ty_0_id _ _ _ _ _ _ _
    FJ_Ty_Wrap_inject _ build_te WF_mtype_ty_0_map mtype_build_te WF_mtype_ty_0_map_id
    WF_mtype_ty_0_map_refl build_te_build_mtye_te''.

  Definition mtype_build_tys_len' := Generic.mtype_build_tys_len' _ _ _ Gty N Ty_trans _ build_fresh _
    _ _ (FJ_mtype_build_tys_len nat Ty).

  Lemma WF_Type_invert : forall (delta : Context) (S : cFJ.FJ_Ty _ ty_ext), WF_Type delta (Base_Ty S) ->
    cFJ.FJ_WF_Type _ _ _ _ ty_ext Ty  (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E md_ext cld_ext CT Context 
    wf_class_ext wf_object_ext delta (Base_Ty S).
    intros; inversion H; subst; auto.
    inversion H0.
  Qed.

  Fixpoint Lem_2_9 gamma S T (sub_S_T : subtype gamma S T) : 
    Lem_2_9_P _ _ _ _ _ subtype mtype Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T :=
    match sub_S_T return Lem_2_9_P _ _ _ _ _ subtype mtype Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T with
      | Base_sub gamma S' T' sub_S_T' => cFJ.FJ_Lem_2_9 _ _ _ _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
        _ _ _ _ _ CT _ subtype build_te Base_sub wf_class_ext wf_object_ext
        WF_Type fields mtype mtype_build_te mtype_build_tys
        mtype_build_mtye FJ_mtype E_WF Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty
        Update ce_build_cte Meth_build_context Meth_WF_Ext override L_WF_Ext L_build_context
        WF_CT FJ_Ty_Wrap_inject WF_mtype_ty_0_map_total mtype_build_tys_len' 
        WF_Type_invert (fun g S T T' Bnd=> Bound_id g S T Bnd T') eq_nat_dec
        build_te_build_ty_0_id WF_mtype_ty_0_map_refl mtype_build_tys_tot 
        mtype_build_mtye_tot build_V' gamma S' T' sub_S_T' Lem_2_9
      | GJ_sub gamma S' T' sub_S_T' => Generic.GJ_Lem_2_9 _ _ _ Gty _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
        _ _ Empty TLookup subtype GJ_sub _ _ _ _ mtype _ _ _ CT build_te 
        Base_sub _ Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext 
        WF_mtype_ty_0_map_id WF_mtype_ty_0_map_refl WF_mtype_ty_0_map_TLookup gamma S' T' sub_S_T'
    end.

  Fixpoint Subtype_Weaken gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T in (subtype gamma S T) return (Subtype_Weaken_P Ty Context subtype Empty gamma S T sub_S_T) with
      | Base_sub gamma' S' T' sub_S_T' => 
        FJ_Subtype_Weaken _ _ _ _ _ _ _ _ _ _ CT _ subtype build_te
        Base_sub Empty gamma' S' T' sub_S_T' Subtype_Weaken
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Subtype_Weaken _ _ Gty _ _ _ Empty TLookup _ GJ_sub TLookup_Empty _ _ _ sub_S_T'
    end.

  Variable TLookup_TUpdate_neq : forall gamma Y X ty ty', TLookup gamma X ty -> X <> Y -> 
       TLookup (TUpdate gamma Y ty') X ty.

  Fixpoint Weaken_subtype_app_TList delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return (Weaken_subtype_app_TList_P _ _ _ _  Empty subtype TUpdate _ _ _ sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => 
        FJ_Weaken_subtype_app_TList _ _ _ _ _ Base_Ty id _ Empty subtype _ _ _ TUpdate
        _ _ _ CT build_te Base_sub Weaken_subtype_app_TList delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => GJ_Weaken_subtype_app_TList _ eq_nat_dec _ Gty _ _
        _ Empty TLookup subtype GJ_sub TUpdate TLookup_Empty TLookup_TUpdate_eq TLookup_TUpdate_neq
        TLookup_TUpdate_neq' TLookup_id delta S' T' sub_S_T'
    end.

  Definition Weaken_WF_Type_app_TList :=
    WF_Type_rect' (Weaken_WF_Type_app_TList_P _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_Q _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate _ _)
    (Weaken_WF_Type_app_TList_P1 _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_ext_H1 _ _ _ _ _ Empty subtype Ty_trans WF_Type TUpdate _ _ 
      Weaken_subtype_app_TList)
    (Weaken_WF_Type_app_TList_ext_H2 _ _ _ _ Empty WF_Type TUpdate)
    (Weaken_WF_Type_app_TList_ext_H3 _ _ _ _ Empty WF_Type TUpdate)
    (GJ_Weaken_WF_Type_app_TList _ eq_nat_dec _ Gty _ _ Empty TLookup WF_Type 
      GJ_WF_Type TUpdate TLookup_Empty TLookup_TUpdate_eq TLookup_TUpdate_neq TLookup_TUpdate_neq'
      TLookup_id)
    (FJ_Weaken_WF_Type_app_TList_H1 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ _ _ CT wf_class_ext
      wf_object_ext Base_WF_Type (Weaken_WF_Type_app_TList_obj_ext _ _ _ _ Empty TUpdate _))
    (FJ_Weaken_WF_Type_app_TList_H2 _ _ _ _ _ _ _ _ Empty WF_Type _ _ _ TUpdate _ _ _
      CT wf_class_ext wf_object_ext Base_WF_Type).
          
  Definition FJ_NTy_trans_invert (ty : Generic.Base_Ty ty_ext nat) (txs : list nat) (tys : list Ty) : 
    Ty_trans ((Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) (id ty)) txs tys =
    FJ_Ty_Trans _ Ty ty_ext _ N (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id TE_trans ty txs tys :=
    refl_equal _.

  Definition Bound'_Trans := Generic.Bound'_Trans _ _ _ _ _ Ty_trans Bound FJ_Bound
    N_trans Ty_trans_eq_NTy_trans.

  Definition FJ_ex_WF_Bound' := FJ_ex_WF_Bound' _ _ _ _ _ id _ WF_Type Bound FJ_Bound.

  Lemma GJ_WF_Type_invert : forall gamma ty , WF_Type gamma (Gty ty) ->
    Generic.GJ_WF_Type _ Ty Gty N Context TLookup gamma (Gty ty).
    intros; inversion H; subst; auto; inversion H0.
  Qed.

  Fixpoint ex_WF_Bound' (S : Ty) := 
    match S return ex_WF_Bound'_P Ty N N_Wrap Context WF_Type Bound S with
      | Base_Ty (ty_def te c) => FJ_ex_WF_Bound' te c
      | Gty (TyVar X) => GJ_ex_WF_Bound' _ _ Gty _ _ _ TLookup WF_Type Bound GJ_Bound GJ_Ty_Wrap_inject
        GJ_WF_Type_invert X
      end.

  Fixpoint sub_Bound delta S T (sub_S_T : subtype delta S T) : 
    (sub_Bound'_P _ _ subtype Bound _ _ _ sub_S_T) :=
    match sub_S_T return (sub_Bound'_P _ _ subtype Bound  _ _ _ sub_S_T) with
      | Base_sub delta S' T' sub_S_T' => 
        FJ_sub_Bound' _ _ _ _ _ _
        _ subtype _ _ _ _ Bound _ _ CT build_te Base_sub
        N_Wrap_inject N_Bound'_invert WF_mtype_ty_0_map_total Bound_id'
        sub_Bound delta S' T' sub_S_T'
      | GJ_sub delta S' T' sub_S_T' => 
        GJ_sub_Bound' _ _ _ Gty _ _ _ _ _ TLookup subtype GJ_sub _ _ _ _ 
        Bound _ _ CT build_te Base_sub GJ_Ty_Wrap_inject TLookup_id
        N_Wrap_inject N_Bound'_invert' GJ_Bound'_invert' delta S' T' sub_S_T'
    end.

  Definition Lem_2_7 (T :Ty) :=
    match T return Generic.Lem_2_7_P _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
      _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound T with 
      | Base_Ty (ty_def te c) => FJ_Lem_2_7 _ _ _ _ _ _ _
        Context Empty subtype Ty_trans WF_Type _ _ _ TUpdate Update _ Bound
        FJ_Bound _ _ CT build_te Base_sub TE_trans FJ_Ty_trans_invert
        N_Wrap_inject N_Bound'_invert FJ_NTy_trans_invert te c
      | Gty (TyVar X) => GJ_Lem_2_7 _ eq_nat_dec _ Gty _ _
        _ Empty TLookup subtype Ty_trans WF_Type _ TUpdate Update TLookup_Update
        TLookup_Empty Bound FJ_Bound GJ_Ty_Wrap_inject GJ_Ty_trans_invert 
        TLookup_TUpdate_eq TLookup_TUpdate_neq TLookup_TUpdate_neq' TLookup_id 
        _ Ty_trans_eq_NTy_trans GJ_Bound'_invert' sub_Bound ex_WF_Bound' X
    end.

  Lemma map_e_invert : forall XNs Us e e',
    E_Ty_Trans XNs Us (Base_E e) e' -> Generic.E_Ty_Trans _ _ _ _ _ _ _ _ _ _
    Base_E mbody_m_call_map mbody_new_map E_Ty_Trans XNs Us (Base_E e) e'.
    intros; inversion H; subst; auto; inversion H0.
  Qed.

  Definition WF_fields_map_sub (X : Ty) : Bound'_sub_P _ _ subtype Bound X :=
    match X return Bound'_sub_P _ _ subtype Bound X with
      | Base_Ty ty => N_Bound'_sub _ _ _ _ N_Wrap _ _ subtype _ _ _ _ Bound _ _ CT
      _ Base_sub N_Bound'_invert ty
      | Gty ty => GJ_Bound'_sub _ _ Gty _ _ _ TLookup subtype GJ_sub Bound
        GJ_Ty_Wrap_inject GJ_Bound'_invert' ty
    end.
    
  Variable lookup_TUpdate : forall gamma X N x ty, lookup (TUpdate gamma X N) x ty -> lookup gamma x ty.
  Variable lookup_TUpdate' : forall gamma X N x ty, lookup gamma x ty -> lookup (TUpdate gamma X N) x ty.
    
  Lemma EWrap_inject : forall e e', Base_E e = Base_E e' -> e = e'.
    intros; injection H; intros; assumption.
  Qed.

  Definition WF_mtype_map_sub gamma ty ty' (Bnd : Bound gamma ty ty') :=
    match Bnd in Bound gamma ty ty' return (WF_mtype_mab_sub_def Ty Context subtype Bound gamma ty ty' Bnd) with 
      | FJ_Bound _ _ _ Bnd' => N_WF_mtype_map_sub _ _ _ _ _ _ _ subtype _ _ _ _ Bound FJ_Bound _ _ 
        CT build_te Base_sub _ _ _ Bnd'
      | GJ_Bound _ _ _ Bnd' => GJ_WF_mtype_map_sub _ _ _ _ _ _ TLookup _ GJ_sub Bound GJ_Bound _ _ _ Bnd'
    end.

  Fixpoint Trans_Bound' T :=
    match T return Trans_Bound'_P _ _ _ Ty_trans Bound T with
      | Base_Ty T' => FJ_Trans_Bound' _ _ _ _ _ _ _ _ Ty_trans Bound FJ_Bound 
        TE_trans FJ_Ty_trans_invert N_Wrap_inject N_Bound'_invert T'
      | Gty T' => GJ_Trans_Bound' _ _ Gty _ _ _ TLookup Ty_trans Bound FJ_Bound GJ_Ty_Wrap_inject
        _ Ty_trans_eq_NTy_trans GJ_Bound'_invert' T'
    end.

  Definition Trans_WF_mtype_map := Trans_Bound'.
  Definition Trans_WF_fields_map := Trans_Bound'.

  Fixpoint subtype_update_list_id' delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return subtype_update_list_id'_P _ _ subtype _ Update _ _ _ sub_S_T with
      | Base_sub delta' S' T' sub_S_T' => FJ_subtype_update_list_id' _ _ _ _ _ _ _ 
        subtype _ _ _ Update _ _ _ CT build_te Base_sub subtype_update_list_id' _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_subtype_update_list_id' _ _ _ _ _ _ 
        TLookup subtype GJ_sub _ Update TLookup_Update' _ _ _ sub_S_T'
    end.

    Definition WF_Type_update_list_id' :=
    WF_Type_rect' (WF_Type_update_list_id'_P _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_Q _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _)
    (WF_Type_update_list_id'_P1 _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _ 
      subtype_update_list_id')
    (WF_Type_update_list_id'_ext_H2 _ _ WF_Type _ Update)
    (WF_Type_update_list_id'_ext_H3 _ _ WF_Type _ Update)
    (GJ_WF_Type_update_list_id' _ _ Gty _ _ TLookup WF_Type GJ_WF_Type _ Update TLookup_Update')
    (FJ_WF_Type_update_list_id'_H1 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _ CT wf_class_ext
      wf_object_ext Base_WF_Type (WF_Type_update_list_id'_obj_ext _ _ _ Update _))
    (FJ_WF_Type_update_list_id'_H2 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _ CT wf_class_ext wf_object_ext
      Base_WF_Type).


  Fixpoint subtype_update_Tupdate delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return subtype_update_Tupdate_P _ _ _ _ subtype _ TUpdate Update _ _ _ sub_S_T with
      | Base_sub delta' S' T' sub_S_T' => FJ_subtype_update_Tupdate _ _ _ _ _ _ _ _ subtype
        _ _ _ TUpdate Update _ _ _ CT build_te Base_sub subtype_update_Tupdate _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_subtype_update_Tupdate _ eq_nat_dec _ Gty _ _ _ TLookup
        subtype GJ_sub _ TUpdate Update TLookup_Update TLookup_Update' TLookup_TUpdate_eq
        TLookup_TUpdate_neq TLookup_TUpdate_neq' TLookup_id _ _ _ sub_S_T'
    end.

    Definition WF_Type_update_Tupdate :=
    WF_Type_rect' (WF_Type_update_Tupdate_P _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_Q _ _ _ _ _ subtype Ty_trans WF_Type _ TUpdate Update _ _)
    (WF_Type_update_Tupdate_P1 _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ TUpdate Update _ _ 
      subtype_update_Tupdate)
    (WF_Type_update_Tupdate_ext_H2 _ _ _ _ WF_Type _ TUpdate Update)
    (WF_Type_update_Tupdate_ext_H3 _ _ _ _ WF_Type _ TUpdate Update)
    (GJ_WF_Type_update_Tupdate _ eq_nat_dec _ Gty _ _ TLookup WF_Type GJ_WF_Type _ 
      TUpdate Update TLookup_Update TLookup_Update' TLookup_TUpdate_eq TLookup_TUpdate_neq
      TLookup_TUpdate_neq' TLookup_id)
    (FJ_WF_Type_update_Tupdate_H1 _ _ _ _ _ _ _ _ WF_Type _ _ _ TUpdate Update _ _ _ CT 
      wf_class_ext wf_object_ext Base_WF_Type 
      (WF_Type_update_Tupdate_obj_ext _ _ _ _ _ TUpdate Update _))
    (FJ_WF_Type_update_Tupdate_H2 _ _ _ _ _ _ _ _ WF_Type _ _ _ TUpdate Update _ _ _ 
      CT wf_class_ext wf_object_ext Base_WF_Type).

    Definition exists_Free_Vars_P2 := exists_Free_Vars_P2 nat Ty Free_Vars exists_Free_Vars.

  Lemma Ty_trans_eq_N_Trans : forall N0 XNs Us,
    N_Wrap (N_Trans XNs Us N0) = Ty_trans (N_Wrap N0) (Extract_TyVar _ N XNs) Us.
    unfold N_Wrap; unfold N_Trans; destruct N0; simpl; reflexivity.
  Qed.
    
  Definition GJ_TE_Free_Vars_Wrap (te : GTy_ext Ty) (txs : list _) :
                          GJ_TE_Free_Vars _ _ _ Free_Vars te txs ->
                          TE_Free_Vars (id te) txs := id.

  Definition Ty_trans_no_op := ty_rect
    (Ty_trans_no_op_P _  _ Ty_trans Free_Vars)
    (Ty_trans_no_op_Q _ _ _ TE_Free_Vars TE_trans)
    (GJ_Ty_trans_no_op _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_invert 
      GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_Ty_trans_no_op _ _ _ _ _ N_Wrap id Ty_trans FJ_Ty_Wrap_inject Free_Vars
      TE_Free_Vars FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (Ty_trans_no_op_H3 _ _ _ Ty_trans _ Free_Vars id GTy_ext_Wrap_inject)
    (Ty_trans_no_op_H4 _ _ _ Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_Wrap
      TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Definition Ty_trans_app :=
    ty_rect (Ty_trans_app_P _ _ Ty_trans Free_Vars)
    (TE_trans_app_Q _ _ _ TE_Free_Vars TE_trans)
    (GJ_Ty_trans_app _ eq_nat_dec _ Gty _ _ GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert)
    (FJ_Ty_trans_app _ _ _ _ _ _ _ _ FJ_Ty_Wrap_inject _ _ FJ_Free_Vars_invert _ FJ_Ty_trans_invert)
    (TE_trans_app_H1 _ _ _ _ Free_Vars)
    (TE_trans_app_H2 _ _ _ _ _ ).

  Definition GJ_Free_Vars_Wrap := GJ_Free_Vars'.

  Definition  Ty_trans_fresh_vars :=
    ty_rect (Ty_trans_fresh_vars_P _ _ Gty Ty_trans Free_Vars)
    ( Ty_trans_fresh_vars_Q _ _ _ Gty Free_Vars TE_Free_Vars TE_trans)
    (GJ_Ty_trans_fresh_vars _ eq_nat_dec _ Gty Ty_trans Free_Vars GJ_Free_Vars_Wrap
      GJ_Free_Vars_invert GJ_Ty_Wrap_inject GJ_Ty_trans_invert Ty_trans_nil Free_Vars_Subst
      Ty_trans_trans_subst Ty_trans_app Ty_trans_no_op)
    (FJ_Ty_trans_fresh_vars _ _ _ Gty _ _ N_Wrap id Ty_trans FJ_Ty_Wrap_inject Free_Vars
      TE_Free_Vars FJ_Free_Vars_invert TE_trans FJ_Ty_trans_invert)
    (Ty_trans_fresh_vars_H3 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id TE_trans
      GJ_TE_Trans_invert)
    (Ty_trans_fresh_vars_H4 _ _ _ Gty Ty_trans _ Free_Vars TE_Free_Vars id GJ_TE_Free_Vars_Wrap
      GJ_TE_Free_Vars_invert TE_trans GTy_ext_Wrap_inject GJ_TE_Trans_invert).

  Lemma te_eq : forall te te' : FJ_ty_ext, te = te'.
    destruct te; destruct te'; reflexivity.
  Qed.

  Fixpoint Strengthen_subtype_update_TList delta S T (sub_S_T : subtype delta S T) :=
    match sub_S_T return Strengthen_subtype_update_TList_P _ _ subtype _ Update _ _ _ sub_S_T with
      | Base_sub delta' S' T' sub_S_T' => FJ_Strengthen_subtype_update_TList _ _ _ _ _ _ _ 
        subtype _ _ _ Update _ _ _ CT build_te Base_sub Strengthen_subtype_update_TList _ _ _ sub_S_T'
      | GJ_sub delta' S' T' sub_S_T' => GJ_Strengthen_subtype_update_TList _ _ Gty _ _ _ TLookup 
        subtype GJ_sub _ Update TLookup_Update _ _ _ sub_S_T'
    end.
  
  Definition Strengthen_WF_Type_update_TList :=
    WF_Type_rect' (Strengthen_WF_Type_update_TList_P _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_Q _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _)
    (Strengthen_WF_Type_update_TList_P1 _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update _ _
      Strengthen_subtype_update_TList)
    (Strengthen_WF_Type_update_TList_ext_H2 _ _ WF_Type _ Update)
    (Strengthen_WF_Type_update_TList_ext_H3 _ _ WF_Type _ Update)
    (GJ_Strengthen_WF_Type_update_TList _ _ Gty _ _ TLookup WF_Type GJ_WF_Type
      _ Update TLookup_Update)
    (FJ_Strengthen_WF_Type_update_TList_H1 _ _ _ _ _ _ _ WF_Type _ _ _ Update _ _ _
      CT wf_class_ext wf_object_ext Base_WF_Type
    (Strengthen_WF_Type_update_TList_obj_ext _ _ _ Update _))
    (FJ_Strengthen_WF_Type_update_TList_H2 _ _ _ _ _ _ _ WF_Type _ _ _ 
      Update _ _ _ CT wf_class_ext wf_object_ext Base_WF_Type).

  Variable Ty_trans_mtype : forall (delta : Context) (m : _) 
    (S : Ty) (mty' : Mty Ty _)
    (mtype_S : mtype delta m S mty'),
    Ty_trans_mtype_P _ Ty N N_Wrap Context Empty subtype
    Ty_trans WF_Type _ _ _ mtype TUpdate Update
    m_call_ext WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext
    mbody_m_call_map delta m S mty' mtype_S.

  Fixpoint Bound_total gamma S T (sub_S_T : subtype gamma S T) :=
    match sub_S_T return Bound_total_P _ _ subtype Bound _ _ _ sub_S_T with 
      | Base_sub gamma' S' T' sub_S_T' => FJ_Bound_total _ _ _ _ _ _ _ subtype _ _ _ _ 
        Bound FJ_Bound _ _ CT build_te Base_sub Bound_total _ _ _ sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => GJ_Bound_total _ _ Gty _ _ 
        _ TLookup subtype GJ_sub Bound GJ_Bound _ _ _ sub_S_T'
    end.

  Fixpoint Lem_2_7'' (S : Ty) :=
    match S return Lem_2_7''_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ TUpdate Update Bound S with
      | Base_Ty S' => FJ_Lem_2_7'' _ _ _ _ _ _ _ _ Empty subtype Ty_trans WF_Type _ _ _ 
        TUpdate Update _ Bound FJ_Bound _ _ CT build_te Base_sub TE_trans FJ_Ty_trans_invert
        N_Wrap_inject N_Bound'_invert S'
      | Gty S' => GJ_Lem_2_7'' _ eq_nat_dec _ Gty _ _ _ Empty TLookup subtype Ty_trans
        WF_Type _ TUpdate Update TLookup_Update TLookup_Update' TLookup_Empty Bound
        GJ_Ty_Wrap_inject GJ_Ty_trans_invert TLookup_TUpdate_eq TLookup_TUpdate_neq
        TLookup_TUpdate_neq' TLookup_id Bound_total GJ_Bound'_invert' Trans_Bound'
        sub_Bound S'
    end.

  Definition WF_mtype_ext_update_list := GJ_WF_mtype_ext_update_list _ _ N Base_Ty _ subtype Ty_trans
    WF_Type _ _ Update _ (FJ_WF_mtype_ext Context) subtype_update_list_id' WF_Type_update_list_id'
    (FJ_WF_mtype_ext_update_list _ _ _ _ ).

  Definition WF_mtype_Us_map_update_list := Generic.GJ_WF_mtype_Us_map_update_list _ _ N _ Ty_trans
    _ _ Update _ (FJ_WF_mtype_Us_map Ty Context) (FJ_WF_mtype_Us_map_update_list _ _ _ Update).

  Definition WF_mtype_U_map_update_list := Generic.GJ_WF_mtype_U_map_update_list _ _ N _ Ty_trans
    _ _ Update _ (FJ_WF_mtype_U_map Ty Context) (FJ_WF_mtype_U_map_update_list _ _ _ Update).

    Definition Strengthen_Bound (S : Ty) := 
      match S return Strengthen_Bound''_P _ _ _ Update Bound S with 
        | Base_Ty (ty_def te' c') => FJ_Strengthen_Bound'' _ _ _ _ _ id _ _ Update Bound FJ_Bound N_Wrap_inject
          N_Bound'_invert te' c'
        | Gty (TyVar X) => GJ_Strengthen_Bound'' _ _ Gty _ _ _ TLookup _ Update TLookup_Update' Bound 
          GJ_Bound GJ_Ty_Wrap_inject GJ_Bound'_invert' X
      end.

    Definition Strengthen_Bound' (S : Ty) := 
      match S return Strengthen_Bound'_P _ _ _ Update Bound S with 
        | Base_Ty (ty_def te' c') => FJ_Strengthen_Bound' _ _ _ _ _ id _ _ Update Bound FJ_Bound N_Wrap_inject
          N_Bound'_invert te' c'
        | Gty (TyVar X) => GJ_Strengthen_Bound' _ _ Gty _ _ _ TLookup _ Update TLookup_Update Bound 
          GJ_Bound GJ_Ty_Wrap_inject GJ_Bound'_invert' X
      end.

  Definition update_list_WF_mtype_ty_0_map := Strengthen_Bound.

    Definition WF_fields_build_tys' := Generic.FJ_WF_fields_build_tys Ty Context WF_Type.

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

  Fixpoint Lem_2_11 gamma e T (WF_e : E_WF gamma e T) :
    Generic.Lem_2_11_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ TUpdate
    Update E E_WF E_Ty_Trans gamma e T WF_e :=
    match WF_e in E_WF gamma e T return Generic.Lem_2_11_P _ _ _ _ _ Empty subtype Ty_trans WF_Type _ 
      TUpdate Update E E_WF E_Ty_Trans gamma e T WF_e with
      | FJ_E_WF gamma e ty FJ_case => Generic.FJ_Lem_2_11 _ eq_nat_dec _ _ Gty _ _ 
        (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ Empty TLookup subtype Ty_trans
        WF_Type _ fields _ _ _ mtype TUpdate app_context Update _ Subtype_Update_list_id
        _ _ CT build_te Base_sub Weakening_2_1_2 _ Base_E E_WF lookup
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
        
  Definition build_cte_Free_Vars := Generic.build_cte_Free_Vars _ _ Gty N _ _ Free_Vars
    GJ_Free_Vars_invert GJ_Ty_Wrap_inject FJ_ce_build_cte.

  Definition build_context'_Empty_1 := FJ_build_context'_Empty_1 _ _ _ _ Empty WF_Type _ TUpdate Update.

  Definition build_context'_Empty_2 := FJ_build_context'_Empty_2 _ _ _ _ Empty subtype _ TUpdate Update.

  Definition build_context'_Empty_3 := FJ_build_context'_Empty_3 _ _ _ _ Empty _ TUpdate Update _ E_WF.

  Definition WF_mtype_U_map'_id := Generic.FJ_WF_mtype_U_map'_id Ty Context.

  Definition WF_mtype_Us_map'_id := Generic.FJ_WF_mtype_Us_map'_id Ty Context.

  Definition mtype_build_tys'_id := Generic.FJ_mtype_build_tys'_id Ty nat.

  Definition TE_trans_app (te : ty_ext) := GJ_TE_trans_app _ _ Ty_trans _ Free_Vars Ty_trans_app te.

  Definition exists_TE_Free_Vars (te : ty_ext) := GJ_exists_TE_Free_Vars _ _ _ Free_Vars exists_Free_Vars te.

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
                   (Vars : list (Var _ * Ty)),
                 L_WF_Ext gamma' ce c ->
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
                        FJ_Ty_Wrap Ty ty_ext _ N N_Wrap id
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
                   (FJ_Ty_Wrap Ty ty_ext _ N N_Wrap id
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
                     S0'' := Generic.GJ_Build_S0''' _ _ _ Gty _ _ (FJ_Ty_Wrap Ty ty_ext _ N N_Wrap id) id
    _ Empty subtype Ty_trans WF_Type _ _ _ build_fresh N_Trans TUpdate
    app_context Update _ _ _ Subtype_Update_list_id _ _ CT build_te
    Base_sub E_WF Free_Vars TE_Free_Vars TE_trans FJ_Ty_trans_invert exists_Free_Vars
    wf_free_vars subst_context L_build_context' L_build_context'_Empty_1 Free_Vars_id subst_context_Empty
    app_context_Empty Type_Subst_Sub_2_5' (@id_map_2 _ _ FJ_ty_ext) build_fresh_len subtype_update_Tupdate Ty_trans_app
    TE_trans_app WF_Type_update_Tupdate Strengthen_WF_Type_update_TList E_Ty_Trans _ _ _ _ _ _ _ _ _ _
    (FJ_WF_mtype_Us_map Ty Context) _ _ 
    mtype_build_tys_len Weaken_WF_Type_app_TList build_context'_Empty_1 build_context'_Empty_2
    build_context'_Empty_3 Ty_trans_eq_N_Trans
    Lem_2_11 build_fresh_distinct build_fresh_id Ty_trans_fresh_vars build_fresh_new build_fresh_new' 
    build_fresh_new'' build_fresh_new''' build_fresh_new''''' WF_mtype_U_map'_id 
    WF_mtype_Us_map'_id mtype_build_tys'_id exists_TE_Free_Vars id.

  Lemma WF_class_ext_TE_trans (gamma delta : Context) (c : nat) (ce : cld_ext) 
    (te te' : ty_ext) (_ : ce_build_cte ce te') (_ : L_WF_Ext gamma ce c)
    (wf_c : wf_class_ext delta ce te) : 
    te = TE_trans te' (Extract_TyVar _ _ (fst (ce))) (fst (te)) .
    eapply GJ_WF_class_ext_TE_trans.
    apply GJ_Ty_trans_invert.
    apply te_eq.
    unfold wf_class_ext in wf_c; unfold wf_class_ext' in wf_c.
    unfold id; apply wf_c.
    unfold id; apply H0.
    apply H.
  Qed.

  Definition Build_S0'' :=
    Generic.Build_S0'' _ _ _ _ _ (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) id _ 
    Empty subtype WF_Type _ _ Update _ FJ_cld_ext _ _ wf_class_ext
    m_call_ext E_WF WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext TE_Free_Vars TE_trans ce_build_cte 
    Meth_build_context Meth_WF_Ext L_WF_Ext L_build_context FJ_ty_ext id mtype_build_mtye
    id build_cte_Free_Vars WF_class_ext_TE_trans map_mbody mtype_build_tys
    Build_S0'''.
  
  Definition Term_subst_pres_typ_P := 
    cFJ.Term_subst_pres_typ_P _ _ _ _ subtype E_WF Update trans.

  Fixpoint Weaken_subtype_Update_list delta S T sub_S_T :=
    match sub_S_T in (subtype delta S T) return 
      (Weaken_subtype_Update_list_P _ _ subtype _ Update delta S T sub_S_T) with
      | Base_sub gamma' S' T' sub_S_T' =>
        FJ_Weaken_subtype_Update_list _ _ _ _ _ _ _ subtype _ _ _ Update _ _ _ CT
        build_te Base_sub Weaken_subtype_Update_list _ _ _ sub_S_T'
      | GJ_sub gamma' S' T' sub_S_T' => 
        GJ_Weaken_subtype_Update_list
        _ _ _ _ _ _ TLookup subtype GJ_sub _ Update TLookup_Update _ _ _ sub_S_T'
    end.

  Definition Weaken_WF_Update_list :=
    WF_Type_rect' (Weaken_WF_Update_list_P _ _ WF_Type _ Update)
    (Weaken_WF_Update_list_Q _ _ _ _ Update _ wf_class_ext)
    (Weaken_WF_Update_list_P1 _ _ WF_Type _ Update)
    (Weaken_WF_Update_list_ext_H1 _ _ _ _ _ subtype Ty_trans WF_Type _ Update
      _ _ Weaken_subtype_Update_list)
    (Weaken_WF_Update_list_ext_H2 _ _ _ _ _)
    (Weaken_WF_Update_list_ext_H3 _ _ _ _ _)
    (GJ_Weaken_WF_Update_list _ _ Gty _ _ TLookup _ GJ_WF_Type _ Update TLookup_Update)
    (FJ_Weaken_WF_Update_list_H1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CT _ _ Base_WF_Type
      (GJ_Weaken_WF_Update_list_obj_ext _ _ _ Update _))
    (FJ_Weaken_WF_Update_list_H2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Base_WF_Type).

  Definition WF_mtype_ext_update_list_id' := Generic.WF_mtype_ext_update_list_id' _ _ N N_Wrap _ 
    subtype Ty_trans WF_Type _ Update Weaken_subtype_Update_list
    Weaken_WF_Update_list _ _ _ 
    (fun delta mce mtye vars => FJ_WF_mtype_ext_update_list_id _ _ _ Update delta vars mce mtye).

  Definition WF_mtype_ext_Weaken_update_list gamma vars mce mtye := 
    WF_mtype_ext_update_list_id' gamma mce mtye vars.

  Fixpoint Term_subst_pres_typ gamma e T (WF_e : E_WF gamma e T) :
    Term_subst_pres_typ_P gamma e T WF_e :=
    match WF_e with 
      | FJ_E_WF gamma e ty FJ_case => FJ_Term_subst_pres_typ _ _ _ _ _ _ 
        _ _ _ Base_E mty_ext _ _ CT _ subtype build_te
        Base_sub WF_Type fields mtype 
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
    build_te_id' _ _ N Ty_trans _ _ FJ_mbody_build_te FJ_build_te FJ_build_te_id.
  
  Lemma mtype_invert : forall (gamma : Context) (m0 : nat) (te : ty_ext) 
    (c : nat) (mty : Mty Ty mty_ext),
    mtype gamma m0 (Base_Ty (ty_def nat ty_ext te (cl nat c))) mty ->
    cFJ.FJ_mtype nat nat nat nat ty_ext Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) E mty_ext
    md_ext cld_ext CT Context mtype mtype_build_te mtype_build_tys
    mtype_build_mtye gamma m0
    (Base_Ty (ty_def nat ty_ext te (cl nat c))) mty.
    intros; inversion H; subst; try assumption.
  Qed.
  
  Definition WF_mtype_Us_map_len' := WF_mtype_Us_map_len' _ _ N _ Ty_trans _ _ 
    _ (FJ_WF_mtype_Us_map_len _ Context).
  
  Definition methods_build_te_id' := methods_build_te_id' _ _ _ N Ty_trans _ _ _ FJ_methods_build_te_id.
    
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
                          ((this _, Base_Ty (ty_def _ ty_ext te' (cl _ c)))
                           :: map
                                (fun Tx : cFJ.VD _ Ty =>
                                 match Tx with
                                 | vd ty x => (var _ x, ty)
                                 end) vds)) gamma ->
                     WF_Type delta (Base_Ty (ty_def _ ty_ext te (cl _ c))) ->
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
                       (Base_Ty (ty_def _ ty_ext te'' (cl _ c)) :: Ds') (@pair _ _) =
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
    Context subtype build_te Base_sub _ _ WF_Type Base_WF_Type fields mtype mtype_build_te
    mtype_build_tys mtype_build_mtye mbody_build_te
    mb_ext build_mb_ext map_mbody
    E_WF Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty Update
    ce_build_cte Meth_build_context Meth_WF_Ext
    override L_WF_Ext L_build_context WF_CT Base_inject 
    Build_S0''  WF_mb_ext WF_Build_mb_ext WF_mtype_Us_map_len' mtype_build_tys_len' methods_build_te_id' WF_Type_par
    build_te_id' mtype_invert 
    (WF_mtype_ty_0_map_cl_id'' _ _ _ _ _ _ _ Bound N_Bound'_invert) 
    (WF_mtype_ty_0_map_tot' _ _ _ _ _ _ _ Bound FJ_Bound) WF_Type_invert.
  
  Lemma FJ_E_WF_invert : forall gamma (e : FJ_E _ _ _ _ _ _ _ ) c0, 
    E_WF gamma (Base_E e) c0 -> cFJ.FJ_E_WF _ _ _ _ _ Ty (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id)
    _ _ Base_E mty_ext
    Context subtype WF_Type fields mtype
    E_WF lookup Bound Bound WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty gamma (Base_E e) c0.
    intros; inversion H; subst; try assumption.
  Qed.
  
  Definition preservation_def := cFJ.preservation Ty E Context subtype E_WF Reduce.
  
  Definition Reduce_List_preservation es es' (red_es : Congruence_List_Reduce es es') :=
    cFJ.Reduce_List_preservation _ _ _ subtype E_WF Congruence_List_Reduce es es' red_es.
        
  Definition WF_fields_map_sub' := 
    WF_fields_map_sub' _ _ _ _ _ _ _ Empty subtype _ fields _ _ _ Bound _ _ CT build_te
    Base_sub N_Wrap_inject N_Bound'_invert (fun n n' H => H) fields_id.
    
    Variable (WFounded_subtyping : forall gamma S T, subtype gamma S T -> subtype gamma T S -> T = S).

    Lemma FJ_E_WF_new_invert : forall gamma e T T0, 
      E_WF gamma (Base_E (cFJ.new nat nat nat nat ty_ext E m_call_ext T e)) T0 ->
      Base_Ty T = T0.
      intros; inversion H; subst.
      inversion H0; subst.
      destruct te; reflexivity.
    Qed.

  Fixpoint preservation e e' (red_e : Reduce e e') : preservation_def _ _ red_e :=
    match red_e with 
      |  FJ_S_Reduce t t' red_t => FJ_pres _ _ _ _ _ _ _ _ _ 
        Base_E _ _ _ CT _ subtype build_te Base_sub WF_Type fields
        mtype mbody_build_te mb_ext build_mb_ext
        map_mbody E_WF lookup
        Bound Bound WF_mtype_Us_map WF_mtype_U_map
        WF_mtype_ext Empty FJ_E_WF Update trans
        Reduce FJ_S_Reduce FJ_E_WF_invert EWrap_inject
        Fields_eq fds_distinct WF_fields_map_id 
        (fun g tye c ty' Bnd => WF_fields_map_id' g _ _ Bnd tye c (refl_equal _))
        WF_fields_map_sub' Subtype_Weaken WF_mtype_map_sub Term_subst_pres_typ WF_mb_ext Lem_2_12
        t t' red_t
      | FJ_C_Reduce e e' fj_red_e' => FJ_C_preservation _ _ _ _ ty_ext _ _ _ _ Base_E _ _ _ CT
        _ subtype build_te Base_sub WF_Type fields mtype E_WF lookup Bound
        Bound WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF 
        Reduce Congruence_List_Reduce FJ_C_Reduce FJ_E_WF_invert EWrap_inject
        Lem_2_8' Lem_2_9 WF_mtype_ty_0_map_total e e' fj_red_e'
        preservation (fix preservation_list (es es' : list E) (red_es : Congruence_List_Reduce es es') : 
          Reduce_List_preservation _ _ red_es :=
          match red_es return Reduce_List_preservation _ _ red_es with
            FJ_Reduce_List es es' red_es' => FJ_C_List_preservation _ _ _ _ _ _ _ _ _ _ 
            CT _ subtype build_te Base_sub E_WF Reduce
            Congruence_List_Reduce FJ_Reduce_List es es' red_es' preservation preservation_list end)      
    end.

  Inductive subexpression : E -> E -> Prop :=
   | FJ_subexpression_Wrap : forall e e', FJ_subexpression _ _ _ _ _ _ _ Base_E subexpression subexpression_list e e' -> subexpression e e'
  with subexpression_list : E -> list E -> Prop :=
    subexpression_list_Wrap : forall e es, FJ_subexpression_list _ subexpression subexpression_list e es ->
      subexpression_list e es.

  Definition progress_1_P := cFJ.progress_1_P _ _ _ _ _ _ Base_Ty _ _ Base_E _ fields
    E_WF Empty subexpression.
  
  Definition progress_1_list_P := cFJ.progress_1_list_P _ _ _ _ _ _ Base_Ty _ _ Base_E 
    _ fields E_WF Empty subexpression_list.
  
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
  
  Fixpoint progress_1 gamma e T (WF_e : E_WF gamma e T) :
    progress_1_P gamma e T WF_e :=
    match WF_e with 
      | FJ_E_WF gamma e ty FJ_case => cFJ.progress_1 _ _ _ _ _ _ _ _ _ Base_E _ _ subtype
        WF_Type fields mtype E_WF lookup Bound Bound WF_mtype_Us_map
        WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert EWrap_inject
        WF_fields_map_id (fun g tye c ty' Bnd => WF_fields_map_id' g _ _ Bnd tye c (refl_equal _))
        subexpression subexpression_list 
        subexp_invert subexpression_list_nil subexpression_list_destruct gamma e ty FJ_case progress_1
    end.
  
  Definition progress_2_P := cFJ.progress_2_P _ _ _ _ _ _ 
    (Generic.FJ_Ty_Wrap Ty ty_ext nat N Base_Ty id) _ _ Base_E _ _ CT _ 
    mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty subexpression.
  
  Definition progress_2_list_P := cFJ.progress_2_list_P _ _ _ _ _ _ Base_Ty _ _ Base_E _ _ 
    CT _ mbody_build_te mb_ext build_mb_ext map_mbody E_WF Empty 
    subexpression_list.
  
  Definition WF_mtype_ty_0_map_Empty_refl := FJ_WF_mtype_ty_0_map_Empty_refl _ _ _ Base_Ty Context.
  
  Definition mtype_mbody_build_te := mtype_mbody_build_te _ _ _ N Ty_trans FJ_cld_ext 
    FJ_mtype_build_te _ FJ_mtype_mbody_build_te.

  Definition build_mb_ext_tot := Generic.build_mb_ext_tot _ _ Gty N Ty_trans _ build_fresh _ _ _ _ _ 
    FJ_build_mb_ext (FJ_mtype_build_tys _ _) (FJ_build_mb_ext_tot nat Ty).

  Definition mbody_m_call_map_tot := GJ_mbody_m_call_map_tot _ _ N Ty_trans FJ_m_call_ext.
    
  Definition mbody_new_map_tot := GJ_mbody_new_map_tot _ _ N Ty_trans FJ_ty_ext.

  Fixpoint E_Ty_trans_tot (e : E) :=
    match e return E_Ty_Trans_tot_P _ _ _ _ E_Ty_Trans e with
      | Base_E e' => FJ_E_Ty_Trans_tot _ _ _ _ _ _ _ _ _ _ Base_E mbody_m_call_map mbody_new_map
        E_Ty_Trans Base_E_Ty_Trans mbody_m_call_map_tot mbody_new_map_tot E_Ty_trans_tot e'
    end.

  Definition map_mbody_tot := Generic.map_mbody_tot _ _ Gty _ Ty_trans _ build_fresh _ _ FJ_m_call_ext
    _ _ _ (FJ_mtype_build_tys nat Ty) E_Ty_trans_tot.
    
  Fixpoint mtype_implies_mbody gamma m ty mty (mtype_m : mtype gamma m ty mty) :=
    match mtype_m with 
      FJ_mtype gamma' m' ty' mty' fj_mtype_m => FJ_mtype_implies_mbody _ _ _ _ _ _ _
      _ _ _ _ _ CT _ mtype mtype_build_te mtype_build_tys mtype_build_mtye
      FJ_mtype mbody_build_te mb_ext build_mb_ext map_mbody
      Empty Base_inject mtype_build_tys_len' map_mbody_tot
      mtype_mbody_build_te build_mb_ext_tot gamma' m' ty' mty' fj_mtype_m mtype_implies_mbody
    end.
    
  Fixpoint progress_2 gamma e T (WF_e : E_WF gamma e T) :
    progress_2_P gamma e T WF_e :=
    match WF_e with 
      | FJ_E_WF gamma e ty FJ_case => FJ_progress_2 _ _ _ _ _ _ _ _ _ Base_E 
        _ _ _ CT _ subtype WF_Type fields mtype mbody_build_te mb_ext
        build_mb_ext map_mbody E_WF lookup Bound Bound
        WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty FJ_E_WF FJ_E_WF_invert
        EWrap_inject WF_mtype_Us_map_len' subexpression subexpression_list
        subexp_invert subexpression_list_nil subexpression_list_destruct
        (WF_mtype_ty_0_map_Empty_refl' _ _ _ _ _ _ _ Bound N_Bound'_invert) 
        mtype_implies_mbody gamma e ty FJ_case progress_2
  end.

End WF_Proofs.

