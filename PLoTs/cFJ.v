Section FJ_definitions.

  Require Import Arith.
  Require Import List.
  Require Import FJ_tactics.

  Variable (C : Set). (** Class Identifiers **)
  Variable (F : Set). (** Field Identifiers **)
  Variable (M : Set). (** Method Identifiers **)
  Variable (X : Set). (** Variable Identifiers **)

  Inductive CL := cl : C -> CL | Object : CL.

  Variable (ty_ext : Set).
  Definition FJ_ty_ext := unit.

  Inductive FJ_Ty : Set :=
    ty_def : ty_ext -> CL -> FJ_Ty.

  Variables (Ty : Set)
    (TyWrap : FJ_Ty -> Ty).

  Coercion TyWrap : FJ_Ty >-> Ty.

  Section Ty_Rect.
    Variable (P : Ty -> Prop).
    
    Hypothesis (H1 : forall tye cl, P (ty_def tye cl)).
  
  End Ty_Rect.

  Section Ty_Map.
    Variable (map_ty_ext : ty_ext -> ty_ext -> Prop).
    Definition FJ_map_ty_ext (x y : FJ_ty_ext) : Prop := True.
    
    Inductive ty_map : Ty -> Ty -> Prop :=
      Base_map : forall cl tye tye', map_ty_ext tye tye' -> ty_map (ty_def tye cl) (ty_def tye' cl).

    Definition ty_pass (f_ty_ext : ty_ext -> ty_ext) (ty : FJ_Ty) : FJ_Ty :=
      match ty with 
        ty_def te cl' => ty_def (f_ty_ext te) cl'
      end.

  End Ty_Map.

  Inductive FD := fd : Ty -> F -> FD. (* Function Definition *)
  Inductive VD := vd : Ty -> X -> VD. (* Variable Definition *)

  Inductive K := k : C -> list FD -> K. (* Class Constructor *) 

  Inductive Var := var : X -> Var | this : Var. (* Variable Expression *)

  Variable E : Set. (* Expression *)

  Definition Es := list E.

  Variables (m_call_ext : Set).

  Definition FJ_m_call_ext := unit.

  Inductive FJ_E : Set := 
    e_var : Var -> FJ_E 
  | fd_access : E -> F -> FJ_E
  | m_call : m_call_ext -> E -> M -> Es -> FJ_E
  | new : FJ_Ty -> Es -> FJ_E.

  Variable EWrap : FJ_E -> E.
  Coercion EWrap : FJ_E >-> E.
  Variable EWrap_inj : forall a b, EWrap a = EWrap b -> a = b.

  Definition FJ_Es := list FJ_E.

  Fixpoint EsWrap (es : FJ_Es) : Es :=
    match es with 
      | (e :: es') => EWrap e :: EsWrap es'
      | _ => nil
    end.

  Coercion EsWrap : FJ_Es >-> Es.

  Section E_recursion.

    Section E_rec.
      Variables
        (P : E -> Set)
        (Q : Es -> Set).
      
      Hypotheses
        (H1 : forall var, P (e_var var))
        (H2 : forall e f, P e -> P (fd_access e f))
        (H3 : forall me e m l, P e -> Q l -> P (m_call me e m l))
        (H4 : forall cl' l , Q l -> P (new cl' l))
        (H6 : Q nil)
        (H7 : forall e l, P e -> Q l -> Q (e :: l)).
      
      Fixpoint e_rec (e : FJ_E) (rect : forall e, P e) (rects : forall l, Q l) : P e :=
        match e return (P e) with
          e_var v => H1 v
          | fd_access e f => H2 e f (rect e) 
          | m_call me e m l => H3 me e m l (rect e) ((fix es_rect (es : Es) : Q es :=
            match es return Q es with
              nil => H6
              | e :: l => H7 e l (rect e) (rects l)
            end) l)
          | new cl' l => H4 cl' l ((fix es_rect (es : Es) : Q es :=
            match es return Q es with
              nil => H6
              | e :: l => H7 e l (rect e) (rects l)
            end) l)
        end.
    End E_rec.

    Section E_rect.

      Variables
        (P : E -> Type)
        (Q : Es -> Type).
      
      Hypotheses
        (H1 : forall var, P (e_var var))
        (H2 : forall e f, P e -> P (fd_access e f))
        (H3 : forall mce e m l, P e -> Q l -> P (m_call mce e m l))
        (H4 : forall cl' l, Q l -> P (new cl' l))
        (H6 : Q nil)
        (H7 : forall e l, P e -> Q l -> Q (e :: l)).
      
      Definition e_rect (e : FJ_E) (rect : forall e, P e) : P e :=
        match e return (P e) with
          e_var v => H1 v
          | fd_access e f => H2 e f (rect e) 
          | m_call me e m l => H3 me e m l (rect e) ((fix es_rect (es : Es) : Q es :=
            match es return Q es with
              nil => H6
              | e :: l => H7 e l (rect e) (es_rect l)
            end) l)
          | new cl' l => H4 cl' l ((fix es_rect (es : Es) : Q es :=
            match es return Q es with
              nil => H6
              | e :: l => H7 e l (rect e) (es_rect l)
            end) l)
        end.
    End E_rect.
  End E_recursion.
  
  Section Map_E.

    Variables (map_m_call_ext : m_call_ext -> m_call_ext -> Prop)
      (map_new_ext : ty_ext -> ty_ext -> Prop)
      (map_e_ext' : (m_call_ext -> m_call_ext -> Prop) -> (ty_ext -> ty_ext -> Prop) -> E -> E -> Prop).

    Definition FJ_map_m_call_ext (x y : FJ_m_call_ext) := True.
    Definition FJ_map_new_ext (x y : FJ_ty_ext) := True. 

    Inductive FJ_map_e_ext' : (FJ_m_call_ext -> FJ_m_call_ext -> Prop) -> 
      (FJ_ty_ext -> FJ_ty_ext -> Prop) -> E -> E -> Prop := 
      fj_map_e_ext : forall e map_mc map_ne, FJ_map_e_ext' map_mc map_ne e e.

    Definition map_e_ext'' e e' := map_e_ext' map_m_call_ext map_new_ext e e'.

    Inductive map_e_ext : E -> E -> Prop :=
      map_e_var : forall v, map_e_ext (e_var v) (e_var v)
    | map_fd_access : forall e e' f, map_e_ext'' e e' -> map_e_ext (fd_access e f) (fd_access e' f)
    | map_m_call : forall e e' m es es' mce mce', map_e_ext'' e e' -> 
      List_P2' map_e_ext'' es es' -> 
      map_m_call_ext mce mce' -> map_e_ext (m_call mce e m es) (m_call mce' e' m es')
    | map_new : forall te te' cl es es', List_P2' map_e_ext'' es es' -> map_new_ext te te' ->
      map_e_ext (new (ty_def te cl) es) (new (ty_def te' cl) es').

  End Map_E.

  Variables (mty_ext : Set)
    (md_ext : Set).

  Definition FJ_mty_ext := unit.
  Definition FJ_md_ext := unit.

  Inductive Mty := mty : mty_ext -> list Ty -> Ty -> Mty.

  Inductive MD : Set :=
    md : md_ext -> Ty -> M -> list VD -> E -> MD.

  Variable cld_ext : Set.
  Definition FJ_cld_ext := unit.

  Inductive L : Set :=
    cld : cld_ext -> C -> FJ_Ty -> list FD -> K -> list MD -> L.

  Definition cld_ce (cld' : L) : cld_ext :=
    match cld' with
      cld ce _ _ _ _ _ => ce
    end.

  Variable CT : C -> option L.
  Variable CT_self : forall ce c c1 cl' l k fds, CT c = Some (cld ce c1 cl' l k fds) -> c = c1.

  Variable Context : Set.
  Variable subtype : Context -> Ty -> Ty -> Prop.
  Variable (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop).

  Definition FJ_build_te : FJ_cld_ext -> FJ_ty_ext -> FJ_ty_ext -> FJ_ty_ext -> Prop := id_map_2.

  Inductive FJ_subtype : Context -> Ty -> Ty -> Prop :=
    sub_refl : forall (ty : Ty) (gamma : Context), FJ_subtype gamma ty ty
  | sub_trans : forall (c d e : Ty) (gamma : Context), subtype gamma c d -> subtype gamma d e -> FJ_subtype gamma c e
  | sub_dir : forall ce c d fs k' ms te te' te'' (gamma : Context), CT c = Some (cld ce c (ty_def te'' d) fs k' ms) -> 
    build_te ce te te'' te' -> FJ_subtype gamma (ty_def te (cl c)) (ty_def te' d).

  Variable subtype_Wrap : forall {gamma : Context} {ty ty' : Ty}, FJ_subtype gamma ty ty' -> subtype gamma ty ty'.
  Coercion subtype_Wrap : FJ_subtype >-> subtype.

  Section subtype_recursion.

    Variable (P : forall (gamma : Context) (ty ty' : Ty), subtype gamma ty ty' -> Prop).
    
    Hypothesis (H1 : forall (ty : Ty) (gamma : Context), P _ _ _ (sub_refl ty gamma))
      (H2 : forall c d e gamma sub_c sub_d, P _ _ _ sub_c -> P _ _ _ sub_d -> 
        P _ _ _ (sub_trans c d e gamma sub_c sub_d))
      (H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
        P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te)).

    Definition FJ_subtype_rect gamma ty ty' (sub_ty : FJ_subtype gamma ty ty') 
      (subtype_rect' : forall gamma ty ty' (sub_ty : subtype gamma ty ty'), P _ _ _ sub_ty) : P _ _ _ sub_ty :=
      match sub_ty return P _ _ _ sub_ty with 
        | sub_refl ty gamma => H1 ty gamma
        | sub_trans c d e gamma sub_c sub_d => H2 c d e gamma sub_c sub_d 
          (subtype_rect' _ _ _ sub_c) (subtype_rect' _ _ _ sub_d)
        | sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te => H3 ce c d fs k' ms te te' te'' gamma CT_c bld_te
      end.
  
  End subtype_recursion.

  Hint Resolve sub_refl.

  Variable (wf_class_ext : Context -> cld_ext -> ty_ext -> Prop)
    (wf_object_ext : Context -> ty_ext -> Prop).

  Definition FJ_wf_class_ext : Context -> FJ_cld_ext -> FJ_ty_ext -> Prop := fun c l tye => True.
  Definition FJ_wf_object_ext : Context -> FJ_ty_ext -> Prop := fun c tye => True.

  Inductive FJ_WF_Type : Context -> Ty -> Prop :=
    WF_Obj : forall gamma te, wf_object_ext gamma te -> FJ_WF_Type gamma (ty_def te Object)
  | WF_Class : forall gamma c cld te, CT c = Some cld -> 
    wf_class_ext gamma (cld_ce cld) te -> FJ_WF_Type gamma (ty_def te (cl c)).

  Variables (WF_Type : Context -> Ty -> Prop)
    (FJ_WF_Type_Wrap : forall {gamma : Context} {ty : Ty}, FJ_WF_Type gamma ty -> WF_Type gamma ty).

  Coercion FJ_WF_Type_Wrap : FJ_WF_Type >-> WF_Type.

  Section WF_Type_recursion.

    Variable (P : forall gamma ty, WF_Type gamma ty -> Prop)
      (Q : forall gamma ce te, wf_class_ext gamma ce te -> Prop).
    
    Hypothesis (H1 : forall gamma te wf_obj, P _ _ (WF_Obj gamma te wf_obj))
      (H2 : forall gamma c cld te CT_c wf_cld_ext, Q _ _ _ wf_cld_ext -> P _ _ (WF_Class gamma c cld te CT_c wf_cld_ext))
      (H3 : forall gamma cld te (wf_cld : wf_class_ext gamma cld te), Q _ _ _ wf_cld).

    Definition FJ_WF_Type_rect' gamma ty (WF_ty : FJ_WF_Type gamma ty) : P _ _ WF_ty :=
      match WF_ty return P _ _ WF_ty with 
        WF_Obj gamma te wf_obj => H1 gamma te wf_obj
        | WF_Class gamma c cld' te CT_c wf_cld_ext => 
          H2 gamma c cld' te CT_c wf_cld_ext (H3 _ _ _ wf_cld_ext)
      end.

  End WF_Type_recursion.

  Fixpoint Unzip_Fields (fds : list FD) : (list Ty) * (list F) :=
    match fds with 
      fd ty f :: fds' => (ty :: fst (Unzip_Fields fds'), f :: snd (Unzip_Fields fds'))
      | _ => (nil, nil)
    end.

  Fixpoint Zip_Fields (tys : list Ty) (fs : list F) : list FD :=
    match tys, fs with
      ty :: tys', f :: fs' => fd ty f :: Zip_Fields tys' fs'
      | _, _ => nil
    end.

  Variable fields : Context -> Ty -> list FD -> Prop.
  Variable (fields_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (fields_build_tys : ty_ext -> cld_ext -> list Ty -> list Ty -> Prop).

  Definition FJ_fields_build_te : FJ_cld_ext -> FJ_ty_ext -> FJ_ty_ext -> FJ_ty_ext -> Prop := 
    fun ce tye tye' tye'' => True.

  Definition FJ_fields_build_tys : FJ_ty_ext -> FJ_cld_ext -> list Ty -> list Ty -> Prop := id_map_2.

  Inductive FJ_fields : Context -> Ty -> list FD -> Prop :=
    fields_Obj : forall te gamma, FJ_fields gamma (ty_def te Object) nil 
  | fields_cl :  forall gamma ce c d c_fds d_fds k' mds te te' te'' tys, CT c = Some (cld ce c (ty_def te'' d) c_fds k' mds) -> 
    fields_build_te ce te te'' te' -> (*** Update Type extension in parent field lookup ***)
    fields gamma (ty_def te' d) d_fds -> (*** Get parent fields***)
    fields_build_tys te ce (fst (Unzip_Fields c_fds)) tys -> (*** Modify own type extensions ***)
    FJ_fields gamma (ty_def te (cl c)) (d_fds ++ (Zip_Fields tys (snd (Unzip_Fields c_fds)))).

  Variable fields_Wrap : forall {gamma ty fds}, FJ_fields gamma ty fds -> fields gamma ty fds.
  Coercion fields_Wrap : FJ_fields >-> fields.

  Section FJ_Fields_recursion.
    
    Variable (P : forall gamma ty fds, fields gamma ty fds -> Prop).
    
    Hypothesis (H1 : forall te gamma, P _ _ _ (fields_Obj te gamma))
      (H2 : forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
        P _ _ _ par_fds -> 
        P _ _ _ (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys)).
    
    Definition FJ_fields_rect' gamma ty fds (ty_fds : FJ_fields gamma ty fds) 
      (fields_rect'' : forall gamma ty fds (ty_fds : fields gamma ty fds), P _ _ _ ty_fds) : P _ _ _ ty_fds :=
      match ty_fds return P _ _ _ ty_fds with 
        fields_Obj te gamma => H1 te gamma
        | fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys =>
          H2 gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys (fields_rect'' _ _ _ par_fds)
      end.

  End FJ_Fields_recursion.

  Variables (mtype : Context -> M -> Ty -> Mty -> Prop)
    (mtype_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (mtype_build_tys : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> list Ty -> list Ty -> Prop)
    (mtype_build_mtye : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> mty_ext -> Prop).

  Definition FJ_mtype_build_te : FJ_cld_ext -> FJ_ty_ext -> FJ_ty_ext -> FJ_ty_ext -> Prop := id_map_2.

  Definition FJ_mtype_build_tys : FJ_cld_ext -> FJ_ty_ext -> Ty -> list VD -> FJ_md_ext ->
    list Ty -> list Ty -> Prop := id_map_5.
  
  Definition FJ_mtype_build_mtye : FJ_cld_ext -> FJ_ty_ext -> Ty -> list VD -> FJ_md_ext ->
    FJ_mty_ext -> Prop := fun ce tye mde ty vds mtye => True.

  Inductive FJ_mtype : Context -> M -> Ty -> Mty -> Prop :=
  | mtype_fnd : forall ce m c d fds k' mds ty ty' vds e me te gamma tys' mtye, 
    CT c = Some (cld ce c d fds k' mds) -> 
    In (md me ty m vds e) mds -> (*** Found the method ***)
(*** Modify type extensions on parameter types ***)
    mtype_build_tys ce te ty vds me (map (fun vd' => match vd' with vd ty _ => ty end) vds) tys' -> 
(*** Modify type extensions on return type ***)
    mtype_build_tys ce te ty vds me (ty :: nil) (ty' :: nil) -> 
(*** Build method type extension ***)
    mtype_build_mtye ce te ty vds me mtye -> 
    FJ_mtype gamma m (ty_def te (cl c)) (mty mtye tys' ty')
  | mtype_not_fnd : forall ce m c d fds k' mds mty' te te' te'' gamma, 
    CT c = Some (cld ce c (ty_def te'' d) fds k' mds) -> (forall me' b vds e, ~ In (md me' b m vds e) mds) ->
    mtype_build_te ce te te'' te' -> (*** Update type extension in parent method lookup ***)
    mtype gamma m (ty_def te' d) mty' -> (*** Lookup parent method ***)
    FJ_mtype gamma m (ty_def te (cl c)) mty'.

  Variable (FJ_mtype_Wrap : forall {gamma m ty mty}, FJ_mtype gamma m ty mty ->
    mtype gamma m ty mty).
  Coercion FJ_mtype_Wrap : FJ_mtype >-> mtype.

  Section mtype_recursion.
    
    Variable (P : forall gamma m ty mty, mtype gamma m ty mty -> Prop).

    Hypothesis (H1 : forall ce m c d fds k' mds ty ty' vds e me te gamma tys' mtye
      CT_c In_m build_tys build_ty build_mtye, P _ _ _ _ (mtype_fnd ce m c d fds k' mds ty ty' 
        vds e me te gamma tys' mtye CT_c In_m build_tys build_ty build_mtye))
    (H2 : forall ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype,
      P _ _ _ _ par_mtype -> 
      P _ _ _ _ (mtype_not_fnd ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype)).
    
    Definition mtype_rect' gamma m ty mty (mtype_m : FJ_mtype gamma m ty mty)  
      (mtype_rect : forall gamma m ty mty mtype_m, P gamma m ty mty mtype_m) : P _ _ _ _ mtype_m :=
      match mtype_m return P _ _ _ _ mtype_m with
        mtype_fnd ce m c d fds k' mds ty ty' vds e me te gamma tys' mtye
        CT_c In_m build_tys build_ty build_mtye => H1 ce m c d fds k' mds ty ty' 
        vds e me te gamma tys' mtye CT_c In_m build_tys build_ty build_mtye
        | mtype_not_fnd ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype =>
          H2 ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype 
          (mtype_rect _ _ _ _ par_mtype)
      end.

  End mtype_recursion.

  Variable mbody_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop.

  Definition FJ_mbody_build_te : FJ_cld_ext -> FJ_ty_ext -> FJ_ty_ext -> FJ_ty_ext -> Prop :=
    id_map_2.

  Definition FJ_mbody_m_call_map : FJ_cld_ext -> FJ_ty_ext -> FJ_m_call_ext -> FJ_md_ext -> FJ_m_call_ext -> FJ_m_call_ext -> Prop := id_map_4.
  
  Definition FJ_mbody_new_map : FJ_cld_ext -> FJ_ty_ext -> FJ_m_call_ext -> FJ_md_ext -> FJ_ty_ext -> FJ_ty_ext -> Prop := id_map_4.

  Variable mb_ext : Set.
  Definition FJ_mb_ext := unit.

  Inductive MB : Set := mb : mb_ext -> list X -> E -> MB.

  Variable build_mb_ext : cld_ext -> ty_ext -> m_call_ext -> md_ext -> mb_ext -> Prop.
  Definition FJ_build_mb_ext (ce : FJ_cld_ext)  (te : FJ_ty_ext) (mce : FJ_m_call_ext) 
    (me : FJ_md_ext) (mbe : FJ_mb_ext) := True.

  Variable map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop.
  Definition FJ_map_mbody : FJ_cld_ext -> FJ_ty_ext -> FJ_m_call_ext -> FJ_md_ext -> E -> E -> Prop := id_map_4.

  Inductive mbody : Context -> m_call_ext -> M -> Ty -> MB -> Prop :=
  | mbody_fnd : forall ce m c d fds k' mds ty vds e e' me te gamma mce mbe, 
    CT c = Some (cld ce c d fds k' mds) -> 
    In (md me ty m vds e) mds -> (*** Found the method ***)
    map_mbody ce te mce me e e' -> (*** Modify the returned expressions ***)
    build_mb_ext ce te mce me mbe ->
    mbody gamma mce m (ty_def te (cl c)) (mb mbe (map (fun vd' => match vd' with vd _ x => x end) vds) e')
  | mbody_not_fnd : forall ce m c d fds k' mds mb' te te' te'' gamma mce, 
    CT c = Some (cld ce c (ty_def te'' d) fds k' mds) -> (forall me b vds e, ~ In (md me b m vds e) mds) ->
    mbody_build_te ce te te'' te' -> (*** Update type extension in parent method lookup ***)
    mbody gamma mce m (ty_def te' d) mb' -> (*** Lookup parent method ***)
    mbody gamma mce m (ty_def te (cl c)) mb'.

  Variables (E_WF : Context -> E -> Ty -> Prop)
    (Es_WF : Context -> Es -> Ty -> Prop)
    (lookup : Context -> Var -> Ty -> Prop)
    (WF_fields_map : Context -> Ty -> Ty -> Prop) 
    (WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_ext -> Prop).

  Definition FJ_WF_fields_map : Context -> Ty -> Ty -> Prop := id_map_1.
  Definition FJ_WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop := id_map_1.
  Definition FJ_WF_mtype_Us_map : Context -> FJ_m_call_ext -> FJ_mty_ext -> list Ty -> list Ty -> Prop :=
    id_map_3.
  Definition FJ_WF_mtype_U_map : Context -> FJ_m_call_ext -> FJ_mty_ext -> Ty -> Ty -> Prop := id_map_3.
  Definition FJ_WF_mtype_ext : Context -> FJ_m_call_ext -> FJ_mty_ext -> Prop :=
    fun gamma mce mtye => True.

  Variable Empty : Context.

  Inductive FJ_E_WF (gamma : Context) : E -> Ty -> Prop :=
  | T_Var : forall x ty, lookup gamma x ty -> FJ_E_WF gamma (e_var x) ty
  | T_Field : forall e f ty ty' fds ty'' i, E_WF gamma e ty -> 
    WF_fields_map gamma ty ty' -> (*** Update the Type appropriately ***)
    fields Empty ty' fds -> 
    nth_error fds i = Some (fd ty'' f) -> FJ_E_WF gamma (fd_access e f) ty''
  | T_Invk : forall e_0 ty_0 ty_0' U U' m mtye mce (Us Us' Ss : list Ty) es, 
    E_WF gamma e_0 ty_0 ->
    WF_mtype_ty_0_map gamma ty_0 ty_0' -> (*** Update lookup type appropriately ***)
    mtype Empty m ty_0' (mty mtye Us U) -> (*** Lookup type of the method ***)
    WF_mtype_Us_map gamma mce mtye Us Us' -> (*** Update method param types ***)
    WF_mtype_U_map gamma mce mtye U U' -> (*** Update method return type ***)
(*** Arg types need to be subtypes of declared params ***)
    List_P2' (E_WF gamma) es Ss -> List_P2' (subtype gamma) Ss Us' -> 
    WF_mtype_ext gamma mce mtye -> 
    FJ_E_WF gamma (m_call mce e_0 m es) U'
  | T_New : forall cl te  Ss fds es, 
    WF_Type gamma (ty_def te cl) -> (*** Type is well-formed ***)
    fields Empty (ty_def te cl) fds -> (*** Get the fields ***)
    List_P2' (E_WF gamma) es Ss ->
    List_P2' (fun S fd' => match fd' with fd T _ => subtype gamma S T end) Ss fds ->
    FJ_E_WF gamma (new (ty_def te cl) es) (ty_def te cl).

  Variable (E_WF_Wrap : forall {gamma e ty}, FJ_E_WF gamma e ty -> E_WF gamma e ty).

  Section FJ_E_WF_recursion.

    Variable (P : forall gamma e ty, E_WF gamma e ty -> Prop)
      (Q : forall gamma es tys, List_P2' (E_WF gamma) es tys -> Prop).

    Hypothesis (H1 : forall gamma x ty lookup_x, P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)))
      (H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, P _ _ _ WF_e ->
        P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)))
      (H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U 
        WF_es sub_Ss_Us' WF_mtye, P _ _ _ WF_e_0 -> Q _ _ _ WF_es -> P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
          mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)))
      (H4 : forall gamma cl te Ss fds es  WF_cl fds_cl WF_es sub_fds,
        Q _ _ _ WF_es -> P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds)))
      (H5 : forall gamma, Q gamma nil nil (nil_P2' (E_WF gamma)))
      (H6 : forall gamma e es ty tys WF_e WF_es,
        P gamma e ty WF_e -> Q gamma es tys WF_es -> Q _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es)).

    Definition FJ_FJ_E_WF_rect' gamma e ty (WF_e : FJ_E_WF gamma e ty)
      (E_WF_rect' : forall gamma e ty (WF_e : E_WF gamma e ty), P _ _ _ WF_e) : P _ _ _ (E_WF_Wrap _ _ _ WF_e) :=
      match WF_e return P _ _ _ (E_WF_Wrap _ _ _ WF_e) with 
        | T_Var x ty lookup_x => H1 gamma x ty lookup_x
        | T_Field e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds => 
          H2 gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds (E_WF_rect' _ _ _ WF_e)
        | T_Invk e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 ty_0_map mtype_m 
          map_Us map_U WF_es sub_Ss_Us' WF_mtye => H3 gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' 
          Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye (E_WF_rect' _ _ _ WF_e_0)
          ((fix es_rect gamma es tys (WF_es : List_P2' (E_WF gamma) es tys) : Q _ _ _ WF_es :=
            match WF_es return Q _ _ _ WF_es with
              | nil_P2' => H5 gamma
              | cons_P2' e ty es tys WF_e WF_es => H6 gamma e es ty tys WF_e WF_es
                (E_WF_rect' _ _ _ WF_e) (es_rect _ _ _ WF_es)
            end) _ _ _ WF_es)
        | T_New cl' te Ss fds es WF_cl fds_cl WF_es sub_fds => 
          H4 gamma cl' te Ss fds es WF_cl fds_cl WF_es sub_fds
          ((fix es_rect gamma es tys (WF_es : List_P2' (E_WF gamma) es tys) : Q _ _ _ WF_es :=
            match WF_es return Q _ _ _ WF_es with
              | nil_P2' => H5 gamma
              | cons_P2' e ty es tys WF_e WF_es => H6 gamma e es ty tys WF_e WF_es
                (E_WF_rect' _ _ _ WF_e) (es_rect _ _ _ WF_es)
            end) _ _ _ WF_es)
      end.

  End FJ_E_WF_recursion.

  Variables (update : Context -> Var -> Ty -> Context)
    (ce_build_cte : cld_ext -> ty_ext -> Prop)
    (Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop)
    (Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop)
    (override : Context -> M -> FJ_Ty -> md_ext -> list Ty -> Ty -> Prop).

  Definition FJ_ce_build_cte : FJ_cld_ext -> FJ_ty_ext -> Prop := fun ce tye => True.
  Definition FJ_Meth_build_context : FJ_cld_ext -> FJ_md_ext -> Context -> Context -> Prop := id_map_2.

  Definition FJ_Meth_WF_Ext : Context -> FJ_cld_ext -> FJ_md_ext -> Prop :=
    fun gamma ce mde => True.
  Definition FJ_override (gamma : Context) (m : M) (ty : FJ_Ty) 
    (mde' : FJ_md_ext) (Ts : list Ty) (T : Ty) : Prop := 
    forall mtye ds d_0, mtype Empty m ty (mty mtye ds d_0) -> 
      T = d_0 /\ Ts = ds.

  Fixpoint update_list (gamma : Context) (lkp_list : list (Var * Ty)) : Context :=
    match lkp_list with
      nil => gamma
      | (v, ty) :: lkp_list' => update (update_list gamma lkp_list') v ty
    end.

  Inductive Meth_WF : C -> MD -> Prop :=
    T_Md : forall gamma c c_0 d m vds e e_0 fds k mds te te' ce mde, 
      ce_build_cte ce te -> (*** Build the type extension for c ***)
      Meth_build_context ce mde (update_list Empty ((this, TyWrap (ty_def te (cl c))) :: (*** Build the typing environment ***)
        (map (fun v => match v with vd ty v => (var v, ty) end) vds))) gamma -> 
      WF_Type gamma c_0 -> (*** Return Type Well-formed ***)
      List_P1 (fun Tx => match Tx with vd ty _ => WF_Type gamma ty end) vds -> (*** Parameter Types Well-formed ***)
      E_WF gamma e e_0 -> (*** Well formed method body ***)
      subtype gamma e_0 c_0 -> (*** Return type is a subtype of the declared type ***)
      CT c = Some (cld ce c (ty_def te' d) fds k mds) -> 
      override gamma m (ty_def te' d) mde (*** Valid overide? ***)
      (map (fun vd' => match vd' with vd ty _ => ty end) vds) c_0 -> 
      Meth_WF_Ext gamma ce mde -> (*** Additional premises for extensions ***)
      Meth_WF c (md mde c_0 m vds e).

  Variables (L_WF_Ext : Context -> cld_ext -> C -> Prop)
    (L_build_context : cld_ext -> Context -> Prop).

  Definition FJ_L_WF_Ext : Context -> FJ_cld_ext -> C -> Prop := fun gamma ce c => True.
  Inductive FJ_L_build_context : FJ_cld_ext -> Context -> Prop :=
    fj_l_build_context : forall ce, FJ_L_build_context ce Empty.

  Inductive L_WF : L -> Prop :=
    T_cld : forall c d d_fds c_fds k' mds ce te gamma, 
      L_build_context ce gamma -> (*** Build up the typing context ***)
      k' = k c (d_fds ++ c_fds) -> (*** Check the constructor ***)
      fields Empty (ty_def te d) d_fds -> (*** Get parent fields ***)
      (forall md, In md mds -> Meth_WF c md) -> (*** Methods Well Formed ***)
      distinct (map (fun md' => match md' with md _ _ m _ _ => m end) mds) ->
      distinct (map (fun fd' => match fd' with fd _ f => f end) (d_fds ++ c_fds)) ->
      List_P1 (fun fd' => match fd' with fd ty _ => WF_Type gamma ty end) c_fds -> (*** Check field types ***)
      WF_Type gamma (ty_def te d) -> (*** Parent a well-formed type? ***)
      L_WF_Ext gamma ce c -> (*** Additional premises for extensions ***)
      L_WF (cld ce c (ty_def te d) c_fds k' mds).

  Variable (trans : E -> list Var -> Es -> E) 
    (x_eq_dec : forall x y : X, {x = y} + {x <> y}).

  Definition FJ_E_trans (e : FJ_E) (xs : list Var) (es' : Es) :=
    match e with 
      e_var y => (fix match_var xs es x : E := 
        match xs, es, x with
          this :: xs', e :: es', this => e
          | var n :: xs', e :: es', var m => if (x_eq_dec m n) then e else match_var xs' es' (var m)
          | _ :: xs' , _ :: es' , _ => match_var xs' es' x
          | _, _, _ => e_var x
        end) xs es' y
      | fd_access d f => fd_access (trans d xs es') f
      | m_call mce d m es => m_call mce (trans d xs es') m (map (fun e => trans e xs es') es)
      | new c es => new c (map (fun e => trans e xs es') es)
    end.

  Definition Xs_To_Vars (Xs : list X) : list Var := map (fun x => var x) Xs.

  Variable Reduce : E -> E -> Prop.

  Inductive FJ_Reduce : E -> E -> Prop :=
  | R_Field : forall (c : CL) te (ty : Ty) (fds : list FD) (es : Es) (f : F) (e : E) (n : nat) (mce : m_call_ext),
    fields Empty (ty_def te c) fds -> nth_error fds n = Some (fd ty f) -> nth_error es n = Some e ->
    FJ_Reduce (fd_access (new (ty_def te c) es) f) e 
  | R_Invk : forall (m : M) (c : CL) te (xs : list X) (e : E) (es ds: Es) (mce : m_call_ext) mbe,
    mbody Empty mce m (ty_def te c) (mb mbe xs e) -> 
    FJ_Reduce (m_call mce (new (ty_def te c) es) m ds) (trans e (this :: (Xs_To_Vars xs)) (EWrap (new (ty_def te c) es) :: ds)).

  Variable FJ_RedWrap : forall {e e'}, FJ_Reduce e e' -> Reduce e e'.
  Coercion FJ_RedWrap : FJ_Reduce >-> Reduce.

  Section FJ_Reduce_Rec.
    Variable (P : forall e e', Reduce e e' -> Prop).
    
    Hypothesis (H1 : forall c te ty fds es f e n mce fields_c In_f In_e,
      P _ _ (R_Field c te ty fds es f e n mce fields_c In_f In_e))
    (H2 : forall m c te xs e es ds mce mbe mbody_m,
      P _ _ (R_Invk m c te xs e es ds mce mbe mbody_m)).
    
    Definition FJ_Reduce_rect' e e' (red_e : FJ_Reduce e e') : P _ _ red_e :=
      match red_e return (P _ _ red_e) with 
        | R_Field c te ty fds es f e n mce fields_c In_f In_e =>
          H1 c te ty fds es f e n mce fields_c In_f In_e
        | R_Invk m c te xs e es ds mce mbe mbody_m =>
          H2 m c te xs e es ds mce mbe mbody_m
      end.

  End FJ_Reduce_Rec.

  Notation "e ~> d" := (Reduce e d) (at level 70).

  Variable (C_Reduce : E -> E -> Prop)
    (C_Reduce_List : Es -> Es -> Prop).

  Inductive FJ_Congruence_Reduce : E -> E -> Prop :=
    RC_Field : forall e e' f, C_Reduce e e' -> FJ_Congruence_Reduce (fd_access e f) (fd_access e' f)
  | RC_Invk_Recv : forall e e' mce m es, C_Reduce e e' ->
    FJ_Congruence_Reduce (m_call mce e m es) (m_call mce e' m es)
  | RC_Invk_Arg : forall e mce m es es', C_Reduce_List es es' ->
    FJ_Congruence_Reduce (m_call mce e m es) (m_call mce e m es')
  | RC_New_Arg : forall ty es es', C_Reduce_List es es' ->
    FJ_Congruence_Reduce (new ty es) (new ty es').

  Inductive Reduce_List : Es -> Es -> Prop :=
  | Reduce_T : forall e e' es, C_Reduce e e' -> Reduce_List (e :: es) (e' :: es)
  | Reduce_P : forall e es es', C_Reduce_List es es' -> Reduce_List (e :: es) (e :: es').

  Variables (FJ_C_Reduce_Wrap : forall e e', FJ_Congruence_Reduce e e' -> C_Reduce e e')
    (Reduce_List_Wrap : forall es es', Reduce_List es es' -> C_Reduce_List es es').

  Coercion FJ_C_Reduce_Wrap : FJ_Congruence_Reduce >-> C_Reduce.
  Coercion Reduce_List_Wrap : Reduce_List >-> C_Reduce_List.

  Section FJ_C_Reduce_Rec.
    Variable (P : forall e e', C_Reduce e e' -> Prop)
      (Q : forall es es', C_Reduce_List es es' -> Prop).
    
    Hypothesis (H1 : forall e e' f Red_e_e', P _ _ Red_e_e' -> P _ _ (RC_Field e e' f Red_e_e'))
      (H2 : forall e e' mce m es Red_e_e', P _ _ Red_e_e' -> P _ _ (RC_Invk_Recv e e' mce m es Red_e_e'))
      (H3 : forall e mce m es es' Red_es_es', Q _ _ Red_es_es' -> P _ _ (RC_Invk_Arg e mce m es es' Red_es_es'))
      (H4 : forall ty es es' Red_es_es', Q _ _ Red_es_es' -> P _ _ (RC_New_Arg ty es es' Red_es_es'))
      (H5 : forall e e' es Red_e_e', P _ _ Red_e_e' -> Q _ _ (Reduce_T e e' es Red_e_e'))
      (H6 : forall e es es' Red_es_es', Q _ _ Red_es_es' -> Q _ _ (Reduce_P e es es' Red_es_es')).
    
    Definition FJ_Congruence_Reduce_rect' e e' (red_e : FJ_Congruence_Reduce e e') 
      (C_Reduce_rect' : forall e e' red_e_e', P e e' red_e_e') 
      (C_Reduce_List_rect' : forall es es' red_es_es', Q es es' red_es_es') : P _ _ red_e :=
      match red_e return P _ _ red_e with 
        | RC_Field e e' f Red_e_e' => H1 e e' f Red_e_e' (C_Reduce_rect' _ _ Red_e_e')
        | RC_Invk_Recv e e' mce m es Red_e_e' => H2 e e' mce m es Red_e_e' (C_Reduce_rect' _ _ Red_e_e')
        | RC_Invk_Arg e mce m es es' Red_es_es' => H3 e mce m es es' Red_es_es' 
          (C_Reduce_List_rect' _ _ Red_es_es')
        | RC_New_Arg ty es es' Red_es_es' => H4 ty es es' Red_es_es' (C_Reduce_List_rect' _ _ Red_es_es')
      end.
    
    Definition Reduce_List_rect' es es' (red_es : Reduce_List es es')     
      (C_Reduce_rect' : forall e e' red_e_e', P e e' red_e_e') 
      (C_Reduce_List_rect' : forall es es' red_es_es', Q es es' red_es_es') : Q _ _ red_es :=
      match red_es return Q _ _ red_es with
        | Reduce_T e e' es red_e => H5 _ _ _ red_e (C_Reduce_rect' _ _ red_e) 
        | Reduce_P e es es' red_es => H6 _ _ _ red_es (C_Reduce_List_rect' _ _ red_es)
      end.

  End FJ_C_Reduce_Rec.

  Section Preservation.

    Definition Subtype_Weaken_P gamma ty ty' (sub_ty : subtype gamma ty ty') :=
      forall gamma', gamma = Empty -> subtype gamma' ty ty'.

    Variables (WF_CT : forall c l, CT c = Some l -> L_WF l)
      (FJ_E_WF_invert : forall gamma (e : FJ_E) c0, E_WF gamma e c0 -> FJ_E_WF gamma e c0)
      (EWrap_inject : forall (e e' : FJ_E), EWrap e = EWrap e' -> e = e')
      (Fields_eq : forall gamma ty fds, fields gamma ty fds -> forall gamma' fds', fields gamma' ty fds' -> fds = fds')
      (fds_distinct : forall gamma cl' fds, fields gamma cl' fds -> forall cl1 cl2 f m n fds',
        map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
        nth_error fds' m = Some (fd cl1 f) -> nth_error fds n = Some (fd cl2 f) -> m = n)
      (WF_fields_map_id : forall gamma cl' fds, fields gamma cl' fds ->
        forall tye c tye' fds' fds'', cl' = ty_def tye c -> fds'' = fds -> 
          fields gamma (ty_def tye' c) fds' -> 
          map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds)
      (Ty_inject : forall ty ty', TyWrap ty = TyWrap ty' -> ty = ty')
      (Fields_invert : forall gamma (ty : FJ_Ty) fds, fields gamma ty fds -> FJ_fields gamma ty fds)
      (fields_build_te_id : forall ce te te' te'' te''', 
        fields_build_te ce te te' te'' -> fields_build_te ce te te' te''' -> te'' = te''')
      (fields_build_tys_id : forall te ce tys tys' tys'', fields_build_tys te ce tys tys' -> 
        fields_build_tys te ce tys tys'' -> tys' = tys'')
      (parent_fields_names_eq : forall gamma cl' d_fds (cl_fields : fields gamma cl' d_fds)
        gamma' te te' d d_fds' d_fds'', cl' = ty_def te d -> d_fds'' = d_fds ->
        fields gamma' (ty_def te' d) d_fds' -> 
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds =
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds')
      (Fields_Build_tys_len : forall te ce tys tys', fields_build_tys te ce tys tys' -> length tys = length tys')
      (WF_fields_map_id' : forall gamma tye c ty', WF_fields_map gamma (ty_def tye c) ty' ->
        exists tye', ty' = ty_def tye' c)
      (WF_fields_map_sub : forall gamma c tye tye' fds fds', WF_fields_map gamma (ty_def tye c) (ty_def tye' c) ->
        fields Empty (ty_def tye c) fds -> fields Empty (ty_def tye' c) fds' -> 
        List_P2' (fun fd' fd'' => match fd', fd'' with fd S' _, fd T' _ => subtype Empty S' T' end) fds fds')
      (Subtype_Weaken : forall gamma S T sub_S_T, Subtype_Weaken_P gamma S T sub_S_T)
      (app_context : Context -> Context -> Context).

    Definition Weaken_Subtype_app_P (delta : Context) (S T : Ty) (sub_S_T : subtype delta S T) :=
      forall gamma, subtype (app_context delta gamma) S T.
    
    Lemma Weaken_Subtype_app_H1 : forall (ty : Ty) (gamma : Context), 
      Weaken_Subtype_app_P _ _ _ (sub_refl ty gamma).
      unfold Weaken_Subtype_app_P; intros; apply subtype_Wrap.
      constructor.
    Qed.
    
    Lemma Weaken_Subtype_app_H2 : forall c d e gamma sub_c sub_d, 
      Weaken_Subtype_app_P _ _ _ sub_c -> 
      Weaken_Subtype_app_P _ _ _ sub_d -> 
      Weaken_Subtype_app_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
      unfold Weaken_Subtype_app_P; intros; apply subtype_Wrap.
      econstructor; eauto.
    Qed.

    Lemma Weaken_Subtype_app_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
      Weaken_Subtype_app_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
      unfold Weaken_Subtype_app_P; intros; apply subtype_Wrap.
      econstructor 3; eauto.
    Qed.

    Definition cFJ_Weaken_Subtype_app := FJ_subtype_rect _ 
      Weaken_Subtype_app_H1 Weaken_Subtype_app_H2 Weaken_Subtype_app_H3.

    Definition FJ_Fields_eq_P gamma ty fds (fields_fds : fields gamma ty fds) := 
      forall gamma' fds', fields gamma' ty fds' -> fds = fds'.
    
    Lemma Fields_eq_H1 : forall te gamma, FJ_Fields_eq_P _ _ _ (fields_Wrap _ _ _ (fields_Obj te gamma)).
      unfold FJ_Fields_eq_P; intros.
      apply Fields_invert in H; inversion H; subst.
      reflexivity.
      generalize (Ty_inject _ _ H0); intros; discriminate.
    Qed.
    
    Lemma Fields_eq_H2 : forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
      FJ_Fields_eq_P _ _ _ par_fds -> 
      FJ_Fields_eq_P _ _ _ (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys).
      unfold FJ_Fields_eq_P; intros.
      apply Fields_invert in H0; inversion H0; subst.
      generalize (Ty_inject _ _ H3); intros; discriminate.
      generalize (Ty_inject _ _ H1); intros H7; inversion H7; subst.
      rewrite c_eq in H2; inversion H2; subst.
      rewrite (fields_build_tys_id _ _ _ _ _ H6 build_tys).
      rewrite (fields_build_te_id _ _ _ _ _ H3 te_upd) in H4.
      rewrite (H _ _ H4); reflexivity.
    Qed.
    
    Definition FJ_Fields_eq := FJ_fields_rect' _ Fields_eq_H1 Fields_eq_H2.

    Definition fds_distinct_P gamma cl' fds (fields_fds : fields gamma cl' fds) :=
      forall cl1 cl2 f m n fds',
        map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
        nth_error fds' m = Some (fd cl1 f) -> nth_error fds n = Some (fd cl2 f) -> m = n.

    Lemma fds_distinct_H1 : forall te gamma, fds_distinct_P _ _ _ (fields_Wrap _ _ _ (fields_Obj te gamma)).
      unfold fds_distinct_P; intros.
      destruct n; simpl in H1; discriminate.
    Qed.
    
    Lemma fds_distinct_H2 : forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
      fds_distinct_P _ _ _ par_fds -> 
      fds_distinct_P _ _ _ (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys).
      unfold fds_distinct_P; intros.
      generalize (WF_CT _ _ c_eq); intros WF_c; inversion WF_c; subst.
      assert (distinct (map (fun fd' => match fd' with fd _ f => f end) (d_fds ++ c_fds))). 
      generalize c_fds d_fds0 (parent_fields_names_eq _ _ _ par_fds _ _ _ _ _ _ 
        (refl_equal _) (refl_equal _) H12) H15; clear.
      induction d_fds; simpl; intros c_fds d_fds0 H H14; destruct d_fds0; simpl in H, H14;
        try discriminate; auto.
      destruct a; destruct f.
      injection H; intros d_fds_eq f_eq; rewrite f_eq; destruct H14 as [NotIn_f dist_rest]; split.
      unfold not; intros In_f; apply NotIn_f; generalize d_fds0 c_fds d_fds_eq In_f; clear; 
        induction d_fds; simpl; intros; destruct d_fds0; simpl in *|-*; try discriminate; auto.
      destruct a; destruct f0; simpl in d_fds_eq; injection d_fds_eq; clear d_fds_eq; intros d_fds_eq a_eq; subst.
      destruct In_f; try tauto; right; eapply IHd_fds; eauto.
      eauto.
      assert (nth_error (map (fun fd' => match fd' with fd _ f => f end) (d_fds ++ c_fds)) n = Some f).
      generalize tys d_fds n (Fields_Build_tys_len _ _ _ _ build_tys) H2; clear; 
        induction c_fds; destruct tys; simpl;
          try (induction d_fds; intros; destruct n; simpl in *|-* );
            first [discriminate | destruct a; injection H1; intros; subst; reflexivity | eauto];
              destruct a; simpl in *|-*; intros; try discriminate; injection H2; intros;
                first [ inversion H0; reflexivity | eauto].
      generalize tys n H0; clear; induction c_fds; simpl; intro n; destruct n; simpl; intros;
        try (destruct tys; simpl in H0; discriminate); eauto.
      destruct n; simpl in H0; discriminate.
      destruct n0; simpl in H0; discriminate.
      destruct n; simpl in H0; discriminate.
      destruct a; simpl in *|-*.
      destruct n0; simpl in *|-*; eauto;injection H0; intros; subst; reflexivity.
      assert (nth_error (map (fun fd' : FD => match fd' with
                                                | fd _ f => f
                                              end) fds') m = Some f) by
      (generalize m H1; clear; induction fds'; simpl; intro m; destruct m; simpl; intros; 
        try discriminate; eauto; destruct a; injection H1; intros; subst; reflexivity).
      rewrite H0 in H5.
      assert (map (fun fd' : FD => match fd' with fd _ f => f end) (Zip_Fields tys (snd (Unzip_Fields c_fds))) =
        map (fun fd' : FD => match fd' with fd _ f => f end) c_fds) by 
      (generalize tys (Fields_Build_tys_len _ _ _ _ build_tys); clear; induction c_fds; 
        simpl; intros; destruct tys; try destruct a; simpl in *|-*; try discriminate; auto;
          rewrite IHc_fds; injection H; auto).
      rewrite map_app in H5; rewrite H6 in H5; rewrite <- map_app in H5.
      generalize m n H3 H4 H5; clear;
        induction (map (fun fd' : FD => match fd' with
                                          | fd _ f => f
                                        end) (d_fds ++ c_fds)); simpl; intros;
        destruct m; destruct n; simpl in *|-*; intros; try discriminate; auto;
          destruct H3.
      inversion H5; subst.
      elimtype False; apply H; eapply nth_error_in; eauto.
      inversion H4; subst.
      elimtype False; apply H; eapply nth_error_in; eauto.
      eauto.
    Qed.
    
    Definition FJ_fds_distinct := FJ_fields_rect' _ fds_distinct_H1 fds_distinct_H2.

    Definition WF_fields_map_id_P gamma cl' fds (fields_fds : fields gamma cl' fds) :=
      forall tye c tye' fds' fds'', cl' = ty_def tye c -> fds'' = fds -> 
        fields gamma (ty_def tye' c) fds' -> 
        map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds.

    Lemma fields_map_id_H1 : forall te gamma, 
      WF_fields_map_id_P _ _ _ (fields_Wrap _ _ _ (fields_Obj te gamma)).
      unfold WF_fields_map_id_P; intros.
      apply Ty_inject in H; inversion H; subst.
      apply Fields_invert in H1; inversion H1; subst.
      reflexivity.
      apply Ty_inject in H0; inversion H0.
    Qed.
    
    Lemma fields_map_id_H2 : forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
      WF_fields_map_id_P _ _ _ par_fds -> 
      WF_fields_map_id_P _ _ _ (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys).
      unfold WF_fields_map_id_P; intros.
      apply Ty_inject in H0; inversion H0; subst; clear H0.
      apply Fields_invert in H2; inversion H2; subst.
      apply Ty_inject in H3; inversion H3.
      apply Ty_inject in H0; inversion H0; subst.
      rewrite c_eq in H1; injection H1; intros; subst; clear H1.
      rewrite map_app; rewrite (H _ _ _ _ _ (refl_equal _) (refl_equal _) H4); rewrite <- map_app.
      assert (map (fun fd' : FD => match fd' with | fd _ f => f end)
        (Zip_Fields tys0 (snd (Unzip_Fields c_fds0)) )= map (fun fd' : FD => match fd' with | fd _ f => f end)
        (Zip_Fields tys (snd (Unzip_Fields c_fds0)))).
      generalize (Fields_Build_tys_len _ _ _ _ H6); rewrite (Fields_Build_tys_len _ _ _ _ build_tys).
      clear; generalize tys tys0; induction c_fds0; simpl; intros;
        destruct tys2; destruct tys1; simpl; try discriminate; auto.
      destruct a; simpl; erewrite IHc_fds0; try reflexivity.
      simpl in H; injection H; auto.
      repeat rewrite map_app; rewrite H1; reflexivity.
    Qed.

    Definition FJ_fields_map_id := FJ_fields_rect' _ fields_map_id_H1 fields_map_id_H2.

    Lemma FJ_fields_build_te_id : forall ce te te' te'' te''', 
      FJ_fields_build_te ce te te' te'' -> FJ_fields_build_te ce te te' te''' -> te'' = te'''.
      intros; destruct te''; destruct te'''; reflexivity.
    Qed.

    Lemma FJ_fields_build_tys_id : forall te ce tys tys' tys'', FJ_fields_build_tys te ce tys tys' -> 
      FJ_fields_build_tys te ce tys tys'' -> tys' = tys''.
      unfold FJ_fields_build_tys; intros.
      destruct H; destruct H0; reflexivity.
    Qed.

    Lemma FJ_Fields_Build_tys_len : forall te ce tys tys', 
      FJ_fields_build_tys te ce tys tys' -> length tys = length tys'.
      unfold FJ_fields_build_tys; intros; destruct H; reflexivity.
    Qed.

    Lemma FJ_WF_fields_map_id' : forall gamma tye c ty', FJ_WF_fields_map gamma (ty_def tye c) ty' ->
      exists tye', ty' = ty_def tye' c.
      unfold FJ_WF_fields_map; intros; exists tye; destruct H; reflexivity.
    Qed.

    Lemma FJ_WF_fields_map_sub : forall gamma c tye tye' fds fds', 
      FJ_WF_fields_map gamma (ty_def tye c) (ty_def tye' c) ->
      fields Empty (ty_def tye c) fds -> fields Empty (ty_def tye' c) fds' -> 
      List_P2' (fun fd' fd'' => match fd', fd'' with fd S' _, fd T' _ => subtype Empty S' T' end)
      fds fds'.
      unfold FJ_WF_fields_map; intros; destruct H.
      rewrite (Fields_eq _ _ _ H0 _ _ H1).
      apply P2_if_P2'.
      unfold List_P2; intros.
      split; intros; eauto.
      exists a0; split; auto.
      destruct a0; eapply subtype_Wrap.
      constructor.
    Qed.

    Definition parent_fields_names_eq_P gamma cl' d_fds (cl_fields : fields gamma cl' d_fds) :=
      forall gamma' te te' d d_fds' d_fds'', cl' = ty_def te d -> d_fds'' = d_fds ->
        fields gamma' (ty_def te' d) d_fds' -> 
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds =
        map (fun fd' : FD => match fd' with fd _ f => f end) d_fds'.

    Lemma parent_fields_names_eq_H1 : forall te gamma, 
      parent_fields_names_eq_P _ _ _ (fields_Wrap _ _ _ (fields_Obj te gamma)).
      unfold parent_fields_names_eq_P; intros.
      apply Fields_invert in H1; apply Ty_inject in H; inversion H; subst.
      inversion H1; subst.
      reflexivity.
      apply Ty_inject in H0; inversion H0.
    Qed.

    Lemma parent_fields_names_eq_H2 : 
      forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys,
        parent_fields_names_eq_P _ _ _ par_fds -> 
        parent_fields_names_eq_P _ _ _ 
        (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq te_upd par_fds build_tys).
      unfold parent_fields_names_eq_P; intros;
        apply Ty_inject in H0; inversion H0; subst; clear H0.
      apply Fields_invert in H2; inversion H2; subst.
      apply Ty_inject in H3; inversion H3; subst.
      apply Ty_inject in H0; inversion H0; subst.
      rewrite c_eq in H1; inversion H1; subst.
      rewrite map_app; rewrite (H _ _ _ _ _ _ (refl_equal _) (refl_equal _) H4); rewrite <- map_app.
      assert (map (fun fd' : FD => match fd' with fd _ f => f end) (Zip_Fields tys (snd (Unzip_Fields c_fds0))) =
        map (fun fd' : FD => match fd' with fd _ f => f end) c_fds0) by 
      (generalize tys (Fields_Build_tys_len _ _ _ _ build_tys); clear; induction c_fds0; 
        simpl; intros; destruct tys; try destruct a; simpl in *|-*; try discriminate; auto;
          rewrite IHc_fds0; injection H; auto).
      assert (map (fun fd' : FD => match fd' with fd _ f => f end) (Zip_Fields tys0 (snd (Unzip_Fields c_fds0))) =
        map (fun fd' : FD => match fd' with fd _ f => f end) c_fds0) by 
      (generalize tys0 (Fields_Build_tys_len _ _ _ _ H6); clear; induction c_fds0; 
        simpl; intros; destruct tys0; try destruct a; simpl in *|-*; try discriminate; auto;
          rewrite IHc_fds0; injection H; auto).
      repeat rewrite map_app; rewrite H5; rewrite H7; reflexivity.
    Qed.

    Definition FJ_parent_fields_names_eq := 
      FJ_fields_rect' _ parent_fields_names_eq_H1 parent_fields_names_eq_H2.
    
    Lemma Subtype_Weaken_H1 : forall ty gamma, Subtype_Weaken_P _ _ _ (sub_refl ty gamma).
      unfold Subtype_Weaken_P; intros; subst.
      apply subtype_Wrap; constructor.
    Qed.
    
    Lemma Subtype_Weaken_H2 : forall c d e gamma sub_c sub_d, Subtype_Weaken_P _ _ _ sub_c -> 
      Subtype_Weaken_P _ _ _ sub_d -> Subtype_Weaken_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
      unfold Subtype_Weaken_P; intros; subst.
      eapply subtype_Wrap; econstructor 2; eauto.
    Qed.

    Lemma Subtype_Weaken_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
      Subtype_Weaken_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
      unfold Subtype_Weaken_P; intros; subst.
      eapply subtype_Wrap; econstructor 3; eauto.
    Qed.

    Definition FJ_Subtype_Weaken := FJ_subtype_rect _ Subtype_Weaken_H1 Subtype_Weaken_H2 Subtype_Weaken_H3.

    Definition preservation e e' (red_e : e ~> e') := 
      forall gamma c, E_WF gamma e c -> exists c', E_WF gamma e' c' /\ subtype gamma c' c.

    Lemma pres_H1 : forall c te ty fds es f e n mce fields_c In_f In_e,
      preservation _ _ (R_Field c te ty fds es f e n mce fields_c In_f In_e).
      unfold preservation; intros.
      apply FJ_E_WF_invert in H; inversion H; subst;
        apply EWrap_inject in H0; inversion H0; subst; clear H0.
      apply FJ_E_WF_invert in H1; inversion H1; subst;
        apply EWrap_inject in H0; inversion H0; subst; clear H0.
      rewrite (Fields_eq _ _ _ fields_c _ _ H6) in *|-*.
      apply P2'_if_P2 in H7; unfold List_P2 in H7; destruct H7 as [fnd_es not_fnd_es].
      destruct (fnd_es _ _ In_e) as [S [In_Ss WF_e]].
      exists S; split; auto.
      destruct (WF_fields_map_id' _ _ _ _ H2).
      generalize (WF_fields_map_id _ _ _ H3 _ _ _ _ _ H0 (refl_equal _) H6); intros.
      rewrite <- (fds_distinct _ _ _ H3 _ _ _ _ _ _ H7 In_f H4) in H4.
      apply P2'_if_P2 in H8; destruct H8 as [fnd_Ss _].
      destruct (fnd_Ss _ _ In_Ss) as [b [fnd_b sub_b]].
      destruct b.
      eapply subtype_Wrap; eapply sub_trans; eauto.
      destruct (WF_fields_map_id' _ _ _ _ H2); subst.
      generalize (WF_fields_map_sub _ _ _ _ _ _ H2 H6 H3); intros.
      apply P2'_if_P2 in H0; revert H0; unfold List_P2; intros.
      destruct H0.
      destruct (H0 _ _ fnd_b) as [b [nth_b sub_a]].
      destruct b.
      rewrite H4 in nth_b; inversion nth_b; subst.
      eapply Subtype_Weaken; eauto.
    Qed.

    Variables 
      (lookup_update_eq : forall gamma X ty, lookup (update gamma X ty) X ty) 
      (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
        lookup (update gamma Y ty') X ty)
      (lookup_update_neq' : forall gamma Y X ty ty',     lookup (update gamma Y ty') X ty -> X <> Y -> 
        lookup gamma X ty)
      (lookup_Empty : forall X ty, ~ lookup Empty X ty)
      (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty').

    Definition Weakening_P gamma e ty (WF_e : E_WF gamma e ty) :=
      forall gamma' vars, gamma = (update_list Empty vars) -> E_WF (update_list gamma' vars) e ty.

    Definition Weakening_Q gamma Es tys (WF_Es : List_P2' (E_WF gamma) Es tys) :=
      forall gamma' vars, gamma = (update_list Empty vars) -> 
        List_P2' (E_WF (update_list gamma' vars)) Es tys.

    Variables 
      (Weakening : forall gamma e ty WF_e, Weakening_P gamma e ty WF_e)
      (WF_mtype_map_sub : forall gamma ty ty', WF_mtype_ty_0_map gamma ty ty' -> subtype gamma ty ty')
      (Weaken_WF_fields_map : forall gamma vars ty ty', WF_fields_map (update_list Empty vars) ty ty' ->
        WF_fields_map (update_list gamma vars) ty ty')
      (Weaken_WF_mtype_ty_0_map : forall gamma vars ty ty', WF_mtype_ty_0_map (update_list Empty vars) ty ty' ->
        WF_mtype_ty_0_map (update_list gamma vars) ty ty')
      (Weaken_WF_mtype_Us_map : forall gamma vars mce Us Us' mtye, WF_mtype_Us_map (update_list Empty vars) mce mtye Us Us' ->
        WF_mtype_Us_map (update_list gamma vars) mce mtye Us Us')
      (Weaken_WF_mtype_U_map : forall gamma vars mce U U' mtye, WF_mtype_U_map (update_list Empty vars) mce mtye U U' ->
        WF_mtype_U_map (update_list gamma vars) mce mtye U U')
      (Weaken_Subtype_update_list : forall gamma S T (sub_S_T : subtype gamma S T)
        vars gamma', gamma = (update_list Empty vars) -> subtype (update_list gamma' vars) S T)
      (Weaken_WF_mtype_ext : forall gamma vars mce mtye, WF_mtype_ext (update_list Empty vars) mce mtye ->
        WF_mtype_ext (update_list gamma vars) mce mtye)
      (Weaken_WF_Type_update_list : forall gamma ty (WF_ty : WF_Type gamma ty) 
        vars gamma', gamma = (update_list Empty vars) -> WF_Type (update_list gamma' vars) ty)
      (Weaken_WF_Object_Ext : forall gamma vars te, wf_object_ext (update_list Empty vars) te ->
        wf_object_ext (update_list gamma vars) te).
    
    Lemma Weakening_H1 : forall gamma x ty lookup_x, Weakening_P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)).
      unfold Weakening_P; intros; subst; apply E_WF_Wrap; constructor.
      induction vars; simpl in *|-*.
      elimtype False; eapply lookup_Empty; eauto.
      destruct a; destruct x; destruct v.
      destruct (x_eq_dec x x0); subst.
      rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ t)); eauto.
      eapply lookup_update_neq' in lookup_x; try (eapply lookup_update_neq; eauto); congruence.
      eapply lookup_update_neq' in lookup_x; try (eapply lookup_update_neq; eauto); congruence.
      eapply lookup_update_neq' in lookup_x; try (eapply lookup_update_neq; eauto); congruence.
      rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ t)); eauto.
    Qed.

    Lemma Weakening_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds,
      Weakening_P _ _ _ WF_e -> 
      Weakening_P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
      unfold Weakening_P; intros; subst; apply E_WF_Wrap.
      econstructor; eauto.
    Qed.

    Lemma Weakening_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 
      ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye, 
      Weakening_P _ _ _ WF_e_0 -> Weakening_Q _ _ _ WF_es -> 
      Weakening_P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
        mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
      unfold Weakening_P; unfold Weakening_Q; intros; subst; apply E_WF_Wrap.
      econstructor; eauto.
      apply P2'_if_P2 in sub_Ss_Us'; unfold List_P2 in sub_Ss_Us' |-*; 
        destruct sub_Ss_Us'; apply P2_if_P2'; split; intros.
      destruct (H1 _ _ H3) as [U'' [nth_U'' sub_a_U'']]; exists U''; split; eauto.
      eauto.
    Qed.

    Lemma Weakening_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
      Weakening_Q _ _ _ WF_es ->
      Weakening_P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds)).
      unfold Weakening_P; unfold Weakening_Q; intros; subst; apply E_WF_Wrap.
      econstructor; eauto.
      apply P2'_if_P2 in sub_fds; unfold List_P2 in sub_fds |- *; destruct sub_fds; 
        apply P2_if_P2'; split; intros.
      destruct (H0 _ _ H2) as [b [nth_b sub_b]]; exists b; destruct b; split; eauto.
      eauto.
    Qed.

    Lemma Weakening_H5 : forall gamma, Weakening_Q _ _ _  (nil_P2' (E_WF gamma)).
      unfold Weakening_Q; intros; subst; constructor.
    Qed.

    Lemma Weakening_H6 : forall gamma e es ty tys WF_e WF_es,
      Weakening_P gamma e ty WF_e -> Weakening_Q gamma es tys WF_es -> 
      Weakening_Q _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
      unfold Weakening_P; unfold Weakening_Q; intros; subst.
      constructor; eauto.
    Qed.
    
    Definition FJ_Weakening := FJ_FJ_E_WF_rect' _ _ Weakening_H1 Weakening_H2 Weakening_H3
      Weakening_H4 Weakening_H5 Weakening_H6.

    Definition FJ_WF_mtype_map_sub : forall gamma ty ty', FJ_WF_mtype_ty_0_map gamma ty ty' -> 
      subtype gamma ty ty'.
    unfold FJ_WF_mtype_ty_0_map; intros; inversion H; subst.
    eapply subtype_Wrap; constructor.
  Qed.
  
  Lemma FJ_Weaken_WF_fields_map : forall gamma vars ty ty', 
    FJ_WF_fields_map (update_list Empty vars) ty ty' ->
    FJ_WF_fields_map (update_list gamma vars) ty ty'.
    unfold FJ_WF_fields_map; intros; inversion H; subst.
    constructor.
  Qed.
  
  Lemma FJ_Weaken_WF_mtype_ty_0_map : forall gamma vars ty ty', 
    FJ_WF_mtype_ty_0_map (update_list Empty vars) ty ty' ->
    FJ_WF_mtype_ty_0_map (update_list gamma vars) ty ty'.
    unfold FJ_WF_mtype_ty_0_map; intros; inversion H; subst.
    constructor.
  Qed.

  Lemma FJ_Weaken_WF_mtype_Us_map : forall gamma vars mce Us Us' mtye, 
    FJ_WF_mtype_Us_map (update_list Empty vars) mce mtye Us Us' ->
    FJ_WF_mtype_Us_map (update_list gamma vars) mce mtye Us Us'.
    unfold FJ_WF_mtype_Us_map; intros; inversion H; subst.
    constructor.
  Qed.

  Lemma FJ_Weaken_WF_mtype_U_map : forall gamma vars mce U U' mtye, 
    FJ_WF_mtype_U_map (update_list Empty vars) mce mtye U U' ->
    FJ_WF_mtype_U_map (update_list gamma vars) mce mtye U U'.
    unfold FJ_WF_mtype_U_map; intros; inversion H; subst.
    constructor.
  Qed.

  Definition Weaken_Subtype_update_list_P gamma S T (sub_S_T : subtype gamma S T) :=
    forall vars gamma', gamma = (update_list Empty vars) -> subtype (update_list gamma' vars) S T.

  Lemma Weaken_Subtype_update_list_H1 : forall (ty : Ty) (gamma : Context), 
    Weaken_Subtype_update_list_P _ _ _ (sub_refl ty gamma).
    unfold Weaken_Subtype_update_list_P; intros; apply subtype_Wrap.
    constructor.
  Qed.

  Lemma Weaken_Subtype_update_list_H2 : forall c d e gamma sub_c sub_d, 
    Weaken_Subtype_update_list_P _ _ _ sub_c -> 
    Weaken_Subtype_update_list_P _ _ _ sub_d -> 
    Weaken_Subtype_update_list_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
    unfold Weaken_Subtype_update_list_P; intros; apply subtype_Wrap.
    econstructor; eauto.
  Qed.

  Lemma Weaken_Subtype_update_list_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
    Weaken_Subtype_update_list_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
    unfold Weaken_Subtype_update_list_P; intros; apply subtype_Wrap.
    econstructor 3; eauto.
  Qed.

  Definition FJ_Weaken_Subtype_update_list := FJ_subtype_rect _
    Weaken_Subtype_update_list_H1 Weaken_Subtype_update_list_H2 Weaken_Subtype_update_list_H3.

  Definition FJ_Weaken_WF_mtype_ext : forall gamma vars mce mtye, 
    FJ_WF_mtype_ext (update_list Empty vars) mce mtye ->
    FJ_WF_mtype_ext (update_list gamma vars) mce mtye.
  unfold FJ_WF_mtype_ext; intros; inversion H; subst.
  constructor.
Qed.

Definition Weaken_WF_Class_Ext_Q gamma' cld te (wf_cld : wf_class_ext gamma' cld te) :=
  forall gamma vars, gamma' =  (update_list Empty vars) ->
    wf_class_ext (update_list gamma vars) cld te.

Definition FJ_Weaken_WF_Type_update_list_P gamma ty (WF_ty : WF_Type gamma ty) :=
  forall vars gamma', gamma = (update_list Empty vars) -> WF_Type (update_list gamma' vars) ty.

Lemma Weaken_WF_Type_update_list_H1 : forall gamma te wf_obj, 
  FJ_Weaken_WF_Type_update_list_P _ _ (WF_Obj gamma te wf_obj).
  unfold FJ_Weaken_WF_Type_update_list_P; intros; subst.
  apply FJ_WF_Type_Wrap; constructor; eauto.
Defined.

Lemma Weaken_WF_Type_update_list_H2 : forall gamma c cld te CT_c wf_cld_ext,
  Weaken_WF_Class_Ext_Q _ _ _ wf_cld_ext -> 
  FJ_Weaken_WF_Type_update_list_P _ _ (WF_Class gamma c cld te CT_c wf_cld_ext).
  unfold FJ_Weaken_WF_Type_update_list_P; intros; subst.
  unfold Weaken_WF_Class_Ext_Q in H; subst.
  apply FJ_WF_Type_Wrap; econstructor; eauto.
Defined.

Definition FJ_Weaken_WF_Type_update_list := 
  FJ_WF_Type_rect' _ _ Weaken_WF_Type_update_list_H1 Weaken_WF_Type_update_list_H2.

Lemma FJ_Weaken_WF_Object_Ext : forall gamma vars te, FJ_wf_object_ext (update_list Empty vars) te ->
  FJ_wf_object_ext (update_list gamma vars) te.
  unfold FJ_wf_object_ext; intros; auto.
Qed.

Lemma FJ_Weaken_WF_Class_Ext : forall gamma vars cld te, FJ_wf_class_ext (update_list Empty vars) cld te ->
  FJ_wf_class_ext (update_list gamma vars) cld te.
  unfold FJ_wf_class_ext; intros; auto.
Qed.

Variable (E_trans_Wrap : forall e vars es', trans (EWrap e) vars es' = FJ_E_trans e vars es').

Variables 
  (Lookup_dec : forall gamma x, (exists ty, lookup gamma x ty) \/ (forall ty, ~ lookup gamma x ty))
  (Lookup_app : forall gamma delta x ty, lookup gamma x ty -> lookup (app_context gamma delta) x ty)
  (Lookup_app' : forall gamma delta x ty, (forall ty', ~ lookup gamma x ty') -> lookup delta x ty -> 
    lookup (app_context gamma delta) x ty).

Definition Term_subst_pres_typ_P gamma e T (WF_e : E_WF gamma e T) :=
  forall delta xs Ts ds Ss Vars, gamma = update_list delta Vars -> 
    zip xs Ts (@pair _ _) = Some Vars -> List_P2' (E_WF delta) ds Ss ->
    List_P2' (subtype delta) Ss Ts->
    exists S, E_WF delta (trans e xs ds ) S /\ subtype delta S T.

Definition Term_subst_pres_typ_Q gamma es tys (WF_es : List_P2' (E_WF gamma) es tys) :=
  forall delta xs Ts ds Ss Vars , gamma =  update_list delta Vars -> 
    zip xs Ts (@pair _ _) = Some Vars -> List_P2' (E_WF delta) ds Ss ->
    List_P2' (subtype delta) Ss Ts ->
    exists Ss', List_P2' (E_WF delta) (map (fun e => trans e xs ds) es) Ss' /\ 
      List_P2' (subtype delta) Ss' tys.

Variable Lem_2_11 : forall delta e T WF_e, Term_subst_pres_typ_P delta e T WF_e.

Definition Lem_2_8_P delta S T (sub_S_T : subtype delta S T) :=
  forall T' fds', 
    WF_fields_map delta T T' -> fields Empty T' fds' -> exists S', 
      WF_fields_map delta S S' 
      /\ exists fds, fields Empty S' fds /\ 
        (forall fd' n, nth_error fds' n = Some fd' -> nth_error fds n = Some fd').

Definition Lem_2_9_P delta S T (sub_S_T : subtype delta S T) := forall S' T' m mtye Us Us' U U' mce,  
  WF_mtype_ty_0_map delta T T' -> mtype Empty m T' (mty mtye Us U) -> 
  WF_mtype_U_map delta mce mtye U U' -> 
  WF_mtype_Us_map delta mce mtye Us Us' -> 
  WF_mtype_ext delta mce mtye -> 
  WF_mtype_ty_0_map delta S S' -> 
  exists V, exists Vs, exists mtye',
    mtype Empty m S' (mty mtye' Vs V) /\ 
    exists V', WF_mtype_U_map delta mce mtye' V V' /\
      WF_mtype_Us_map delta mce mtye' Vs Us' /\
      subtype delta V' U' /\
      WF_mtype_ext delta mce mtye'.

Definition Subtype_Update_list_id_P gamma S T (sub_S_T : subtype gamma S T) :=
  forall delta vars, gamma = (update_list delta vars) -> subtype delta S T.

Definition WF_Type_update_list_id_P gamma ty (wf_ty : WF_Type gamma ty) :=
  forall delta Vars, gamma = (update_list delta Vars) -> WF_Type delta ty.

Variable (Lem_2_8 : forall delta S T sub_S_T, Lem_2_8_P delta S T sub_S_T)
  (Lem_2_9 : forall delta S T (sub_S_T : subtype delta S T), Lem_2_9_P _ _ _ sub_S_T)
  (WF_fields_map_update_list : forall delta Vars ty ty', 
    WF_fields_map (update_list delta Vars) ty ty' -> WF_fields_map delta ty ty')
  (WF_mtype_ty_0_map_Weaken_update_list : forall delta Vars T T',
    WF_mtype_ty_0_map (update_list delta Vars) T T' -> 
    WF_mtype_ty_0_map delta T T')
  (WF_mtype_U_map_Weaken_update_list : forall delta Vars mce mtye U U',
    WF_mtype_U_map (update_list delta Vars) mce mtye U U' -> 
    WF_mtype_U_map delta mce mtye U U')
  (WF_mtype_Us_map_Weaken_update_list : forall delta Vars mce mtye Us Us',
    WF_mtype_Us_map (update_list delta Vars) mce mtye Us Us' -> 
    WF_mtype_Us_map delta mce mtye Us Us')
  (WF_mtype_ext_Weaken_update_list : forall delta Vars mce mtye,
    WF_mtype_ext (update_list delta Vars) mce mtye ->
    WF_mtype_ext delta mce mtye)
  (WF_mtype_ty_0_map_total : forall delta S T, subtype delta S T -> forall T',
    WF_mtype_ty_0_map delta T T' ->  exists S', WF_mtype_ty_0_map delta S S')
  (Subtype_Update_list_id : forall gamma S T sub_S_T, Subtype_Update_list_id_P gamma S T 
    sub_S_T)
  (WF_mtype_ext_update_list_id : forall delta mce mtye Vars, 
    WF_mtype_ext (update_list delta Vars) mce mtye -> WF_mtype_ext delta mce mtye)
  (WF_Type_update_list_id : forall delta ty WF_ty, WF_Type_update_list_id_P delta ty WF_ty).

Lemma Term_subst_pres_typ_H1 : forall gamma x ty lookup_x, 
  Term_subst_pres_typ_P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)).
  unfold Term_subst_pres_typ_P; intros; subst.
  revert x ty delta Ts ds Ss Vars H0 H1 H2 lookup_x; induction xs; intros;
    destruct Ts; simpl in H0; inversion H0; subst.
  simpl in *|-*; exists ty; split.
  eapply E_WF_Wrap; rewrite E_trans_Wrap; econstructor; eauto.
  apply subtype_Wrap; constructor.
  caseEq (zip xs Ts (@pair _ _)); intros; rewrite H in H3; inversion H3; subst.
  inversion H2; subst; inversion H1; subst; rewrite E_trans_Wrap; destruct a; 
    destruct x; simpl.
  destruct (x_eq_dec x x0); subst.
  exists a0; split; eauto.
  simpl in lookup_x; rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)); 
    assumption.
  simpl in lookup_x; eapply lookup_update_neq' in lookup_x.
  destruct (IHxs _ _ _ _ _ _ _ H H10 H8 lookup_x) as [S [WF_x sub_S_ty]].
  rewrite E_trans_Wrap in WF_x; exists S; split; eauto.
  congruence.
  simpl in lookup_x; eapply lookup_update_neq' in lookup_x.
  destruct (IHxs _ _ _ _ _ _ _ H H10 H8 lookup_x) as [S [WF_x sub_S_ty]].
  rewrite E_trans_Wrap in WF_x; exists S; split; eauto.
  congruence.
  simpl in lookup_x; eapply lookup_update_neq' in lookup_x.
  destruct (IHxs _ _ _ _ _ _ _ H H10 H8 lookup_x) as [S [WF_x sub_S_ty]].
  rewrite E_trans_Wrap in WF_x; exists S; split; eauto.
  congruence.
  eexists; split; eauto.
  simpl in lookup_x; rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)); 
    assumption.
Qed.

Lemma Term_subst_pres_typ_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, 
  Term_subst_pres_typ_P _ _ _ WF_e ->
  Term_subst_pres_typ_P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
  unfold Term_subst_pres_typ_P; intros; subst.
  destruct (H _ _ _ _ _ _ (refl_equal _) H1 H2 H3) as [S0 [WF_trans_e sub_S0_ty]].
  destruct (Lem_2_8 _ _ _ sub_S0_ty ty' fds') as [S0' [S0_map [fds [fds_S subset_fds_fds']]]];
    eauto.
  exists ty''; split.
  eapply E_WF_Wrap; rewrite E_trans_Wrap; econstructor; eauto.
  eapply subtype_Wrap; constructor.
Qed.

Lemma Term_subst_pres_typ_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es 
  WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye, 
  Term_subst_pres_typ_P _ _ _ WF_e_0 -> Term_subst_pres_typ_Q _ _ _ WF_es -> 
  Term_subst_pres_typ_P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
    mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
  unfold Term_subst_pres_typ_P; unfold Term_subst_pres_typ_Q; intros; subst.
  destruct (H _ _ _ _ _ _ (refl_equal _) H2 H3 H4) as [S0 [WF_trans_e sub_S0_ty]].
  destruct (H0 _ _ _ _ _ _ (refl_equal _) H2 H3 H4) as [Ss0' [WF_trans_es sub_Ss0_tys']].
  destruct (WF_mtype_ty_0_map_total delta S0 _ sub_S0_ty ty_0') as [S0' map_S0'].
  eauto.
  destruct (Lem_2_9 _ _ _ sub_S0_ty _ _ _ _ _ _ _ _ _
    (WF_mtype_ty_0_map_Weaken_update_list _ _ _ _ ty_0_map)
    mtype_m
    (WF_mtype_U_map_Weaken_update_list _ _ _ _ _ _ map_U)
    (WF_mtype_Us_map_Weaken_update_list _ _ _ _ _ _ map_Us) 
    (WF_mtype_ext_Weaken_update_list _ _ _ _ WF_mtye) map_S0')
  as [V [Vs [mtye' [mtype_S0' [V' [V_map [Vs_map [sub_V'_ty' WF_mce_mtye']]]]]]]].
  eexists; split.
  eapply E_WF_Wrap; rewrite E_trans_Wrap; econstructor; eauto.
  assert (List_P2' (subtype delta) Ss Us').
  generalize sub_Ss_Us' Subtype_Update_list_id; clear; intros;
    Prop_Ind sub_Ss_Us'; intros; econstructor; eauto;
      injection H0; injection H1; intros; subst; eapply Subtype_Update_list_id; eauto.
  generalize H1 sub_Ss0_tys' subtype_Wrap; clear; intros; Prop_Ind H1; subst; intros;
    inversion sub_Ss0_tys'; subst; constructor; eauto.
  eapply subtype_Wrap; econstructor 2; eauto.
  assumption.    
Qed.

Lemma Term_subst_pres_typ_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
  Term_subst_pres_typ_Q _ _ _ WF_es -> 
  Term_subst_pres_typ_P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds)).
  unfold Term_subst_pres_typ_P; unfold Term_subst_pres_typ_Q; intros; subst.
  destruct (H _ _ _ _ _ _ (refl_equal _) H1 H2 H3) as [Ss' [WF_Ss' sub_Ss']].
  eexists; split.
  eapply E_WF_Wrap; rewrite E_trans_Wrap; econstructor; eauto.
  eapply WF_Type_update_list_id; eauto.
  generalize sub_Ss' sub_fds subtype_Wrap Subtype_Update_list_id; clear; 
    intros; Prop_Ind sub_Ss'; intros; subst; inversion sub_fds;
      subst; constructor; eauto.
  destruct b0.
  eapply subtype_Wrap; econstructor 2; eauto; eapply Subtype_Update_list_id; eauto.
  eapply subtype_Wrap; econstructor; eauto.
Qed.

Lemma Term_subst_pres_typ_H5 : forall gamma, 
  Term_subst_pres_typ_Q gamma nil nil (nil_P2' (E_WF gamma)).
  unfold Term_subst_pres_typ_Q; intros; subst.
  exists nil; split; constructor.
Qed.

Lemma Term_subst_pres_typ_H6 : forall gamma e es ty tys WF_e WF_es,
  Term_subst_pres_typ_P gamma e ty WF_e -> 
  Term_subst_pres_typ_Q gamma es tys WF_es -> 
  Term_subst_pres_typ_Q _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
  unfold Term_subst_pres_typ_P; unfold Term_subst_pres_typ_Q; intros; subst.
  destruct (H _ _ _ _ _ _ (refl_equal _) H2 H3 H4) as [S0 [WF_trans_e sub_S0_ty]].
  destruct (H0 _ _ _ _ _ _ (refl_equal _) H2 H3 H4) as [Ss0' [WF_trans_es sub_Ss0_tys']].
  exists (S0 :: Ss0'); split; constructor; auto.
Qed.

Definition FJ_Term_subst_pres_typ := FJ_FJ_E_WF_rect' _ _ 
  Term_subst_pres_typ_H1 Term_subst_pres_typ_H2 Term_subst_pres_typ_H3
  Term_subst_pres_typ_H4 Term_subst_pres_typ_H5 Term_subst_pres_typ_H6.

Definition WF_Type_par_P gamma ty' (WF_ty' : WF_Type gamma ty') := 
  forall te te' te'' ce c d fds k' mds delta, ty' = ty_def te' d -> 
    WF_Type delta (ty_def te (cl c)) -> CT c = Some (cld ce c (ty_def te' d) fds k' mds) -> 
    L_build_context ce gamma -> mtype_build_te ce te te' te'' -> 
    WF_Type delta (ty_def te'' d).

Variable (Build_S0'' : forall ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce
  Ds Ds' Vars (ce_WF : L_WF_Ext gamma' ce c)
  (build_gamma' : L_build_context ce gamma')
  (wf_me : Meth_WF_Ext gamma ce me)
  (build_te' : ce_build_cte ce te'),
  Meth_build_context ce me (update_list Empty ((this, TyWrap (ty_def te' (cl c))) :: 
    (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
  E_WF gamma e S0 -> subtype gamma S0 T0 -> wf_class_ext delta ce te -> 
  mtype_build_mtye ce te T0 vds me mtye -> 
  map_mbody ce te mce me e e' ->
  mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) -> WF_mtype_U_map delta mce mtye D D' ->
  WF_mtype_ext delta mce mtye ->
  WF_mtype_Us_map delta mce mtye Ds Ds' -> 
  List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
  zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
  (TyWrap (ty_def te (cl c)) :: Ds') (@pair _ _) = Some Vars ->
  mtype_build_tys ce te T0 vds me (map (fun vd' : VD => match vd' with
                                                          | vd ty _ => ty
                                                        end) vds) Ds -> 
  exists S0'', 
    subtype delta S0'' D' /\ 
       E_WF (update_list delta Vars) e' S0'')
(WF_mb_ext : Context -> mb_ext -> Prop)
(WF_Build_mb_ext : forall ce me gamma te te' c vds T0 delta  D D' mtye mce mbe
  Ds Ds' te'' Vars,  
  Meth_WF_Ext gamma ce me -> 
  Meth_build_context ce me (update_list Empty ((this, TyWrap (ty_def te' (cl c))) :: 
    (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
  WF_Type delta (ty_def te (cl c)) -> 
  build_mb_ext ce te mce me mbe -> 
  mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) -> WF_mtype_U_map delta mce mtye D D' ->
  WF_mtype_ext delta mce mtye ->
  WF_mtype_Us_map delta mce mtye Ds Ds' -> 
  List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
  zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
  (TyWrap (ty_def te'' (cl c)) :: Ds') (@pair _ _) = Some Vars ->
  mtype_build_tys ce te'' T0 vds me (map (fun vd' : VD => match vd' with
                                                            | vd ty _ => ty
                                                          end) vds) Ds -> 
  WF_mb_ext (update_list delta Vars) mbe)
(WF_mtype_Us_map_len : forall delta mce mtye Ds Ds', WF_mtype_Us_map delta mce mtye Ds Ds' ->
  length Ds = length Ds')
(mtype_build_tys_len : forall ce te ty vds me tys tys', mtype_build_tys ce te ty vds me tys tys' -> length tys = length tys')
(methods_build_te_id : forall ce te te' te'' te''', mtype_build_te ce te te' te'' -> mbody_build_te ce te te' te''' ->
  te'' = te''')
(WF_Type_par : forall delta ty WF_ty, WF_Type_par_P delta ty WF_ty)
(build_te_id : forall ce te te' te'', mbody_build_te ce te te'' te' -> 
  build_te ce te te'' te').

Definition FJ_WF_mb_ext : Context -> FJ_mb_ext -> Prop := fun gamma mbe => True.

Section Build_S0''_Sect.
  Variable te_eq : forall (te te' : ty_ext) , te = te'.

  Lemma FJ_te_eq : forall (te te' : FJ_ty_ext) , te = te'.
    destruct te'; destruct te; reflexivity.
  Qed.

  Lemma FJ_Build_S0'' (FJ_tye_unWrap : ty_ext -> FJ_ty_ext) :
    forall ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce
      Ds Ds' Vars 
      (ce_WF : FJ_L_WF_Ext gamma' ce c) (build_gamma' : FJ_L_build_context ce gamma')
      (wf_me : FJ_Meth_WF_Ext gamma ce me) (build_te' : FJ_ce_build_cte ce (FJ_tye_unWrap te')), 
      FJ_Meth_build_context ce me (update_list Empty ((this, TyWrap (ty_def te' (cl c))) :: 
        (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
      E_WF gamma e S0 -> subtype gamma S0 T0 -> FJ_wf_class_ext gamma ce (FJ_tye_unWrap te) ->
      FJ_mtype_build_mtye ce (FJ_tye_unWrap te) T0 vds me mtye -> 
      FJ_map_mbody ce (FJ_tye_unWrap te) mce me e e' -> 
      FJ_mtype_build_tys ce (FJ_tye_unWrap te) T0 vds me (T0 :: nil) (D :: nil) -> 
      FJ_WF_mtype_U_map delta mce mtye D D' ->
      FJ_WF_mtype_ext delta mce mtye ->
      FJ_WF_mtype_Us_map delta mce mtye Ds Ds' -> 
      List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
      zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
      (TyWrap (ty_def te (cl c)) :: Ds') (@pair _ _) = Some Vars -> 
      FJ_mtype_build_tys ce (FJ_tye_unWrap te) T0 vds me (map (fun vd' : VD => match vd' with
                                                                                 | vd ty _ => ty
                                                                               end) vds) Ds -> 
      exists S0'',
        subtype delta S0'' D' /\ E_WF (update_list delta Vars) e' S0''.
    intros.
    inversion H; inversion H5; inversion H6; subst.
    inversion H7; inversion H8; subst.
    inversion H4; subst.
    exists S0; split.
    eapply Subtype_Weaken; try reflexivity; eapply Subtype_Update_list_id; eauto.
    inversion H11; subst.
    assert (zip (map (fun Tx : VD => match Tx with | vd _ x => var x end) vds) 
      (map (fun Tx : VD => match Tx with | vd ty _ => ty end) vds) (@pair _ _) = 
      Some (map (fun Tx : VD => match Tx with | vd ty x => (var x, ty) end) vds)) by
    (clear; induction vds; simpl; try reflexivity; rewrite IHvds; destruct a; simpl; reflexivity).
    simpl in H10; rewrite H12 in H10; injection H10; intros; subst.
    rewrite (te_eq te te'); eapply Weakening; eauto.
  Qed.  

End Build_S0''_Sect.

Lemma distinct_ms_md_eq : forall mds me me0 ty ty0 m vds0 vds e e1,
  distinct
  (map (fun md' : MD => match md' with
                          | md _ _ m1 _ _ => m1
                        end) mds) ->
  In (md me0 ty0 m vds0 e1) mds -> In (md me ty m vds e) mds -> 
  md me ty m vds e = md me0 ty0 m vds0 e1.
  clear; induction mds; simpl; intros.
  contradiction.
  destruct H as [NIn dis_mds].
  destruct H1; destruct H0; subst.
  injection H; intros; subst; reflexivity.
  elimtype False; apply NIn; generalize H0; clear; induction mds; simpl; intros.
  contradiction.
  destruct H0; subst.
  left; reflexivity.
  right; auto.
  elimtype False; apply NIn; generalize H; clear; induction mds; simpl; intros.
  contradiction.
  destruct H; subst.
  left; reflexivity.
  right; auto.
  auto.
Qed.

Variable (mtype_invert : forall gamma m te c mty, mtype gamma m (ty_def te (cl c)) mty ->
  FJ_mtype gamma m (ty_def te (cl c)) mty)
(WF_mtype_ty_0_map_cl_id'' : forall delta te d S', 
  WF_mtype_ty_0_map delta (ty_def te d) S' -> S' = ty_def te d)
(WF_mtype_ty_0_map_tot' : forall delta te c, exists S', WF_mtype_ty_0_map delta (ty_def te c) S')
(WF_Type_invert : forall delta S, WF_Type delta (TyWrap S) -> FJ_WF_Type delta S).

Lemma FJ_WF_mtype_ty_0_map_cl_id'' : forall delta te d S',
  FJ_WF_mtype_ty_0_map delta (TyWrap (ty_def te d)) S' ->
  S' = TyWrap (ty_def te d).
  intros; inversion H; subst; reflexivity.
Qed.

Lemma FJ_WF_mtype_ty_0_map_tot' : forall delta te c,
  exists S' : Ty, FJ_WF_mtype_ty_0_map delta (TyWrap (ty_def te c)) S'.
  intros; eexists; constructor.
Qed.

Lemma FJ_WF_Build_mb_ext (FJ_tye_unWrap : ty_ext -> FJ_ty_ext) :
  forall ce me gamma te te' c vds T0 delta D D' mtye mce mbe
    Ds Ds' te'' Vars, 
    FJ_Meth_WF_Ext gamma ce me -> 
    FJ_Meth_build_context ce me (update_list Empty ((this, TyWrap (ty_def te' (cl c))) :: 
      (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
    WF_Type delta (ty_def te (cl c)) ->
    FJ_build_mb_ext ce (FJ_tye_unWrap te) mce me mbe -> 
    FJ_mtype_build_tys ce (FJ_tye_unWrap te) T0 vds me (T0 :: nil) (D :: nil) -> 
    FJ_WF_mtype_U_map delta mce mtye D D' ->
    FJ_WF_mtype_ext delta mce mtye ->
    FJ_WF_mtype_Us_map delta mce mtye Ds Ds' -> 
    List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
    zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
    (TyWrap (ty_def te'' (cl c)) :: Ds') (@pair _ _) = Some Vars ->
    te = te'' -> te'' = te' ->
    FJ_mtype_build_tys ce (FJ_tye_unWrap te'') T0 vds me (map (fun vd' : VD => match vd' with
                                                                                 | vd ty _ => ty
                                                                               end) vds) Ds -> 
    FJ_WF_mb_ext (update_list delta Vars) mbe.
  intros; auto.
Qed.

Lemma FJ_Lem_2_12 : forall m C_0 mce mbe xs e,
  mbody Empty mce m C_0 (mb mbe xs e) -> forall C_0' delta Ds Ds' D D' mtye, 
    mtype Empty m C_0' (mty mtye Ds D) -> 
    WF_mtype_ty_0_map delta C_0 C_0' ->
    WF_Type delta C_0 ->
    WF_mtype_ext delta mce mtye -> 
    WF_mtype_Us_map delta mce mtye Ds Ds'-> 
    WF_mtype_U_map delta mce mtye D D' ->
    exists S, exists Vars, exists N,
      zip (this :: Xs_To_Vars xs) (N :: Ds') (@pair _ _) = Some Vars /\ 
      subtype delta C_0' N /\ WF_Type delta N /\
      subtype delta S D' /\ 
      E_WF (update_list delta Vars) e S 
      /\ WF_mb_ext (update_list delta Vars) mbe.
  intros until e; intro H.
  assert (exists mce', mce = mce') by (eexists; reflexivity);
    destruct H0 as [mce' mce_eq]; rewrite mce_eq in H; revert mce mce_eq.
  assert (exists mb', mb mbe xs e = mb') by (eexists; reflexivity);
    destruct H0 as [mb' mb_eq]; rewrite mb_eq in H; revert xs e mb_eq.
  assert (exists gamma', Empty = gamma') by (eexists; reflexivity);
    destruct H0 as [gamma' gamma_eq]; rewrite gamma_eq in H; revert gamma_eq.
  induction H.
  intros; rewrite (WF_mtype_ty_0_map_cl_id'' _ _ _ _ H4) in *|-*.
  intros; apply mtype_invert in H3; inversion H3.
  apply Ty_inject in H9; injection H9; intros; clear gamma0 gamma_eq H14; subst;
    rewrite H13 in H; inversion H; subst; clear H9 H.
  generalize (WF_CT _ _ H13); intros WF_c; inversion WF_c; subst.
  generalize (H22 _ H0); intros WF_m; inversion WF_m; subst.
  injection mb_eq; intros; subst; clear mb_eq.
  caseEq (zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds)) 
    (TyWrap (ty_def te (cl c)) :: Ds') (@pair _ _)); intros.
  rewrite H33 in H13; inversion H13; subst.
  generalize (distinct_ms_md_eq _ _ _ _ _ _ _ _ _ _ H23 H0 H16) as md_eq; intro.
  injection md_eq; intros; subst.
  apply WF_Type_invert in H5; inversion H5; subst; apply Ty_inject in H9; try discriminate;
    injection H9; intros; subst; rewrite H10 in H33; injection H33; intros; subst.
  destruct (Build_S0'' ce me gamma1 gamma0 te te1 c vds e_0 ty delta e e' D D' mtye mce 
    Ds Ds' l) as [S0'' [sub_S0'' WF_e]]; auto.
  exists S0''; exists l; exists (ty_def te (cl c)); repeat split; auto.
  simpl.
  assert (zip (Xs_To_Vars (map (fun vd' : VD => match vd' with | vd _ x => x end) vds)) Ds' (@pair _ _) =
    zip (map (fun Tx : VD => match Tx with | vd _ x => var x end) vds) Ds' (@pair _ _)).
  generalize l Ds'; clear; induction vds; simpl; intros.
  destruct Ds'; auto.
  destruct Ds'.
  reflexivity.
  rewrite <- IHvds.
  caseEq (zip (Xs_To_Vars (map (fun vd' => match vd' with | vd _ x => x end) vds)) Ds' (@pair _ _)); 
  auto; destruct a; simpl; reflexivity.
  assumption.
  rewrite H11.
  revert H; simpl;
    caseEq (zip (map (fun Tx : VD => match Tx with | vd _ x => var x end) vds) Ds' (@pair _ _));
    auto.
  eauto.
  revert H; simpl;
    caseEq (zip (map (fun Tx : VD => match Tx with | vd _ x => var x end) vds) Ds' (@pair _ _)).
  discriminate.
  generalize (distinct_ms_md_eq _ _ _ _ _ _ _ _ _ _ H23 H0 H16) as md_eq; intro;
    injection md_eq; intros; subst.
  elimtype False; generalize (WF_mtype_Us_map_len _ _ _ _ _ H7);
    generalize Ds Ds' (mtype_build_tys_len _ _ _ _ _ _ _ H17) H; clear; induction vds;
      intros Ds Ds'; destruct Ds; destruct Ds'; simpl; intros; try discriminate.
  caseEq (zip (map (fun Tx : VD => match Tx with | vd _ x => var x end) vds) Ds' (@pair _ _));
  intros; rewrite H2 in H0; try discriminate; eapply IHvds; eauto.
  congruence.
  generalize Ty_inject H9 H H10 H11 H0; clear; intros; apply Ty_inject in H9; inversion H9; subst; 
    rewrite H in H10; inversion H10; subst.
  elimtype False; eapply H11; apply H0.
  intros; rewrite (WF_mtype_ty_0_map_cl_id'' _ _ _ _ H4) in *|-*.
  apply mtype_invert in H3; inversion H3.
  generalize Ty_inject H9 H13 H16 H H0; clear; intros; apply Ty_inject in H9; inversion H9; subst; 
    rewrite H in H13; inversion H13; subst.
  elimtype False; eapply H0; apply H16.
  apply Ty_inject in H9; inversion H9; revert H13 gamma_eq; subst; rewrite H in H10; 
    inversion H10; subst; intros.
  rewrite (methods_build_te_id _ _ _ _ _ H12 H1) in *|-*.
  generalize (WF_CT _ _ H); intros WF_c; inversion WF_c; revert H13 gamma_eq; subst; intros.
  destruct (IHmbody (gamma_eq) _ _ (refl_equal _) _ (refl_equal _) _ delta Ds Ds' D D' _ H15) as 
    [S [Vars [N [Vars_eq [sub_d0 [WF_N [sub_S [WF_e WF_mbe]]]]]]]]; eauto.
  destruct (WF_mtype_ty_0_map_tot' delta te' d0).
  rewrite (WF_mtype_ty_0_map_cl_id'' _ _ _ _ H14) in H14; assumption.
  eapply WF_Type_par; eauto.
  rewrite <- (methods_build_te_id _ _ _ _ _ H12 H1); assumption.
  exists S; exists Vars; exists N; repeat split; auto.
  apply subtype_Wrap; econstructor 2.
  apply subtype_Wrap; econstructor 3; eauto.
  assumption.
Qed.    

Variable (Lem_2_12 : forall m C_0 mce mbe xs e,
  mbody Empty mce m C_0 (mb mbe xs e) -> forall C_0' delta Ds Ds' D D' mtye, 
    mtype Empty m C_0' (mty mtye Ds D) -> 
    WF_mtype_ty_0_map delta C_0 C_0' ->
    WF_Type delta C_0 ->
    WF_mtype_ext delta mce mtye -> 
    WF_mtype_Us_map delta mce mtye Ds Ds'-> 
    WF_mtype_U_map delta mce mtye D D' ->
    exists S, exists Vars, exists N,
      zip (this :: Xs_To_Vars xs) (N :: Ds') (@pair _ _) = Some Vars /\ 
      subtype delta C_0' N /\ WF_Type delta N /\
      subtype delta S D' /\ 
      E_WF (update_list delta Vars) e S
      /\ WF_mb_ext (update_list delta Vars) mbe).

Definition fields_tot_P delta ty fds (ty_fields : fields delta ty fds) :=
  forall te te'' te''' ce d, ty = (ty_def te d) -> 
    fields_build_te ce te''' te te'' -> exists fds', fields delta (ty_def te'' d) fds'.

Definition fields_id_P delta ty fds (ty_fields : fields delta ty fds) :=
  forall te c fds', ty = (ty_def te c) ->
    fields delta (ty_def te c) fds' -> fds = fds'.

Variables (WF_fields_map_tot : forall gamma te c, 
  exists te', WF_fields_map gamma (ty_def te c) (ty_def te' c))
(fields_build_te_tot : forall ce te te' te3 te4, build_te ce te te3 te4 -> 
  exists te'', fields_build_te ce te te' te'')
(fields_build_tys_tot : forall te ce tys te' te'', build_te ce te te' te'' ->
  exists tys', fields_build_tys te ce tys tys')
(fields_build_te_tot' : forall ce0 ce te te' te'' te3 te4, fields_build_te ce0 te'' te3 te4 -> 
  fields_build_te ce te3 te te' -> 
  exists te'', fields_build_te ce te4 te te'')
(fields_build_tys_tot' : forall te ce tys tys3 tys4, fields_build_tys te ce tys3 tys4 ->
  exists tys', fields_build_tys te ce tys tys')
(WF_fields_map_id'' : forall ty gamma ty' ty'', 
  WF_fields_map gamma ty ty' ->
  WF_fields_map gamma ty ty'' -> ty' = ty'')
(fields_tot : forall delta ty fds ty_fields, fields_tot_P delta ty fds ty_fields)
(fields_build_te_id' : forall gamma ce c d te te' te'' te3 te4 te5, 
  build_te ce te te5 te' -> 
  WF_fields_map gamma (ty_def te' d) (ty_def te'' d) -> 
  WF_fields_map gamma (ty_def te (cl c)) (ty_def te3 (cl c)) ->
  fields_build_te ce te3 te5 te4 -> te'' = te4)
(fields_id : forall delta ty fds ty_fields,
  fields_id_P delta ty fds ty_fields)
(WF_fields_map_bld_te_tot : forall gamma c ce te te', WF_fields_map gamma (ty_def te c) (ty_def te' c) -> 
  forall te3 te4, build_te ce te te3 te4 -> exists te5, build_te ce te' te3 te5)
(WF_fields_map_id_FJ : forall gamma ty, WF_fields_map gamma (TyWrap ty) (TyWrap ty))
(bld_te_eq_fields_build_te : forall ce te te' te'', build_te ce te te' te'' -> fields_build_te ce te te' te'').

Lemma Lem_2_8_H1 : forall (ty : Ty) (gamma : Context), 
  Lem_2_8_P _ _ _ (sub_refl ty gamma).
  unfold Lem_2_8_P; intros.
  exists T'; split; auto.
  exists fds'; repeat split; auto.
Qed.

Lemma Lem_2_8_H2 : forall c d e gamma sub_c sub_d, 
  Lem_2_8_P _ _ _ sub_c -> 
  Lem_2_8_P _ _ _ sub_d -> 
  Lem_2_8_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
  unfold Lem_2_8_P; intros.
  destruct (H0 _ _ H1 H2) as [S' [WF_S' [fds [fields_fds sub_fds]]]].
  destruct (H _ _ WF_S' fields_fds) as [S'' [WF_S'' [fds'' [fields_fds'' sub_fds'']]]].
  exists S''; split; auto.
  exists fds''; split; auto.
Qed.

Lemma Lem_2_8_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
  Lem_2_8_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
  unfold Lem_2_8_P; intros.
  destruct (WF_fields_map_tot gamma te (cl c)) as [te''' WF_S'];
    eexists; split; eauto.
  rewrite (WF_fields_map_id'' _ _ _ _ WF_S' (WF_fields_map_id_FJ _ _)).
  destruct (fields_build_tys_tot _ _ (fst (Unzip_Fields fs)) _ _ bld_te) as [tys' build_tys'].
  eexists; split.
  apply fields_Wrap; econstructor; try eassumption.
  apply (bld_te_eq_fields_build_te _ _ _ _ bld_te).
  rewrite (WF_fields_map_id'' _ _ _ _ H (WF_fields_map_id_FJ _ _)) in H0; eassumption.
  clear; induction fds'; intros; destruct n; simpl in *|-*; try discriminate; eauto.
Qed.

Definition FJ_Lem_2_8 := FJ_subtype_rect _ Lem_2_8_H1 Lem_2_8_H2 Lem_2_8_H3.

Variable (WF_mtype_ty_0_map_id : forall delta S T T', WF_mtype_ty_0_map delta S T ->
  WF_mtype_ty_0_map delta S T' -> T = T')
(WF_mtype_ty_0_map_tot : forall delta S T, subtype delta S T -> forall T',
  WF_mtype_ty_0_map delta T T' -> exists S', WF_mtype_ty_0_map delta S S')
(WF_mtype_ty_0_map_cl_id : forall delta te te' d c, 
  WF_mtype_ty_0_map delta (ty_def te d) (ty_def te' (cl c)) -> d = cl c)
(WF_mtype_ty_0_map_cl_id' : forall delta te d S', 
  WF_mtype_ty_0_map delta (ty_def te d) S' -> exists te', S' = ty_def te' d)
(m_eq_dec : forall (m m' : M), {m = m'} + {m <> m'})
(build_te_build_ty_0_id : forall ce c d te te' te'' te''' te4 delta, 
  build_te ce te te4 te' -> 
  WF_mtype_ty_0_map delta (ty_def te' d) (ty_def te''' d) ->
  WF_mtype_ty_0_map delta (ty_def te (cl c)) (ty_def te'' (cl c)) ->
  mtype_build_te ce te'' te4 te''').

Lemma In_m_mds_dec : forall m mds, 
  (exists mde, exists ty, exists vds, exists e, In (md mde ty m vds e) mds) \/
  (forall mde ty vds e, ~ In (md mde ty m vds e) mds).
  revert m_eq_dec; clear; induction mds; intros; simpl.
  tauto.
  destruct a as [mde' ty' m' vds' e']; destruct (m_eq_dec m m').
  subst; left; exists mde'; exists ty'; exists vds'; exists e'; tauto.
  destruct IHmds as [[mde'' [ty'' [vds'' [e'' In_m]]]] | NIn_m].
  left; exists mde''; exists ty''; exists vds''; exists e''; tauto.
  right; unfold not; intros mde ty vds e H; destruct H.
  congruence.
  eapply NIn_m; eauto.
Qed.

Lemma Lem_2_9_H1 : forall (ty : Ty) (gamma : Context), 
  Lem_2_9_P _ _ _ (sub_refl ty gamma).
  unfold Lem_2_9_P; intros.
  rewrite (WF_mtype_ty_0_map_id _ _ _ _ H H4) in *|-*.
  repeat eexists; try eassumption; repeat split; try eassumption.
  apply subtype_Wrap; constructor.
Qed.

Lemma Lem_2_9_H2 : forall c d e gamma sub_c sub_d, 
  Lem_2_9_P _ _ _ sub_c -> 
  Lem_2_9_P _ _ _ sub_d -> 
  Lem_2_9_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
  unfold Lem_2_9_P; intros.
  destruct (WF_mtype_ty_0_map_total _ _ _ sub_d _ H1) as [W map_d].
  destruct (H0 _ _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 map_d) as 
    [V [Vs [mtye' [mtype_W [V' [map_V [map_Vs [sub_V_U' WF_mce_mtye]]]]]]]].
  destruct (H _ _ _ _ _ _ _ _ _ map_d mtype_W map_V map_Vs WF_mce_mtye H6) as
    [Q [Qs [mtye'' [mtype_S' [Q' [map_Q [map_Qs [sub_Q_V' WF_mce_mtye']]]]]]]].
  repeat eexists; try eassumption; repeat split; try eassumption.
  apply subtype_Wrap; econstructor 2; eassumption.
Qed.

Variable WF_mtype_ty_0_map_cl_refl : forall delta T, WF_mtype_ty_0_map delta (TyWrap T) (TyWrap T).
Variable mtype_build_tys_tot : forall ce te te' te'' ty vds me tys, build_te ce te te'' te' -> 
  exists tys', mtype_build_tys ce te ty vds me tys tys'.
Variable mtype_build_mtye_tot : forall ce te te' te'' ty vds mde', build_te ce te te'' te' -> 
  exists mtye',mtype_build_mtye ce te ty vds mde' mtye'. 
Variable build_V' : forall gamma1 m ty mde' Ws W,
  override gamma1 m ty mde' Ws W -> 
  forall gamma gamma' ce ce' te te' te'' d T' mtye U U' Us Us' mce vars mtye' W' Ws'  vds,
    ty = (ty_def te'' d) -> 
    WF_mtype_ty_0_map gamma (ty_def te' d) T' ->
    mtype Empty m T' (mty mtye Us U) ->
    WF_mtype_U_map gamma mce mtye U U' ->
    WF_mtype_Us_map gamma mce mtye Us Us' ->
    WF_mtype_ext gamma mce mtye ->  
    build_te ce te te'' te' ->
    L_build_context ce gamma' ->
    (wf_class_ext gamma' ce'  te'' \/ wf_object_ext gamma' te'') -> 
    Meth_build_context ce mde' (update_list Empty vars) gamma1 -> 
    WF_Type gamma1 W ->
    List_P1 (WF_Type gamma1) Ws -> 
    Meth_WF_Ext gamma1 ce mde' ->
    mtype_build_mtye ce te W vds mde' mtye' ->
    mtype_build_tys ce te W vds mde' Ws Ws' ->
    mtype_build_tys ce te W vds mde' (W :: nil) (W' :: nil) ->
    exists V', WF_mtype_U_map gamma mce mtye' W' V' /\
      WF_mtype_Us_map gamma mce mtye' Ws' Us' /\
      subtype gamma V' U' /\ WF_mtype_ext gamma mce mtye'.

   Lemma FJ_WF_fields_map_id_FJ : forall gamma ty, FJ_WF_fields_map gamma (TyWrap ty) ty.
     intros; constructor.
   Qed.

   Lemma FJ_bld_te_eq_fields_build_te : forall ce te te' te'',
     FJ_build_te ce te te' te'' -> FJ_fields_build_te ce te te' te''.
     intros; inversion H; subst; constructor; auto.
   Qed.

   Lemma FJ_WF_mtype_ty_0_map_cl_refl : forall delta T, 
     FJ_WF_mtype_ty_0_map delta (TyWrap T) (TyWrap T).
     intros; constructor.
   Qed.

Lemma FJ_mtype_build_tys_tot : forall ce te te' te'' ty vds me tys, FJ_build_te ce te te'' te' -> 
  exists tys', FJ_mtype_build_tys ce te ty vds me tys tys'.
  intros; eexists; econstructor.
Qed.

Lemma FJ_mtype_build_mtye_tot : forall ce te te' te'' ty vds mde', FJ_build_te ce te te'' te' -> 
  exists mtye', FJ_mtype_build_mtye ce te ty vds mde' mtye'. 
  intros; exists tt; econstructor.
Qed.

Section FJ_build_V'_Sec.

  Variable build_te_refl : forall ce te te' te'', build_te ce te te' te'' -> te' = te''.
  Variable WF_mtype_U_map_trans : forall gamma mce mtye U U' mtye', WF_mtype_U_map gamma mce mtye U U' ->
    WF_mtype_U_map gamma mce mtye' U U'.
  Variable WF_mtype_Us_map_trans : forall gamma mce mtye Us Us' mtye', WF_mtype_Us_map gamma mce mtye Us Us' ->
    WF_mtype_Us_map gamma mce mtye' Us Us'.
  Variable WF_mtype_ext_trans : forall gamma mce mtye mtye', WF_mtype_ext gamma mce mtye -> WF_mtype_ext gamma mce mtye'.
  Variable mtype_build_tys_refl : forall ce te U vds mde' Ts Ts', mtype_build_tys ce te U vds mde' Ts Ts' -> Ts = Ts'.
  
  Lemma FJ_build_te_refl : forall ce te te' te'', FJ_build_te ce te te' te'' -> te' = te''.
    intros; inversion H; subst; auto.
  Qed.

  Lemma FJ_WF_mtype_U_map_trans : forall gamma mce mtye U U' mtye', FJ_WF_mtype_U_map gamma mce mtye U U' ->
    FJ_WF_mtype_U_map gamma mce mtye' U U'.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_WF_mtype_Us_map_trans : forall gamma mce mtye Us Us' mtye', FJ_WF_mtype_Us_map gamma mce mtye Us Us' ->
    FJ_WF_mtype_Us_map gamma mce mtye' Us Us'.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_WF_mtype_ext_trans : forall gamma mce mtye mtye', FJ_WF_mtype_ext gamma mce mtye -> 
    FJ_WF_mtype_ext gamma mce mtye'.
    intros; inversion H; subst; constructor.
  Qed.

  Lemma FJ_mtype_build_tys_refl : forall ce te U vds mde' Ts Ts', FJ_mtype_build_tys ce te U vds mde' Ts Ts' -> Ts = Ts'.
    intros; inversion H; subst; auto.
  Qed.

  Lemma FJ_build_V' (md_ext_unwrap : md_ext -> FJ_md_ext) : forall gamma1 m ty mde' Ws W,
    FJ_override gamma1 m ty (md_ext_unwrap mde') Ws W -> 
    forall gamma gamma' ce ce' te te' te'' d T' mtye U U' Us Us' mce vars mtye' W' Ws'  vds,
      ty = (ty_def te'' d) -> 
      WF_mtype_ty_0_map gamma (ty_def te' d) T' ->
      mtype Empty m T' (mty mtye Us U) ->
      WF_mtype_U_map gamma mce mtye U U' ->
      WF_mtype_Us_map gamma mce mtye Us Us' ->
      WF_mtype_ext gamma mce mtye ->  
      build_te ce te te'' te' ->
      L_build_context ce gamma' ->
      (wf_class_ext gamma' ce'  te'' \/ wf_object_ext gamma' te'') -> 
      Meth_build_context ce mde' (update_list Empty vars) gamma1 -> 
      WF_Type gamma1 W ->
      List_P1 (WF_Type gamma1) Ws -> 
      Meth_WF_Ext gamma1 ce mde' ->
      mtype_build_mtye ce te W vds mde' mtye' ->
      mtype_build_tys ce te W vds mde' Ws Ws' ->
      mtype_build_tys ce te W vds mde' (W :: nil) (W' :: nil) ->
      exists V', WF_mtype_U_map gamma mce mtye' W' V' /\
        WF_mtype_Us_map gamma mce mtye' Ws' Us' /\
        subtype gamma V' U' /\ WF_mtype_ext gamma mce mtye'.
    intros; rewrite (build_te_refl _ _ _ _ H6) in *|-*.
    intros; generalize (WF_mtype_ty_0_map_id _ _ _ _ H1 (WF_mtype_ty_0_map_cl_refl _ _)); intros; 
      subst; destruct (H _ _ _ H2); subst.
    generalize (mtype_build_tys_refl _ _ _ _ _ _ _ H15); generalize (mtype_build_tys_refl _ _ _ _ _ _ _ H14);
      intros; subst; exists U'; injection H16; intros; subst; repeat split; eauto.
  Qed.

End FJ_build_V'_Sec.

Lemma Lem_2_9_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
  Lem_2_9_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
  unfold Lem_2_9_P; intros.
  rewrite (WF_mtype_ty_0_map_id _ _ _ _ H4 (WF_mtype_ty_0_map_cl_refl _ _)) in *|-*.
  destruct (In_m_mds_dec m ms) as [[mde' [ty' [vds' [e' In_m']]]] | NIn_m].
      (*** In m case ***)
  generalize (WF_CT _ _ CT_c); intros WF_c; inversion WF_c; subst.
  generalize (H15 _ In_m'); intro WF_m.
  inversion WF_m; subst.
  rewrite H25 in CT_c; inversion CT_c; subst.
  destruct (mtype_build_tys_tot ce te _ _ ty' vds' mde' 
    (map (fun vd' : VD => match vd' with | vd ty _ => ty end) vds') bld_te) as [tys' map_tys].
  destruct (mtype_build_tys_tot ce te _ _ ty' vds' mde' (ty' :: nil) bld_te) as [ty''' map_ty'].
  destruct (mtype_build_mtye_tot ce te _ _ ty' vds' mde' bld_te) as [mtye' build_mtye'].
  assert (exists ty'', ty''' = ty'' :: nil) as eq_ty''' by
    (generalize (mtype_build_tys_len _ _ _ _ _ _ _ map_ty'); clear;
      destruct ty'''; simpl; intros; try discriminate;
        destruct ty'''; simpl in *|-*; try discriminate; eexists; reflexivity);
    destruct eq_ty''' as [ty'' eq_ty''']; subst.
  eexists; eexists; eexists; split.
  apply FJ_mtype_Wrap; econstructor; try eassumption.
  apply WF_Type_invert in H19; inversion H19; subst.
  apply Ty_inject in H5; injection H5; intros; subst.
  eapply (build_V' _ _ _ _ _ _ H26 _ _ _ ce _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
    _ _ (refl_equal _) H H0 H1 H2 H3); try eassumption.
  right; auto.
  generalize H21; clear; induction vds'; intros; constructor; inversion H21; subst; 
    destruct a; auto.
  apply Ty_inject in H5; injection H5; intros; subst.
  eapply (build_V' _ _ _ _ _ _ H26 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
    _ _ (refl_equal _) H H0 H1 H2 H3); try eassumption.
  left; eauto.
  generalize H21; clear; induction vds'; intros; constructor; inversion H21; subst; 
    destruct a; auto.
  exists U; exists Us; exists mtye; split.
  apply FJ_mtype_Wrap; econstructor 2; try eassumption.
  eapply build_te_build_ty_0_id with (delta := Empty) (c := c) (d := d); eauto.
  rewrite (WF_mtype_ty_0_map_id _ _ _ _ H (WF_mtype_ty_0_map_cl_refl _ _)) in H0; assumption.
  eexists; repeat split; try eassumption.
  apply subtype_Wrap; constructor.
Qed.

Definition FJ_Lem_2_9 := FJ_subtype_rect _ Lem_2_9_H1 Lem_2_9_H2 Lem_2_9_H3.

Lemma FJ_WF_mtype_ty_0_map_id : forall delta S T T', FJ_WF_mtype_ty_0_map delta S T ->
  FJ_WF_mtype_ty_0_map delta S T' -> T = T'.
  unfold FJ_WF_mtype_ty_0_map; intros; inversion H; inversion H0; subst; assumption.
Qed.

Lemma FJ_WF_mtype_ty_0_map_tot : forall delta S T, 
  subtype delta S T -> forall T', FJ_WF_mtype_ty_0_map delta T T' ->
    exists S', FJ_WF_mtype_ty_0_map delta S S'.
  intros; exists S; constructor.
Qed.

Lemma FJ_WF_mtype_ty_0_map_cl_id : forall delta te te' d c, 
  FJ_WF_mtype_ty_0_map delta (ty_def te d) (ty_def te' (cl c)) -> d = cl c.
  intros; inversion H; subst.
  apply Ty_inject in H3; injection H3; auto.
Qed.

Lemma FJ_WF_mtype_ty_0_map_cl_id' : forall delta te d S', 
  FJ_WF_mtype_ty_0_map delta (ty_def te d) S' -> exists te', S' = ty_def te' d.
  intros; inversion H; subst.
  eexists; reflexivity.
Qed.

Lemma FJ_build_te_build_ty_0_id : forall (FJ_tye_unWrap : ty_ext -> FJ_ty_ext)
  ce c d te te' te'' te''' te4 delta, 
  FJ_build_te ce (FJ_tye_unWrap te) (FJ_tye_unWrap te4) (FJ_tye_unWrap te') -> 
  FJ_WF_mtype_ty_0_map delta (ty_def te' d) (ty_def te''' d) ->
  FJ_WF_mtype_ty_0_map delta (ty_def te (cl c)) (ty_def te'' (cl c)) ->
  FJ_mtype_build_te ce (FJ_tye_unWrap te'') (FJ_tye_unWrap te4) (FJ_tye_unWrap te''').
  unfold FJ_mtype_build_te; intros; destruct (FJ_tye_unWrap te''');  destruct (FJ_tye_unWrap te4); 
    destruct (FJ_tye_unWrap te''); constructor.
Qed.

Lemma FJ_WF_fields_map_update_list : forall delta Vars ty ty', 
  FJ_WF_fields_map (update_list delta Vars) ty ty' -> FJ_WF_fields_map delta ty ty'.
  intros; inversion H; subst; constructor.
Qed.

Lemma FJ_WF_mtype_ty_0_map_Weaken_update_list : forall delta Vars T T',
  FJ_WF_mtype_ty_0_map (update_list delta Vars) T T' -> 
  FJ_WF_mtype_ty_0_map delta T T'.
  intros; inversion H; subst; constructor.
Qed.

Lemma FJ_WF_mtype_U_map_Weaken_update_list : forall delta Vars mce mtye U U',
  FJ_WF_mtype_U_map (update_list delta Vars) mce mtye U U' -> 
  FJ_WF_mtype_U_map delta mce mtye U U'.
  intros; inversion H; subst; constructor.
Qed.

Lemma FJ_WF_mtype_Us_map_Weaken_update_list : forall delta Vars mce mtye Us Us',
  FJ_WF_mtype_Us_map (update_list delta Vars) mce mtye Us Us' -> 
  FJ_WF_mtype_Us_map delta mce mtye Us Us'.
  intros; inversion H; subst; constructor.
Qed.

Lemma FJ_WF_mtype_ty_0_map_total : forall delta S, 
  exists S', FJ_WF_mtype_ty_0_map delta S S'.
  intros; exists S; constructor.
Qed.

Lemma FJ_WF_mtype_ext_update_list_id : forall delta Vars mce mtye, 
  FJ_WF_mtype_ext (update_list delta Vars) mce mtye -> FJ_WF_mtype_ext delta mce mtye.
  intros; inversion H; subst; constructor.
Qed.

Lemma FJ_WF_mtype_Us_map_len : forall delta mce mtye Ds Ds', 
  FJ_WF_mtype_Us_map delta mce mtye Ds Ds' -> length Ds = length Ds'.
  intros; inversion H; subst; reflexivity.
Qed.

Lemma FJ_mtype_build_tys_len : forall ce te T0 vds me tys tys', 
  FJ_mtype_build_tys ce te T0 vds me tys tys' -> length tys = length tys'.
  intros; inversion H; subst; reflexivity.
Qed.

Lemma FJ_methods_build_te_id : forall ce te te' te'' te''', 
  FJ_mtype_build_te ce te te' te'' -> FJ_mbody_build_te ce te te' te''' -> te'' = te'''.
  destruct te''; destruct te'''; reflexivity.
Qed.

Lemma FJ_build_te_id : forall ce te te' te'',
  FJ_mbody_build_te ce te te'' te' -> 
  FJ_build_te ce te te'' te'.
  intros; destruct te; destruct te'; destruct te''.
  constructor.
Qed.

Lemma FJ_WF_fields_map_tot : forall gamma te c, 
  exists te', FJ_WF_fields_map gamma (ty_def te c) (ty_def te' c).
  intros; exists te; constructor.
Qed.

Lemma FJ_fields_build_te_tot : forall ce te te'' te3 te4, FJ_build_te ce te te3 te4 ->
  exists te', FJ_fields_build_te ce te te'' te'.
  intros; exists te; constructor.
Qed.

Lemma FJ_fields_build_tys_tot : forall te ce tys te' te'' , FJ_build_te ce te te' te'' ->
  exists tys', FJ_fields_build_tys te ce tys tys'.
  intros; exists tys; constructor.
Qed.

Lemma FJ_WF_fields_map_id'' : forall ty gamma ty' ty'', 
  FJ_WF_fields_map gamma ty ty' ->
  FJ_WF_fields_map gamma ty ty'' -> ty' = ty''.
  intros; inversion H; inversion H0; subst; assumption.
Qed.

Lemma FJ_fields_build_te_id' (FJ_tye_unWrap : ty_ext -> FJ_ty_ext) :
  forall gamma ce c d te te' te'' te3 te4 te5,
    FJ_build_te ce (FJ_tye_unWrap te) (FJ_tye_unWrap te5) (FJ_tye_unWrap te') -> 
    FJ_WF_fields_map gamma (ty_def te' d) (ty_def te'' d) -> 
    FJ_WF_fields_map gamma (ty_def te (cl c)) (ty_def te3 (cl c)) ->
    FJ_fields_build_te ce (FJ_tye_unWrap te3) (FJ_tye_unWrap te5) (FJ_tye_unWrap te4) ->
    FJ_tye_unWrap te'' = FJ_tye_unWrap te4.
  intros; destruct (FJ_tye_unWrap te''); destruct (FJ_tye_unWrap te4); 
    reflexivity.
Qed.

Variable (WF_Object_ext_Update_Vars_id : forall delta Vars te,
  wf_object_ext (update_list delta Vars) te -> 
  wf_object_ext delta te).

Lemma FJ_WF_Object_ext_Update_Vars_id : forall delta Vars te,
  FJ_wf_object_ext (update_list delta Vars) te -> 
  FJ_wf_object_ext delta te.
  unfold FJ_wf_object_ext; auto.
Qed.

Definition WF_Class_ext_Update_Vars_id_Q delta' l te (wf_l : wf_class_ext delta' l te) :=
  forall delta Vars, delta' = (update_list delta Vars) -> wf_class_ext delta l te.

Lemma FJ_WF_Class_ext_Update_Vars_id : forall delta' l te (wf_l : FJ_wf_class_ext delta' l te)
  delta Vars, delta' = (update_list delta Vars) -> FJ_wf_class_ext delta l te.
  auto.
Qed.

Lemma WF_Type_update_list_id_H1 : forall gamma te wf_obj, 
  WF_Type_update_list_id_P _ _ (WF_Obj gamma te wf_obj).
  unfold WF_Type_update_list_id_P; intros; subst.
  apply FJ_WF_Type_Wrap; constructor; eauto.
Qed.

Lemma WF_Type_update_list_id_H2 : forall gamma c cld te CT_c wf_cld_ext,
  WF_Class_ext_Update_Vars_id_Q _ _ _ wf_cld_ext -> 
  WF_Type_update_list_id_P _ _ (WF_Class gamma c cld te CT_c wf_cld_ext).
  unfold WF_Type_update_list_id_P; intros; subst.
  unfold WF_Class_ext_Update_Vars_id_Q in H; subst.
  apply FJ_WF_Type_Wrap; econstructor; eauto.
Qed.

Definition FJ_WF_Type_update_list_id := 
  FJ_WF_Type_rect' _ _ WF_Type_update_list_id_H1 WF_Type_update_list_id_H2.

Variable (WF_Obj_ext_Lem : forall gamma gamma0 te0 te' te'' ce c0 fds k' mds,
  L_build_context ce gamma0 -> mtype_build_te ce te0 te' te'' ->
  wf_object_ext gamma0 te' -> wf_class_ext gamma ce te0 ->
  CT c0 = Some (cld ce c0 (ty_def te' Object) fds k' mds) ->
  wf_object_ext gamma te'').

Lemma FJ_WF_Obj_ext_Lem : forall gamma te'', FJ_wf_object_ext gamma te''.
  unfold FJ_wf_object_ext; intros; auto.
Qed.

Definition WF_Type_par_Lem_P delta ty' (WF_ty' : WF_Type delta ty') :=
  forall gamma te0 te' te'' ce c fds k' mds, 
    ty' = ty_def te0 (cl c) -> L_build_context ce gamma -> 
    mtype_build_te ce te0 te' te'' -> 
    wf_object_ext gamma te' -> CT c = Some (cld ce c (ty_def te' Object) fds k' mds) -> 
    wf_object_ext delta te''.

Lemma WF_Type_par_Lem_H1 : forall gamma te wf_obj, 
  WF_Type_par_Lem_P _ _ (WF_Obj gamma te wf_obj).
  unfold WF_Type_par_Lem_P; intros; subst.
  apply Ty_inject in H; inversion H.
Qed.

Lemma WF_Type_par_Lem_H2 : forall gamma c cld te CT_c wf_cld_ext (T : True),
  WF_Type_par_Lem_P _ _ (WF_Class gamma c cld te CT_c wf_cld_ext).
  unfold WF_Type_par_Lem_P; intros; subst.
  apply Ty_inject in H; injection H; intros; subst.
  rewrite CT_c in H3; injection H3; intros; subst; clear H H3.
  eauto.
Qed.

Definition FJ_WF_Type_par_Lem := 
  FJ_WF_Type_rect' _ (fun x y z a => True) WF_Type_par_Lem_H1 WF_Type_par_Lem_H2 (fun x y z a => I).

Definition WF_cld_ext_Lem_Q gamma ce te0 (wf_cld' : wf_class_ext gamma ce te0) :=
  forall te'' c0 fds k' mds c1 gamma0 ce' te' cld',
    wf_class_ext gamma0 ce' te' -> 
    CT c0 = Some cld' ->
    cld_ce cld' = ce' ->
    L_build_context ce gamma0 -> 
    mtype_build_te ce te0 te' te'' ->
    CT c1 = Some (cld ce c1 (ty_def te' (cl c0)) fds k' mds) ->
    wf_class_ext gamma ce' te''.

Lemma FJ_WF_Cld_ext_Lem : forall gamma cld te'', FJ_wf_class_ext gamma cld te''.
  unfold FJ_wf_class_ext; intros; auto.
Qed.

Definition WF_Type_par_Lem_P' delta ty' (WF_ty' : WF_Type delta ty') :=
  forall gamma te0 te' te'' ce c c0 fds k' mds cld0 (CT_c : CT c = Some cld0), 
    ty' = ty_def te0 (cl c0) -> L_build_context ce gamma -> 
    mtype_build_te ce te0 te' te'' -> 
    wf_class_ext gamma (cld_ce cld0) te' -> CT c0 = Some (cld ce c0 (ty_def te' (cl c)) fds k' mds) -> 
    wf_class_ext delta (cld_ce cld0) te''.

Lemma WF_Type_par_Lem'_H1 : forall gamma te wf_obj, 
  WF_Type_par_Lem_P' _ _ (WF_Obj gamma te wf_obj).
  unfold WF_Type_par_Lem_P'; intros; subst.
  apply Ty_inject in H; inversion H.
Qed.

Lemma WF_Type_par_Lem'_H2 : forall gamma c cld te CT_c wf_cld_ext,
  WF_cld_ext_Lem_Q _ _ _ wf_cld_ext -> 
  WF_Type_par_Lem_P' _ _ (WF_Class gamma c cld te CT_c wf_cld_ext).
  unfold WF_Type_par_Lem_P'; intros; subst.
  apply Ty_inject in H0; injection H0; intros; subst.
  rewrite CT_c in H4; injection H4; intros; subst; clear H0 H4.
  simpl in *|-*.
  eapply H.
  apply H3.
  apply CT_c0.
  reflexivity.
  assumption.
  assumption.
  eassumption.
Qed.

Definition FJ_WF_Type_par_Lem' := 
  FJ_WF_Type_rect' _ _ WF_Type_par_Lem'_H1 WF_Type_par_Lem'_H2.

Variable (WF_Type_par_Lem : forall delta ty' WF_ty', 
  WF_Type_par_Lem_P delta ty' WF_ty')
(WF_Type_par_Lem' : forall delta ty' WF_ty', 
  WF_Type_par_Lem_P' delta ty' WF_ty').

Lemma WF_Type_par_H1 : forall gamma te wf_obj, 
  WF_Type_par_P _ _ (WF_Obj gamma te wf_obj).
  unfold WF_Type_par_P; intros; subst.
  apply Ty_inject in H; injection H; intros; subst.
  apply FJ_WF_Type_Wrap; constructor; eauto.
  eapply WF_Type_par_Lem; eauto.
Qed.

Lemma WF_Type_par_H2 : forall gamma c cld te CT_c wf_cld_ext (T : True),
  WF_Type_par_P _ _ (WF_Class gamma c cld te CT_c wf_cld_ext).
  unfold WF_Type_par_P; intros; subst.
  apply Ty_inject in H; injection H; intros; subst.
  apply FJ_WF_Type_Wrap; econstructor; eauto.
  eapply WF_Type_par_Lem'; eauto.
Qed.

Definition FJ_WF_Type_par := 
  FJ_WF_Type_rect' _ (fun a b c d => True) WF_Type_par_H1 WF_Type_par_H2 (fun a b c d => I).

Lemma fields_id_H1 : forall te gamma, fields_id_P _ _ _ (fields_Obj te gamma).
  unfold fields_id_P; intros.
  apply Ty_inject in H; injection H; intros; subst.
  apply Fields_invert in H0; inversion H0; subst.
  reflexivity.
  apply Ty_inject in H1; inversion H1.
Qed.

Lemma fields_id_H2 : forall gamma ce c d c_fds d_fds k' mds te te' te'' tys c_eq 
  te_upd par_fds build_tys,
  fields_id_P _ _ _ par_fds -> 
  fields_id_P _ _ _ (fields_cl gamma ce c d c_fds d_fds k' mds te te' te'' tys
    c_eq te_upd par_fds build_tys).
  unfold fields_id_P; intros.
  apply Ty_inject in H0; injection H0; intros; subst.
  apply Fields_invert in H1; inversion H1; subst.
  apply Ty_inject in H4; inversion H4.
  apply Ty_inject in H2; inversion H2; subst.
  rewrite c_eq in H3; injection H3; intros; subst.
  rewrite <- (fields_build_te_id _ _ _ _ _ te_upd H4) in H5.
  rewrite (H _ _ _ (refl_equal _) H5).
  rewrite (fields_build_tys_id _ _ _ _ _ H7 build_tys).
  reflexivity.
Qed.

Definition FJ_fields_id := FJ_fields_rect' _ fields_id_H1 fields_id_H2.

Lemma Subtype_Update_list_id_H1 : forall (ty : Ty) (gamma : Context), 
  Subtype_Update_list_id_P _ _ _ (sub_refl ty gamma).
  unfold Subtype_Update_list_id_P; intros; apply subtype_Wrap.
  constructor.
Qed.

Lemma Subtype_Update_list_id_H2 : forall c d e gamma sub_c sub_d, 
  Subtype_Update_list_id_P _ _ _ sub_c -> 
  Subtype_Update_list_id_P _ _ _ sub_d -> 
  Subtype_Update_list_id_P _ _ _ (sub_trans c d e gamma sub_c sub_d).
  unfold Subtype_Update_list_id_P; intros; apply subtype_Wrap.
  econstructor 2.
  eapply H; eauto.
  eauto.
Qed.

Lemma Subtype_Update_list_id_H3 : forall ce c d fs k' ms te te' te'' gamma CT_c bld_te,
  Subtype_Update_list_id_P _ _ _ (sub_dir ce c d fs k' ms te te' te'' gamma CT_c bld_te).
  unfold Subtype_Update_list_id_P; intros; apply subtype_Wrap.
  econstructor 3; eauto.
Qed.

Definition FJ_Subtype_Update_list_id := 
  FJ_subtype_rect _ Subtype_Update_list_id_H1 Subtype_Update_list_id_H2 Subtype_Update_list_id_H3.

Lemma pres_H2 : forall m c te xs e es ds mce mbe mbody_m,
  preservation _ _ (R_Invk m c te xs e es ds mce mbe mbody_m).
  unfold preservation; intros until c0; intros wf_m_call.
  apply FJ_E_WF_invert in wf_m_call; inversion wf_m_call; subst;
    apply EWrap_inject in H; inversion H; subst; clear H.
  rename H0 into wf_new_c; apply FJ_E_WF_invert in wf_new_c; inversion wf_new_c;
    subst; apply EWrap_inject in H; inversion H; subst; clear H.
  destruct (Lem_2_12 _ _ _ _ _ _ mbody_m _ _ _ _ _ _ _ H2 H1 H0 H7 H3 H4) as 
    [S [Vars' [N [zip_eq [sub_N [WF_N [sub_S [WF_e WF_mbe]]]]]]]].
  destruct (Lem_2_11 _ _ _ WF_e _ _ _ _ _ _ (refl_equal _) zip_eq 
    (cons_P2' _ _ _ _ _ (E_WF_Wrap _ _ _ wf_new_c) H5)) as [S' [WF_e_trans sub_S']].
  constructor; eauto.
  eapply subtype_Wrap; eapply sub_trans; eauto.
  eexists; split; eauto.
  eapply subtype_Wrap; eapply sub_trans; eauto.
Qed.

Definition FJ_pres e e' (red_e : FJ_Reduce e e') := 
  FJ_Reduce_rect' _ pres_H1 pres_H2 e e' red_e.

Definition Weaken_mtype_P delta m ty mty' (mtype_m : mtype delta m ty mty') :=
  forall gamma, delta = Empty -> mtype gamma m ty mty'.

Variable (Weaken_mtype : forall gamma m ty mty' mtype_m, Weaken_mtype_P gamma m ty mty' mtype_m).

Lemma Weaken_mtype_H1 : forall ce m c d fds k' mds ty ty' vds e me te gamma tys' mtye
  CT_c In_m build_tys build_ty build_mtye, 
  Weaken_mtype_P _ _ _ _ (mtype_fnd ce m c d fds k' mds ty ty' 
    vds e me te gamma tys' mtye CT_c In_m build_tys build_ty build_mtye).
  unfold Weaken_mtype_P; intros; subst.
  apply FJ_mtype_Wrap.
  econstructor; eauto.
Qed.

Lemma Weaken_mtype_H2 : forall ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m 
  build_te par_mtype, Weaken_mtype_P _ _ _ _ par_mtype -> 
  Weaken_mtype_P _ _ _ _ (mtype_not_fnd ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype).
  unfold Weaken_mtype_P; intros; subst.
  apply FJ_mtype_Wrap.
  econstructor 2; eauto.
Qed. 

Definition FJ_Weaken_mtype := mtype_rect' _ Weaken_mtype_H1 Weaken_mtype_H2.

Definition C_preservation e e' (red_e : C_Reduce e e') := 
  forall gamma c, E_WF gamma e c -> exists c', E_WF gamma e' c' /\ subtype gamma c' c.

Definition Reduce_List_preservation es es' (red_es : C_Reduce_List es es') :=
  forall gamma cs, List_P2' (E_WF gamma) es cs -> exists cs', List_P2' (E_WF gamma) es' cs' /\
    List_P2' (subtype gamma) cs' cs.

Lemma C_preservation_H1 : forall e e' f Red_e_e', C_preservation _ _ Red_e_e' -> 
  C_preservation _ _ (RC_Field e e' f Red_e_e').
  unfold C_preservation; intros.
  apply FJ_E_WF_invert in H0; inversion H0; apply EWrap_inject in H1; try discriminate; 
    injection H1; intros; subst.
  destruct (H _ _ H2) as [c' [WF_e' sub_c'_c]].
  exists c; split.
  destruct (Lem_2_8 _ _ _ sub_c'_c _ _ H3 H4) as [c'' [map_c'_c'' [fds' [fds_c'' nth_fds']]]].
  apply E_WF_Wrap; econstructor; eauto.
  eapply subtype_Wrap; constructor.
Qed.

Lemma C_preservation_H2 : forall e e' mce m es Red_e_e', C_preservation _ _ Red_e_e' -> 
  C_preservation _ _ (RC_Invk_Recv e e' mce m es Red_e_e').
  unfold C_preservation; intros.
  apply FJ_E_WF_invert in H0; inversion H0; apply EWrap_inject in H1; try discriminate; 
    injection H1; intros; subst.
  destruct (H _ _ H2) as [c' [WF_e' sub_c'_c]].
  destruct (WF_mtype_ty_0_map_total gamma c' ty_0 sub_c'_c ty_0' H3) as [c'' map_c'_c''].
  destruct (Lem_2_9 _ _ _ sub_c'_c _ _ _ _ _ _ _ _ _ H3 H4 H6 H5 H9 map_c'_c'') as 
    [V [Vs [mtye' [mtype_c' [V' [map_V_V' [map_Vs_Us [sub_V'_U' WF_mce_mtye']]]]]]]]. 
  exists V'; split; auto.
  apply E_WF_Wrap; econstructor; eauto.
Qed.

Lemma C_preservation_H3 : forall e mce m es es' Red_es_es', Reduce_List_preservation _ _ Red_es_es' ->
  C_preservation _ _ (RC_Invk_Arg e mce m es es' Red_es_es').
  unfold C_preservation; unfold Reduce_List_preservation; intros.
  apply FJ_E_WF_invert in H0; inversion H0; apply EWrap_inject in H1; try discriminate; 
    injection H1; intros; subst.
  destruct (H _ _ H7) as [Ss' [WF_es' sub_Ss_Ss']].
  exists c; split.
  apply E_WF_Wrap; econstructor; eauto.
  generalize Us' H8 subtype_Wrap Ss' sub_Ss_Ss'; clear; intros Us' H8; induction H8; intros;
    inversion sub_Ss_Ss'; subst; constructor.
  apply subtype_Wrap; econstructor 2; eauto.
  eapply IHList_P2'; eauto.
  apply subtype_Wrap; econstructor.
Qed.

Lemma C_preservation_H4 : forall ty es es' Red_es_es', Reduce_List_preservation _ _ Red_es_es' -> 
  C_preservation _ _ (RC_New_Arg ty es es' Red_es_es').
  unfold C_preservation; unfold Reduce_List_preservation; intros.
  apply FJ_E_WF_invert in H0; inversion H0; apply EWrap_inject in H1; try discriminate; 
    injection H1; intros; subst.
  destruct (H _ _ H4) as [Ss' [WF_es' sub_Ss_Ss']].
  exists (ty_def te cl0); split.
  apply E_WF_Wrap; econstructor; eauto.
  generalize fds H5 subtype_Wrap Ss' sub_Ss_Ss'; clear; intros fds H5; induction H5; intros;
    inversion sub_Ss_Ss'; subst; constructor.
  destruct b; apply subtype_Wrap; econstructor 2; eauto.
  eapply IHList_P2'; eauto.
  apply subtype_Wrap; econstructor.
Qed.

Lemma C_preservation_H5 : forall e e' es Red_e_e', C_preservation _ _ Red_e_e' ->
  Reduce_List_preservation _ _ (Reduce_T e e' es Red_e_e').
  unfold C_preservation; unfold Reduce_List_preservation; intros.
  inversion H0; subst.
  destruct (H _ _ H3) as [c' [WF_e' sub_c'_b]].
  exists (c' :: Bs); split; constructor; eauto.
  generalize (subtype_Wrap); clear; induction Bs; constructor; eauto.
Qed.

Lemma C_preservation_H6 : forall e es es' Red_es_es', Reduce_List_preservation _ _ Red_es_es' -> 
  Reduce_List_preservation _ _ (Reduce_P e es es' Red_es_es').
  unfold Reduce_List_preservation; intros.
  inversion H0; subst.
  destruct (H _ _ H5) as [Bs' [WF_es' sub_Bs'_Bs]].
  exists (b :: Bs'); split; constructor; eauto.
Qed.

Definition FJ_C_preservation := FJ_Congruence_Reduce_rect' _ _ C_preservation_H1 C_preservation_H2
  C_preservation_H3 C_preservation_H4.

Definition FJ_C_List_preservation := Reduce_List_rect' _ _ C_preservation_H5 C_preservation_H6.

Variable (subexpression : E -> E -> Prop)
  (subexpression_list : E -> Es -> Prop).

Inductive FJ_subexpression : E -> E -> Prop :=
  subexp_refl : forall e, FJ_subexpression e e
| subexp_fd_access : forall e e' f, subexpression e e' -> FJ_subexpression e (fd_access e' f)
| subexp_m_call_inv : forall mce e m es e', subexpression e e' -> 
  FJ_subexpression e (m_call mce e' m es)
| subexp_m_call_arg : forall mce e m es e', subexpression_list e es ->
  FJ_subexpression e (m_call mce e' m es)
| subexp_new : forall ty es e, subexpression_list e es ->
  FJ_subexpression e (new ty es).

Inductive  FJ_subexpression_list : E -> Es -> Prop :=
  subexp_t : forall e e' es, subexpression e e' -> FJ_subexpression_list e (e' :: es)
| subexp_p : forall e e' es, subexpression_list e es -> FJ_subexpression_list e (e' :: es).

Variable (subexp_Wrap : forall e e', FJ_subexpression e e' -> subexpression e e')
  (subexp_list_Wrap : forall es es', FJ_subexpression_list es es' -> subexpression_list es es')
  (subexp_invert : forall e (e' : FJ_E), subexpression e e' -> FJ_subexpression e e').
Coercion subexp_Wrap : FJ_subexpression >-> subexpression.
Coercion subexp_list_Wrap : FJ_subexpression_list >-> subexpression_list.

Definition progress_1_P gamma e ty (WF_e : E_WF gamma e ty) := forall ty es f, 
  subexpression (fd_access (new ty es) f) e -> exists fds, fields Empty ty fds /\ 
    exists i, exists ty', nth_error fds i = Some (fd ty' f).

Definition progress_1_list_P gamma es tys (WF_es : List_P2' (E_WF gamma) es tys) :=
  forall ty es' f, subexpression_list (fd_access (new ty es') f) es -> 
    exists fds, fields Empty ty fds /\ exists i, exists ty', nth_error fds i = Some (fd ty' f).

Lemma progress_1_H1 : forall gamma x ty lookup_x, progress_1_P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)).
  unfold progress_1_P; intros.
  apply subexp_invert in H; inversion H; try (apply EWrap_inject in H2; discriminate);
    try (apply EWrap_inject in H0; discriminate).
Qed.

Lemma progress_1_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, progress_1_P _ _ _ WF_e ->
  progress_1_P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
  unfold progress_1_P; intros.
  apply subexp_invert in H0; inversion H0; try (apply EWrap_inject in H3; discriminate);
    try (apply EWrap_inject in H1; discriminate).
  apply EWrap_inject in H3; injection H3; intros; subst; clear H3.
  apply FJ_E_WF_invert in WF_e; inversion WF_e; try (apply EWrap_inject in H1; discriminate);
    subst.
  apply EWrap_inject in H1; injection H1; intros; subst.
  exists fds; split; eauto.
  destruct (WF_fields_map_id' _ _ _ _ ty_map0) as [te' eq_te']; subst.
  exists i; generalize fds' i fds nth_fds 
    (WF_fields_map_id _ _ _ H3 _ _ _ _ _ (refl_equal _) (refl_equal _) fds_ty'); clear; 
      induction fds'; intros; destruct i; simpl in nth_fds; try discriminate.
  injection nth_fds; intros; subst; destruct fds; simpl in H; try discriminate.
  destruct f0; simpl in *|-*; injection H; intros; subst; eexists; reflexivity.
  destruct fds; simpl in H; try discriminate; injection H; intros; eauto.
  destruct a; destruct f0; subst.
  simpl; eauto.
  apply EWrap_inject in H1; injection H1; intros; subst.
  destruct (H _ _ _ H3) as [fds'' [fields_ty0 [i' [ty''' nth_fds'']]]].
  eexists; eauto.
Qed.

Lemma progress_1_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U 
  WF_es sub_Ss_Us' WF_mtye, progress_1_P _ _ _ WF_e_0 -> progress_1_list_P _ _ _ WF_es ->
  progress_1_P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
    mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
  unfold progress_1_P; unfold progress_1_list_P; intros.
  apply subexp_invert in H1; inversion H1; try (apply EWrap_inject in H2; discriminate);
    try (apply EWrap_inject in H4; discriminate).
  apply EWrap_inject in H2; injection H2; intros; subst; eauto.
  apply EWrap_inject in H2; injection H2; intros; subst; eauto.
Qed.

Lemma progress_1_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
  progress_1_list_P _ _ _ WF_es -> 
  progress_1_P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es  WF_cl fds_cl WF_es sub_fds)).
  unfold progress_1_P; unfold progress_1_list_P; intros.
  apply subexp_invert in H0; inversion H0; try (apply EWrap_inject in H3; discriminate);
    try (apply EWrap_inject in H1; discriminate).
  apply EWrap_inject in H1; injection H1; intros; subst; eauto.
Qed.

Lemma FJ_subexpression_list_nil : forall e , ~  (FJ_subexpression_list e nil).
  clear; unfold not; intros; inversion H; subst.
Qed.

Lemma FJ_subexpression_list_destruct : forall e e' es, FJ_subexpression_list e (e' :: es) -> 
  (subexpression e e') \/ (subexpression_list e es).
  clear; intros; inversion H; subst; tauto.
Qed.

Variables (subexpression_list_nil : forall e, ~ subexpression_list e nil)
  (subexpression_list_destruct : forall e e' es, subexpression_list e (e' :: es) -> 
    (subexpression e e') \/ (subexpression_list e es)).

Lemma progress_1_H5 : forall gamma, progress_1_list_P gamma nil nil (nil_P2' (E_WF gamma)).
  unfold progress_1_list_P; intros.
  assert (exists es : Es, es = nil) as H1 by (eexists; reflexivity); intros; destruct H1 as [es es_eq]; 
    rewrite <- es_eq in H; elimtype False; subst; eapply subexpression_list_nil; eauto.
Qed.

Lemma progress_1_H6 : forall gamma e es ty tys WF_e WF_es,
  progress_1_P gamma e ty WF_e -> progress_1_list_P gamma es tys WF_es -> 
  progress_1_list_P _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
  unfold progress_1_P; unfold progress_1_list_P; intros.
  destruct (subexpression_list_destruct _ _ _ H1) as [In | NIn]; eauto.
Qed.

Definition progress_1 := FJ_FJ_E_WF_rect' _ _ 
  progress_1_H1 progress_1_H2 progress_1_H3
  progress_1_H4 progress_1_H5 progress_1_H6.

Definition progress_2_P gamma e ty (WF_e : E_WF gamma e ty) := forall ty' mce m es ds, 
  subexpression (m_call mce (new ty' es) m ds) e -> exists mbe, exists xs, exists e0,
    mbody Empty mce m ty' (mb mbe xs e0) /\ length xs = length ds.

Definition progress_2_list_P gamma es tys (WF_es : List_P2' (E_WF gamma) es tys) :=
  forall ty' mce m es' ds, subexpression_list (m_call mce (new ty' es') m ds) es -> 
    exists mbe, exists xs, exists e0, mbody Empty mce m ty' (mb mbe xs e0) /\ length xs = length ds.

Lemma progress_2_H1 : forall gamma x ty lookup_x, progress_2_P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)).
  unfold progress_2_P; intros.
  apply subexp_invert in H; inversion H; try (apply EWrap_inject in H2; discriminate);
    try (apply EWrap_inject in H0; discriminate).
Qed.

Lemma progress_2_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, progress_2_P _ _ _ WF_e ->
  progress_2_P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
  unfold progress_2_P; intros.
  apply subexp_invert in H0; inversion H0; try (apply EWrap_inject in H3; discriminate);
    try (apply EWrap_inject in H1; discriminate).
  apply EWrap_inject in H1; injection H1; intros; subst; eauto.
Qed.

Variable (map_mbody_tot : forall ce te mce me ty vds tys tys' e,
  mtype_build_tys ce te ty vds me tys tys' -> exists e', map_mbody ce te mce me e e')
(WF_mtype_ty_0_map_Empty_refl : forall gamma te c ty, WF_mtype_ty_0_map gamma (ty_def te c) ty -> ty = ty_def te c)
(mtype_mbody_build_te : forall ce te te' te'', mtype_build_te ce te te' te'' -> mbody_build_te ce te te' te'')
(build_mb_ext_tot : forall ce te mce me ty vds tys tys',
  mtype_build_tys ce te ty vds me tys tys' -> exists mb, build_mb_ext ce te mce me mb).

Lemma FJ_map_mbody_tot : forall ce te0 mce me ty vds tys tys' e,
  FJ_mtype_build_tys ce te0 ty vds me tys tys' -> 
  exists e', FJ_map_mbody ce te0 mce me e e'.
  clear; intros; eexists; constructor.
Qed.      

Lemma FJ_WF_mtype_ty_0_map_Empty_refl : forall gamma te c ty, 
  FJ_WF_mtype_ty_0_map gamma (ty_def te c) ty -> ty = ty_def te c.
  clear; intros; inversion H; subst; reflexivity.
Qed.

Lemma FJ_mtype_mbody_build_te : forall ce te te' te'', FJ_mtype_build_te ce te te' te'' -> FJ_mbody_build_te ce te te' te''.
  clear; intros; inversion H; subst; constructor.
Qed.

Definition mtype_implies_mbody_P delta m ty mty' (mtype_m : mtype delta m ty mty') :=
  forall mce cl te mtye Us U, delta = Empty -> mty' = (mty mtye Us U) -> ty = (ty_def te cl) ->
    exists mbe, exists xs, exists e, mbody Empty mce m (ty_def te cl) (mb mbe xs e) /\ length xs = length Us.

Lemma mtype_implies_mbody_H1 : forall ce m c d fds k' mds ty ty' vds e me te gamma tys' mtye
  CT_c In_m build_tys build_ty build_mtye, 
  mtype_implies_mbody_P _ _ _ _ (mtype_fnd ce m c d fds k' mds ty ty' 
    vds e me te gamma tys' mtye CT_c In_m build_tys build_ty build_mtye).
  unfold mtype_implies_mbody_P; intros; subst.
  inversion H0; apply Ty_inject in H1; injection H1; intros; subst.
  destruct (map_mbody_tot _ _ mce me _ _ _ _ e build_tys) as [e' map_e'_ext'].
  destruct (build_mb_ext_tot _ _ mce me _ _ _ _ build_tys) as [mbe' build_mbe']; exists mbe'.
  exists (map (fun vd' => match vd' with | vd _ x => x end) vds); exists e'; split.
  econstructor; eauto.
  generalize Us (mtype_build_tys_len _ _ _ _ _ _ _ build_tys); clear; induction vds; 
    destruct Us; simpl; intros; try discriminate; auto.
Qed.

Lemma mtype_implies_mbody_H2 : forall ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m 
  build_te par_mtype, mtype_implies_mbody_P _ _ _ _ par_mtype -> 
  mtype_implies_mbody_P _ _ _ _ (mtype_not_fnd ce m c d fds k' mds mty' te te' te'' gamma CT_c NIn_m build_te par_mtype).
  unfold mtype_implies_mbody_P; intros; subst.
  apply Ty_inject in H2; injection H2; intros; subst.
  destruct (H mce _ _ _ _ _ (refl_equal _) (refl_equal _) (refl_equal _)) as [mbe [xs [e [mbody_m eq_len]]]].
  exists mbe; exists xs; exists e; split; eauto.
  econstructor; eauto.
Qed.

Lemma FJ_build_te_id' : forall (ce : FJ_cld_ext) (te te' te'' : FJ_ty_ext),
  FJ_mbody_build_te ce te te'' te' ->
  FJ_build_te ce te te'' te'.
  intros; destruct te; destruct te'; destruct te''; constructor.
Qed.

Lemma FJ_WF_fields_map_id : forall gamma ty, FJ_WF_fields_map gamma (TyWrap ty) (TyWrap ty).
  intros; constructor.
Qed.

Lemma FJ_build_mb_ext_tot : forall ce te mce me ty vds tys tys',
  FJ_mtype_build_tys ce te ty vds me tys tys' ->
  exists mb : FJ_mb_ext, FJ_build_mb_ext ce te mce me mb.
  intros; exists tt; constructor.
Qed.

Definition FJ_mtype_implies_mbody := mtype_rect' _ mtype_implies_mbody_H1 mtype_implies_mbody_H2.

Variable mtype_implies_mbody : forall delta m ty mty' mtype_m, mtype_implies_mbody_P delta m ty mty' mtype_m.

Lemma progress_2_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U 
  WF_es sub_Ss_Us' WF_mtye, progress_2_P _ _ _ WF_e_0 -> progress_2_list_P _ _ _ WF_es ->
  progress_2_P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
    mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
  unfold progress_2_P; unfold progress_2_list_P; intros.
  apply subexp_invert in H1; inversion H1; try (apply EWrap_inject in H2; discriminate);
    try (apply EWrap_inject in H4; discriminate).
  apply EWrap_inject in H4; injection H4; intros; subst; eauto.
  apply FJ_E_WF_invert in WF_e_0; inversion WF_e_0; subst;
    try (apply EWrap_inject in H2; discriminate).
  apply EWrap_inject in H2; injection H2; intros; subst; auto.
  rewrite (WF_mtype_ty_0_map_Empty_refl _ _ _ _ ty_0_map) in *|-*.
  destruct (mtype_implies_mbody _ _ _ _ mtype_m mce _ _ _ _ _ (refl_equal _) (refl_equal _)
    (refl_equal _)) as [mbe' [xs' [e' [mbody_m len_xs]]]].
  exists mbe'; exists xs'; exists e'; split; auto.
  generalize xs' Ss Us Us' (WF_mtype_Us_map_len _ _ _ _ _ map_Us) len_xs WF_es sub_Ss_Us'; clear;
    induction es; intros.
  inversion WF_es; subst; inversion sub_Ss_Us'; destruct Us; destruct xs'; simpl in *|-*; try discriminate;
    auto.
  subst; simpl in H; discriminate.
  inversion WF_es; subst; inversion sub_Ss_Us'; subst; destruct Us; destruct xs'; simpl in *|-*; try discriminate;
    auto.
  injection H; injection len_xs; intros.
  rewrite (IHes _ _ _ _ H1 H0 H4 H6); reflexivity.
  apply EWrap_inject in H2; injection H2; intros; subst; eauto.
  apply EWrap_inject in H2; injection H2; intros; subst; eauto.
Qed.

Lemma progress_2_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
  progress_2_list_P _ _ _ WF_es -> 
  progress_2_P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es  WF_cl fds_cl WF_es sub_fds)).
  unfold progress_2_P; unfold progress_2_list_P; intros.
  apply subexp_invert in H0; inversion H0; try (apply EWrap_inject in H3; discriminate);
    try (apply EWrap_inject in H1; discriminate).
  apply EWrap_inject in H1; injection H1; intros; subst; eauto.
Qed.

Lemma progress_2_H5 : forall gamma, progress_2_list_P gamma nil nil (nil_P2' (E_WF gamma)).
  unfold progress_2_list_P; intros.
  assert (exists es : Es, es = nil) as H1 by (eexists; reflexivity); intros; destruct H1 as [es es_eq]; 
    rewrite <- es_eq in H; elimtype False;  subst; eapply subexpression_list_nil; eauto.
Qed.

Lemma progress_2_H6 : forall gamma e es ty tys WF_e WF_es,
  progress_2_P gamma e ty WF_e -> progress_2_list_P gamma es tys WF_es -> 
  progress_2_list_P _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
  unfold progress_2_P; unfold progress_2_list_P; intros.
  destruct (subexpression_list_destruct _ _ _ H1) as [In | NIn]; eauto.
Qed.

Definition FJ_progress_2 := FJ_FJ_E_WF_rect' _ _ 
  progress_2_H1 progress_2_H2 progress_2_H3
  progress_2_H4 progress_2_H5 progress_2_H6.

End Preservation.

End FJ_definitions.
