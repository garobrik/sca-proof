Section State.
  
  Require Import Arith.
  Require Import List.
  Require Import FJ_tactics.
  Require Import cFJ.

  
  Variable (C : Set). (** Class Identifiers **)
  Variable (F : Set). (** Field Identifiers **)
  Variable (M : Set). (** Method Identifiers **)
  Variable (X : Set). (** Variable Identifiers **)
  
  Definition CL := cFJ.CL C.


  Variable (ty_ext : Set).
  Variables (Ty : Set).
  
  Definition FD := cFJ.FD F Ty.
  Definition VD := cFJ.VD X Ty.
  
  Variable E : Set.
  Variable S : Set.

  Definition Es := list E.
  Definition Ss := list S.

  Variable (X_eq_dec : forall (x y : X), {x = y} + {x <> y}).

  Fixpoint match_var (xs : list (cFJ.Var X)) (ys : list X) (x : Var X) : Var X := 
    match xs, ys, x with
      | this :: xs', e :: es', this => (var _ e)
      | var n :: xs', e :: es', var m => if (X_eq_dec m n) then (var _ e) else match_var xs' es' (var X m)
      | _ :: xs' , _ :: es' , _ => match_var xs' es' x
      | _, _, _ => x
    end.

  Fixpoint match_var' (vars : list (cFJ.Var X)) (xs' : list X) (x : X) :  X := 
    match vars, xs', x with
      | var n :: xs', e :: es', m => if (X_eq_dec m n) then e else match_var' xs' es' m
      | _ :: xs' , _ :: es' , _ => match_var' xs' es' x
      | _, _, _ => x
    end.

  Definition Var := cFJ.Var X.

  Inductive LJ_S : Set :=
  | var_assign : X -> E -> LJ_S
  | field_assign : Var -> F -> E -> LJ_S
  | block : Ss -> LJ_S.

  Variable (LJ_S_Wrap : LJ_S -> S).
  Coercion LJ_S_Wrap : LJ_S >-> S.

  Section LJ_S_rect.
    
    Variables
      (P : S -> Type)
      (Q : Ss -> Type).
    
    Hypotheses
      (H1 : forall var e, P (var_assign var e))
      (H2 : forall x f e, P (field_assign x f e))
      (H3 : forall ss, Q ss -> P (block ss))
      (H4 : Q nil)
      (H5 : forall s ss', P s -> Q ss' -> Q (s :: ss')).
    
    Definition lj_s_rect (s : LJ_S) (rect : forall s, P s) : P s :=
      match s return (P s) with
        | var_assign v e => H1 v e
        | field_assign x f e => H2 x f e
        | block ss => H3 ss ((fix ss_rect (ss : Ss) : Q ss :=
          match ss return Q ss with
            | nil => H4 
            | s :: ss' => H5 s ss' (rect s) (ss_rect ss')
          end) ss)
      end.

  End LJ_S_rect.

  Variable (md_def_ext mb_ext' : Set).

  Definition LJ_md_ext := prod Ss md_def_ext.
  Definition LJ_mb_ext := prod Ss mb_ext'.
      
  Variables (Context mty_ext m_call_ext mb_ext: Set)
    (subtype : Context -> Ty -> Ty -> Prop)
    (E_WF : Context -> E -> Ty -> Prop)
    (Es_WF : Context -> Es -> Ty -> Prop)
    (S_WF : Context -> S -> Prop)
    (Empty : Context)
    (lookup : Context -> Var -> Ty -> Prop)
    (WF_fields_map : Context -> Ty -> Ty -> Prop) 
    (WF_mtype_ty_0_map : Context -> Ty -> Ty -> Prop)
    (WF_mtype_Us_map : Context -> m_call_ext -> mty_ext -> list Ty -> list Ty -> Prop)
    (WF_mtype_U_map : Context -> m_call_ext -> mty_ext -> Ty -> Ty -> Prop)
    (WF_mtype_ext : Context -> m_call_ext -> mty_ext -> Prop)
    (fields : Context -> Ty -> list FD -> Prop).

  Inductive LJ_S_WF (gamma : Context) : S -> Prop :=
  | T_Var_Assign : forall v e S T, lookup gamma (var _ v) T -> 
    E_WF gamma e S -> subtype gamma S T -> LJ_S_WF gamma (var_assign v e)
  | T_Field_Assign : forall x f e S T V V' fds i, lookup gamma x V -> 
    WF_fields_map gamma V V' ->
    fields Empty V' fds -> (*** Get fields for x ***)
    nth_error fds i = Some (fd _ _ T f) -> (*** find f in x's fields ***)
    E_WF gamma e S -> 
    subtype gamma S T -> LJ_S_WF gamma (field_assign x f e)
  | T_Block : forall ss, List_P1 (S_WF gamma) ss -> LJ_S_WF gamma (block ss).
  
  Variable (LJ_S_WF_Wrap : forall {gamma s}, LJ_S_WF gamma s -> S_WF gamma s).
  Coercion LJ_S_WF_Wrap : LJ_S_WF >-> S_WF.

  Section LJ_S_WF_recursion.

  Variable (P : forall gamma s, S_WF gamma s -> Prop)
  (Q : forall gamma ss, List_P1 (S_WF gamma) ss -> Prop).

  Hypothesis (H1 : forall gamma v e S T lookup_x WF_e sub_S_T, P _ _ (T_Var_Assign gamma v e S T lookup_x WF_e sub_S_T))
    (H2 : forall gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T,
      P _ _ (T_Field_Assign gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T))
    (H3 : forall gamma ss P1_ss, Q gamma ss P1_ss -> P _ _ (T_Block gamma ss P1_ss))
    (H4 : forall gamma, Q _ _ (Nil (S_WF gamma)))
    (H5 : forall gamma s ss' WF_s WF_ss', P gamma s WF_s -> Q gamma ss' WF_ss' -> 
      Q gamma (s :: ss') (Cons_a _ s ss' WF_s WF_ss')).

  Definition LJ_S_WF_rect gamma s (WF_s : LJ_S_WF gamma s) 
    (S_WF_rect : forall gamma s (WF_s : S_WF gamma s), P _ _ WF_s) : P _ _ WF_s :=
    match WF_s return P _ _ WF_s with
      | T_Var_Assign v e S T lookup_x WF_e sub_S_T => H1 gamma v e S T lookup_x WF_e sub_S_T
      | T_Field_Assign x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T => 
        H2 gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T
      | T_Block ss P1_ss => H3 gamma ss P1_ss 
        ((fix ss_rect gamma ss (WF_ss : List_P1 (S_WF gamma) ss) : Q _ _ WF_ss :=
          match WF_ss return Q _ _ WF_ss with
            | Nil => H4 gamma
            | Cons_a s ss' WF_s WF_ss' => 
              H5 gamma s ss' WF_s WF_ss' (S_WF_rect gamma s WF_s) (ss_rect gamma ss' WF_ss')
          end) _ _ P1_ss)
    end.

  End LJ_S_WF_recursion.

  Variable (cld_ext md_ext O : Set)
    (Meth_WF_Ext : Context -> cld_ext -> md_ext -> Prop)
    (map_mbody : cld_ext -> ty_ext -> m_call_ext -> md_ext -> E -> E -> Prop)
    (map_s : cld_ext -> ty_ext -> m_call_ext -> md_ext -> S -> S -> Prop).
  
  Section Map_S.
    
    (* Variables (map_m_call_ext : m_call_ext -> m_call_ext -> Prop) *)
    (*   (map_new_ext : ty_ext -> ty_ext -> Prop). *)

    (* Definition map_e_ext'' e e' := map_e_ext' map_m_call_ext map_new_ext e e'. *)
    (* Definition map_s'' s s' := map_s map_m_call_ext map_new_ext s s'. *)

    Inductive LJ_map_S : cld_ext -> ty_ext -> m_call_ext -> md_ext -> S -> S -> Prop :=
    | map_var_assign : forall ce te mce mde v e e', map_mbody ce te mce mde e e' -> 
      LJ_map_S ce te mce mde (var_assign v e) (var_assign v e')
    | map_field_assign : forall ce te mce mde x f e e', map_mbody ce te mce mde e e' -> 
      LJ_map_S ce te mce mde (field_assign x f e) (field_assign x f e')
    | map_blck : forall ce te mce mde ss ss', 
      List_P2' (map_s ce te mce mde) ss ss' -> LJ_map_S ce te mce mde (block ss) (block ss').
      
  End Map_S. 

  Definition LJ_Meth_WF_Ext {Meth_WF_Ext' : Context -> cld_ext -> md_def_ext -> Prop}
    (gamma : Context) (ce : cld_ext) (mde : LJ_md_ext) := 
    List_P1 (S_WF gamma) (fst mde) /\ Meth_WF_Ext' gamma ce (snd mde).

  Variable (unwrap_md_ext : md_ext -> list S).

  Inductive LJ_build_mb_ext (ce : cld_ext) (te : ty_ext) (mce : m_call_ext) : md_ext -> LJ_mb_ext -> Prop := 
    lj_build_mb_ext : forall mde me' ss', 
      List_P2' (map_s ce te mce mde) (unwrap_md_ext mde) ss' -> 
      LJ_build_mb_ext ce te mce mde (ss', me').

  Inductive LJ_Val := 
    | Oid : O -> LJ_Val
    | Null : LJ_Val.

  Inductive NPE : Set := npe : NPE.

  Definition FJ_E := cFJ.FJ_E C F M X ty_ext E m_call_ext.

  Definition FJ_Ty := cFJ.FJ_Ty C ty_ext.

  Variable (Config Exception Value : Set)
    (SLookup : Config -> Var -> Value -> Prop)
    (SUpdate : Config -> Var -> Value -> Config)
    (HLookup_Type : Config -> O -> FJ_Ty -> Prop)
    (HLookup_Field : Config -> O -> F -> Value -> Prop)
    (HUpdate : Config -> O -> FJ_Ty -> list (F * Value) -> Config)
    (HUpdate_Field : Config -> O -> F -> Value -> Config)
    (Push_mb_ext : Config -> S -> Config)
    (Set_Exception : Config -> Exception -> Config)
    (NPE_Wrap : NPE -> Exception)
    (FJ_E_Wrap : FJ_E -> E)
    (E_Val : E -> Prop)
    (LJ_Val_Wrap : LJ_Val -> Value)
    (FJ_Ty_Wrap : FJ_Ty -> Ty)
    (Val_E_Wrap : Value -> E)
    (MB_ext_S : mb_ext -> S).
  
  Coercion NPE_Wrap : NPE >-> Exception.
  Coercion FJ_E_Wrap : FJ_E >-> E.
  Coercion FJ_Ty_Wrap : FJ_Ty >-> Ty.

  Definition var v : Var := cFJ.var X v.
  Definition e_var v : FJ_E := cFJ.e_var C F M X ty_ext E m_call_ext v.
  Definition fd_access e f : FJ_E := cFJ.fd_access C F M X ty_ext E m_call_ext e f.
  Definition new ty es : FJ_E := cFJ.new C F M X ty_ext E m_call_ext ty es.
  Definition m_call mce e m es : FJ_E := cFJ.m_call C F M X ty_ext E m_call_ext mce e m es.

  Inductive LJ_E_Val : E -> Prop := e_var_val : forall x, LJ_E_Val (e_var x).
  
  Definition SFresh sigma x := forall v, ~SLookup sigma (var x) v.
  Definition HFresh sigma o := (forall ty, ~ HLookup_Type sigma o ty) /\ (forall f v, ~ HLookup_Field sigma o f v).
  
  Inductive LJ_Field_Reduce : Config -> E -> Config -> E -> Prop :=
  | R_Field_Read_NPE : forall sigma x f, SLookup sigma x (LJ_Val_Wrap Null) -> 
    LJ_Field_Reduce sigma (fd_access (e_var x) f) (Set_Exception sigma npe) (fd_access (e_var x) f)
  | R_Field_Read : forall sigma x f oid v x', SLookup sigma x (LJ_Val_Wrap (Oid oid)) -> 
    HLookup_Field sigma oid f v -> SFresh sigma x' -> 
    LJ_Field_Reduce sigma (fd_access (e_var x) f) (SUpdate sigma (var x') v) (e_var (var x')).
  
  Inductive LJ_New_Reduce : Config -> E -> Config -> E -> Prop :=
  | R_New : forall sigma xs ty vals o' x' fds fds_vals, 
    HFresh sigma o' -> SFresh sigma x' -> (*** Fresh Oid and Variable***)
    fields Empty (FJ_Ty_Wrap ty) fds -> (*** Fetch new class' fields ***)
    List_P2' (SLookup sigma) xs vals -> (*** Get values for provided arguments ***)  
    zip fds vals (fun fd' val => (match fd' with cFJ.fd _ f => f end, val)) = Some fds_vals -> (***Merge fields + Vals***)
    LJ_New_Reduce sigma (new ty (map (fun x => (FJ_E_Wrap (e_var x))) xs))
    (HUpdate (SUpdate sigma (var x') (LJ_Val_Wrap (Oid o'))) o' ty fds_vals) (e_var (var x')).

  Definition MB := cFJ.MB X E mb_ext.
  Definition mb := cFJ.mb X E mb_ext.
  Definition Xs_To_Vars := cFJ.Xs_To_Vars X.
  Definition this := cFJ.this X.

  Variable (mbody : Context -> m_call_ext -> M -> Ty -> MB -> Prop)
    (trans : E -> list Var -> Es -> E)
    (S_trans : S -> list Var -> list X -> S).

  Fixpoint SUpdate_list (sigma : Config) (lkp_list : list (Var * Value)) : Config :=
    match lkp_list with
      nil => sigma
      | (x, val) :: lkp_list' => SUpdate (SUpdate_list sigma lkp_list') x val
    end.

  Inductive LJ_M_Call_Reduce : Config -> E -> Config -> E -> Prop :=
  | R_Invk_NPE : forall sigma mce x m xs, SLookup sigma x (LJ_Val_Wrap Null) -> 
    LJ_M_Call_Reduce sigma (m_call mce (e_var x) m (map (fun x => (FJ_E_Wrap (e_var x))) xs))
    (Set_Exception sigma npe) (m_call mce (e_var x) m (map (fun x => (FJ_E_Wrap (e_var x))) xs))
  | R_Invk : forall sigma mce x m xs mbe ys e oid ty x' xs' vs y_vs, 
    SLookup sigma x (LJ_Val_Wrap (Oid oid)) -> (*** Find object_id ***)
    HLookup_Type sigma oid ty -> (*** Find runtime type ***)
    mbody Empty mce m ty (mb mbe ys e) -> (*** Lookup Method Body ***)
    SFresh sigma x' -> (*** Get fresh return variable ***)
    List_P1 (SFresh sigma) xs' -> (*** Get fresh variables for parameters ***)
    distinct (x' :: xs') -> (*** Distinct new variables ***)
    List_P2' (SLookup sigma) xs vs -> (*** Get values for provided arguments ***)
    zip (x' :: xs') ((LJ_Val_Wrap (Oid oid)) :: vs) (fun x val => pair (var x) val) = Some y_vs -> 
    LJ_M_Call_Reduce sigma (m_call mce (e_var x) m (map (fun x => (FJ_E_Wrap (e_var x))) xs))
    (Push_mb_ext (SUpdate_list sigma y_vs) (S_trans (MB_ext_S mbe) (this :: (Xs_To_Vars ys)) 
      (x' :: xs')))
    (trans e (this :: (Xs_To_Vars ys)) (FJ_E_Wrap (e_var (var x')) :: (map (fun x => (FJ_E_Wrap (e_var (var x))))
      xs'))).

  Variable (E_C_Reduce : Config -> E -> Config -> E -> Prop)
    (E_C_Reduce_List : Config -> Es -> Config -> Es -> Prop).
  
  Inductive FJ_Congruence_Reduce : Config -> E -> Config -> E -> Prop :=
    RC_Field : forall sigma e sigma' e' f, E_C_Reduce sigma e sigma' e' -> 
      FJ_Congruence_Reduce sigma (fd_access e f) sigma' (fd_access e' f)
  | RC_Invk_Recv : forall e sigma e' sigma' mce m es, E_C_Reduce sigma e sigma' e' ->
    FJ_Congruence_Reduce sigma (m_call mce e m es) sigma' (m_call mce e' m es)
  | RC_Invk_Arg : forall e sigma sigma' mce m es es', E_C_Reduce_List sigma es sigma' es' ->
    FJ_Congruence_Reduce sigma (m_call mce e m es) sigma' (m_call mce e m es')
  | RC_New_Arg : forall ty sigma es sigma' es', E_C_Reduce_List sigma es sigma' es' ->
    FJ_Congruence_Reduce sigma (new ty es) sigma' (new ty es').
  
  Inductive Reduce_List : Config -> Es -> Config -> Es -> Prop :=
  | Reduce_T : forall e sigma e' sigma' es, E_C_Reduce sigma e sigma' e' -> Reduce_List sigma (e :: es) sigma' (e' :: es)
  | Reduce_P : forall x sigma es sigma' es', E_C_Reduce_List sigma es sigma' es' -> 
    Reduce_List sigma ((FJ_E_Wrap (e_var x)) :: es) sigma' ((FJ_E_Wrap (e_var x)) :: es').

  Variables 
    (LJ_Field_Reduce_Wrap : forall sigma e sigma' e',
    LJ_Field_Reduce sigma e sigma' e' -> E_C_Reduce sigma e sigma' e')
    (LJ_New_Reduce_Wrap : forall sigma e sigma' e',
      LJ_New_Reduce sigma e sigma' e' -> E_C_Reduce sigma e sigma' e')
    (LJ_M_Call_Reduce_Wrap : forall sigma e sigma' e',
      LJ_M_Call_Reduce sigma e sigma' e' -> E_C_Reduce sigma e sigma' e')
    (FJ_C_Reduce_Wrap : forall sigma e sigma' e', 
    FJ_Congruence_Reduce sigma e sigma' e' -> E_C_Reduce sigma e sigma' e')
    (Reduce_List_Wrap : forall sigma es sigma' es', 
      Reduce_List sigma es sigma' es' -> E_C_Reduce_List sigma es sigma' es').
  
  Coercion FJ_C_Reduce_Wrap : FJ_Congruence_Reduce >-> E_C_Reduce.
  Coercion Reduce_List_Wrap : Reduce_List >-> E_C_Reduce_List.

  Section FJ_C_Reduce_Rec.
    Variable (P : forall sigma e sigma' e', E_C_Reduce sigma e sigma' e' -> Prop)
      (Q : forall sigma es sigma' es', E_C_Reduce_List sigma es sigma' es' -> Prop).
    
    Hypothesis (H1 : forall sigma e sigma' e' f Red_e_e', P _ _ _ _ Red_e_e' ->
      P _ _ _ _ (RC_Field sigma e sigma' e' f Red_e_e'))
      (H2 : forall sigma e sigma' e' mce m es Red_e_e', P _ _ _ _ Red_e_e' -> 
        P _ _ _ _ (RC_Invk_Recv sigma e sigma' e' mce m es Red_e_e'))
      (H3 : forall e mce m sigma es sigma' es' Red_es_es', Q _ _ _ _ Red_es_es' -> 
        P _ _ _ _ (RC_Invk_Arg e mce m sigma es sigma' es' Red_es_es'))
      (H4 : forall ty sigma es sigma' es' Red_es_es', Q _ _ _ _ Red_es_es' -> 
        P _ _ _ _ (RC_New_Arg ty sigma es sigma' es' Red_es_es'))
      (H5 : forall sigma e sigma' e' es Red_e_e', P _ _ _ _ Red_e_e' -> 
        Q _ _ _ _ (Reduce_T sigma e sigma' e' es Red_e_e'))
      (H6 : forall e sigma es sigma' es' Red_es_es', Q _ _ _ _ Red_es_es' -> 
        Q _ _ _ _ (Reduce_P e sigma es sigma' es' Red_es_es')).
    
    Definition FJ_Congruence_Reduce_rect' sigma e sigma' e' (red_e : FJ_Congruence_Reduce sigma e sigma' e') 
      (C_Reduce_rect' : forall sigma e sigma' e' red_e_e', P sigma e sigma' e' red_e_e') 
      (C_Reduce_List_rect' : forall sigma es sigma' es' red_es_es', Q sigma es sigma' es' red_es_es') : P _ _ _ _ red_e :=
      match red_e return P _ _ _ _ red_e with 
        | RC_Field sigma e sigma' e' f Red_e_e' => H1 sigma e sigma' e' f Red_e_e' (C_Reduce_rect' _ _ _ _ Red_e_e')
        | RC_Invk_Recv sigma e sigma' e' mce m es Red_e_e' => 
          H2 sigma e sigma' e' mce m es Red_e_e' (C_Reduce_rect' _ _ _ _ Red_e_e')
        | RC_Invk_Arg e mce m sigma es sigma' es' Red_es_es' => H3 e mce m sigma es sigma' es' Red_es_es' 
          (C_Reduce_List_rect' _ _ _ _ Red_es_es')
        | RC_New_Arg ty sigma es sigma'  es' Red_es_es' => 
          H4 ty sigma es sigma' es' Red_es_es' (C_Reduce_List_rect' _ _ _ _ Red_es_es')
      end.
    
    Definition Reduce_List_rect' sigma es sigma' es' (red_es : Reduce_List sigma es sigma' es')     
      (C_Reduce_rect' : forall sigma e sigma' e' red_e_e', P sigma e sigma' e' red_e_e') 
      (C_Reduce_List_rect' : forall sigma es sigma' es' red_es_es', Q sigma es sigma' es' red_es_es') : Q _ _ _ _ red_es :=
      match red_es return Q _ _ _ _ red_es with
        | Reduce_T sigma e sigma' e' es red_e => H5 _ _ _ _ _ red_e (C_Reduce_rect' _ _ _ _ red_e) 
        | Reduce_P e sigma es sigma' es' red_es => H6 _ _ _ _ _ red_es (C_Reduce_List_rect' _ _ _ _ red_es)
    end.
  
  End FJ_C_Reduce_Rec.
  
  Definition LJ_S_trans (s : LJ_S) (vars : list Var) (xs : list X): S := 
    match s with 
      | var_assign v e => var_assign (match_var' vars xs v) (trans e vars (map (fun x => FJ_E_Wrap (e_var (var x))) xs))
      | field_assign x f e => field_assign (match_var vars xs x) f 
        (trans e vars (map (fun x => FJ_E_Wrap (e_var (var x))) xs))
      | block ss => block (map (fun s => S_trans s vars xs) ss)
    end.

  Variable (Check_NPE_Exception : Config -> bool)
    (Pop_mb_ext : Config -> S -> Config -> Prop).
  
  Inductive LJ_S_Reduce : Config -> list S -> Config -> list S -> Prop :=
  | R_NPE : forall sigma ss,
    Check_NPE_Exception sigma = true -> 
    LJ_S_Reduce sigma ss sigma nil
  | R_Block : forall sigma ss ss',
    Check_NPE_Exception sigma = false -> 
    LJ_S_Reduce sigma ((LJ_S_Wrap (block ss)) :: ss') sigma (ss ++ ss')
  | R_Var_Assign : forall sigma var' x v ss,
    Check_NPE_Exception sigma = false -> 
    SLookup sigma x v -> 
    LJ_S_Reduce sigma ((LJ_S_Wrap (var_assign var' (e_var x))) :: ss) (SUpdate sigma (var var') v) ss
  | R_Field_Assign_NPE : forall sigma x f y ss,
    SLookup sigma x (LJ_Val_Wrap Null) -> 
    LJ_S_Reduce sigma ((LJ_S_Wrap (field_assign x f (e_var y))) :: ss) (Set_Exception sigma npe) nil
  | R_Field_Assign : forall sigma x f y oid ss v,
    Check_NPE_Exception sigma = false -> 
    SLookup sigma x (LJ_Val_Wrap (Oid oid)) -> 
    SLookup sigma y v -> 
    LJ_S_Reduce sigma ((LJ_S_Wrap (field_assign x f (e_var y))) :: ss) (HUpdate_Field sigma oid f v) ss.

  Inductive LJ_C_S_Reduce : Config -> list S -> Config -> list S -> Prop :=
  | R_C_Field_Assign : forall sigma sigma' sigma'' x f e e' ss s',
    Check_NPE_Exception sigma = false -> 
    E_C_Reduce sigma e sigma' e' -> 
    Pop_mb_ext sigma' s' sigma'' -> 
    LJ_C_S_Reduce sigma ((LJ_S_Wrap (field_assign x f e)) :: ss) sigma''
    (s' :: (LJ_S_Wrap (field_assign x f e')) :: ss)
  | R_C_Var_Assign : forall sigma sigma' sigma'' var e e' ss s',
    Check_NPE_Exception sigma = false -> 
    E_C_Reduce sigma e sigma' e' -> 
    Pop_mb_ext sigma' s' sigma'' -> 
    LJ_C_S_Reduce sigma ((LJ_S_Wrap (var_assign var e)) :: ss) 
    sigma'' (s' :: (LJ_S_Wrap (var_assign var e')) :: ss).

  Variable (WF_Config : Context -> Config -> Prop)
    (S_Reduce : Config -> list S -> Config -> list S -> Prop)
    (LJ_S_Reduce_Wrap : forall sigma ss sigma' ss', LJ_S_Reduce sigma ss sigma' ss' ->
      S_Reduce sigma ss sigma' ss')
    (LJ_C_S_Reduce_Wrap : forall sigma ss sigma' ss', LJ_C_S_Reduce sigma ss sigma' ss' ->
      S_Reduce sigma ss sigma' ss')
    (mtype : Context -> M -> Ty -> Mty Ty mty_ext -> Prop)
    (WF_Type : Context -> Ty -> Prop).

  Definition LJ_WF_Config (gamma : Context) (sigma : Config) : Prop :=
    (forall x ty, lookup gamma x ty -> 
      (SLookup sigma x (LJ_Val_Wrap Null) \/
        exists oid, SLookup sigma x (LJ_Val_Wrap (Oid oid)) /\
          exists ty', HLookup_Type sigma oid ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty')) /\
    (forall oid f v, HLookup_Field sigma oid f v -> exists ty, HLookup_Type sigma oid ty) /\
    (forall oid ty, HLookup_Type sigma oid ty -> 
      exists fds, fields Empty ty fds /\ 
        (forall n ty f, nth_error fds n = Some (fd _ _ ty f) -> 
          HLookup_Field sigma oid f (LJ_Val_Wrap Null) \/
          (exists oid', HLookup_Field sigma oid f (LJ_Val_Wrap (Oid oid')) /\
            exists ty', HLookup_Type sigma oid' ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty'))) /\
    (forall s sigma', Pop_mb_ext sigma s sigma' -> S_WF gamma s).

  Definition E_Progress_P (gamma : Context) (e : E) (ty : Ty) (WF_e : E_WF gamma e ty) :=
    forall sigma, WF_Config gamma sigma -> E_Val e \/ exists sigma', exists e', 
      E_C_Reduce sigma e sigma' e'.

  Definition E_Progress_Q (gamma : Context) (es : Es) (tys : list Ty) 
    (WF_es : List_P2' (E_WF gamma) es tys) := 
    forall sigma, WF_Config gamma sigma -> List_P1 E_Val es \/ exists sigma', exists es', 
      E_C_Reduce_List sigma es sigma' es'.

  Definition S_progress_P (gamma : Context) (s : S) (WF_ss : S_WF gamma s) := 
    forall sigma ss, WF_Config gamma sigma -> exists ss', exists sigma',
      S_Reduce sigma (s :: ss) sigma' ss'.

  Definition S_progress_Q (gamma : Context) (ss : Ss) (WF_ss : List_P1 (S_WF gamma) ss) := 
    forall sigma, WF_Config gamma sigma -> ss = nil \/ exists ss', exists sigma',
      S_Reduce sigma ss sigma' ss'.
    
  Variable (E_WF_Wrap : forall gamma e ty, cFJ.FJ_E_WF _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty gamma e ty -> E_WF gamma e ty)
  (LJ_E_Val_Wrap : forall e, LJ_E_Val e -> E_Val e)
  (ex_SFresh : forall sigma, exists x, SFresh sigma x)
  (ex_HFresh : forall sigma, exists o, HFresh sigma o).

  Definition Exp_WF := cFJ.FJ_E_WF _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty.
    
  Definition T_Var := cFJ.T_Var _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty.

  Lemma FJ_progress_1_H1 : forall gamma x ty lookup_x, E_Progress_P _ _ _ (E_WF_Wrap _ _ _ (T_Var gamma x ty lookup_x)).
    unfold E_Progress_P; intros.
    left; apply LJ_E_Val_Wrap; econstructor.
  Qed.

  Definition T_Field := cFJ.T_Field _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty.

  Variable (LJ_imp_WF_Config : forall gamma sigma, WF_Config gamma sigma -> LJ_WF_Config gamma sigma)
    (E_Val_invert: forall e, E_Val e -> LJ_E_Val e)
    (FJ_E_WF_invert : forall gamma (e : FJ_E) c0, E_WF gamma e c0 -> Exp_WF gamma e c0)
    (EWrap_inject : forall (e e' : FJ_E), FJ_E_Wrap e = FJ_E_Wrap e' -> e = e')
    (Lem_2_8 : forall delta S T sub_S_T, Lem_2_8_P F Ty Context subtype fields WF_fields_map Empty delta S T sub_S_T)
    (WF_fields_map_id : forall gamma cl' fds, fields gamma cl' fds ->
      forall tye c tye' fds' fds'', cl' = FJ_Ty_Wrap (ty_def _ _ tye c) -> fds'' = fds -> 
        fields gamma (FJ_Ty_Wrap (ty_def _ _ tye' c)) fds' -> 
        map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds)
    (WF_fields_map_id' : forall gamma tye c ty', WF_fields_map gamma (FJ_Ty_Wrap (ty_def _ _ tye c)) ty' ->
      exists tye', ty' = (FJ_Ty_Wrap (ty_def _ _ tye' c)))
    (WF_fields_map_id'' : forall gamma ty ty' ty'', 
      WF_fields_map gamma ty ty' ->
      WF_fields_map gamma ty ty'' -> ty' = ty'').
    
  Lemma FJ_progress_1_H2 : forall gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds, E_Progress_P _ _ _ WF_e ->
    E_Progress_P _ _ _ (E_WF_Wrap _ _ _ (T_Field gamma e f ty ty' fds' ty'' i WF_e ty_map fds_ty' nth_fds)).
    unfold E_Progress_P; intros. 
    rename H into progress_e; rename H0 into WF_sigma;
      right; destruct (progress_e _ WF_sigma) as [val_e | [sigma' [e' red_e]]].
    apply LJ_imp_WF_Config in WF_sigma.
    apply E_Val_invert in val_e; inversion val_e; subst.
    destruct WF_sigma as [SWF_sig [HWF_T_sig HWF_F_sig]].
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate.
    injection H; intros; subst.
    destruct (SWF_sig _ _ H0) as [x_Null | [oid [x_Oid [ty''' [fnd_oid [sub_ty_ty''' WF_ty''']]]]]].
    eexists _; eexists _; eapply LJ_Field_Reduce_Wrap; econstructor; assumption.
    destruct (HWF_F_sig _ _ fnd_oid) as [fds [fds_ty in_fds]].
    destruct (ex_SFresh sigma) as [x' Fresh_x'].
    destruct (Lem_2_8 _ _ _ sub_ty_ty''' _ _ ty_map fds_ty') as [S' [map_ty''' [fds'' [fields_S' sub_fds''_fds']]]].
    destruct ty'''; destruct (WF_fields_map_id' _ _ _ _ map_ty'''); subst.
    generalize (WF_fields_map_id _ _ _ fds_ty _ _ _ _ _ 
      (refl_equal _) (refl_equal _) fields_S'); intros.
    assert (exists ty', nth_error fds i = Some (fd F Ty ty' f)).
    generalize i fds'' fds sub_fds''_fds' nth_fds H1; clear; induction fds'; destruct i; destruct fds; 
      destruct fds''; simpl; intros; try discriminate.
    injection nth_fds; intros; subst.
    generalize (sub_fds''_fds' _ 0 (refl_equal _)); intros; discriminate.
    destruct f0; destruct f1; simpl in *|-*; injection H1; intros; subst.
    generalize (sub_fds''_fds' _ 0 (refl_equal _)); simpl; intros; injection H0; 
      injection nth_fds; intros; subst; injection H3; intros; subst; eexists _; reflexivity.
    generalize (sub_fds''_fds' _ 0 (refl_equal _)); simpl; intros; discriminate.
    destruct f0; destruct f1; simpl in *|-*; injection H1; intros; subst; clear H1.
    eapply (IHfds' i fds'' fds); eauto.
    intros; eapply (sub_fds''_fds' _ (1 + n)); auto.
    destruct H2 as [S' nth_fds'].    
    destruct (in_fds _ _ _ nth_fds') as [Null_lookup | [o [o_lookup _]]];
      eexists _; eexists _; eapply LJ_Field_Reduce_Wrap; econstructor 2; try eassumption.
    eexists _; eexists _; apply FJ_C_Reduce_Wrap; econstructor; eauto.
  Qed.

  Definition T_Invk := cFJ.T_Invk  _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty.

  Lemma E_Val_List_map : forall es, List_P1 E_Val es -> exists xs, es = (map (fun x => (FJ_E_Wrap (e_var x))) xs).
    induction es; intros; inversion H; subst.
    exists nil; reflexivity.
    destruct (IHes H3) as [xs' eq_es]; subst.
    apply E_Val_invert in H2; inversion H2; subst.
    exists (x :: xs'); reflexivity.
  Qed.
  
  Definition L := cFJ.L C F M X ty_ext Ty E md_ext cld_ext.

  Variable 
    (CT : C -> option L)
    (build_mb_ext : cld_ext -> ty_ext ->  m_call_ext -> md_ext -> mb_ext -> Prop)
    (mbody_build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
    (mtype_implies_mbody : forall delta m ty mty' mtype_m, 
      mtype_implies_mbody_P C F M X ty_ext Ty FJ_Ty_Wrap E m_call_ext mty_ext md_ext cld_ext 
      CT Context mtype mbody_build_te mb_ext build_mb_ext map_mbody Empty delta m ty mty' 
      mtype_m)
  (Lem_2_9 : forall delta S T (sub_S_T : subtype delta S T), 
    Lem_2_9_P _ _ _ _ _ subtype mtype WF_mtype_ty_0_map WF_mtype_Us_map
    WF_mtype_U_map WF_mtype_ext Empty _ _ _ sub_S_T)
  (WF_mtype_ty_0_map_Empty_refl : forall gamma te c ty, 
    WF_mtype_ty_0_map gamma (FJ_Ty_Wrap (ty_def _ _ te c)) ty -> ty = FJ_Ty_Wrap (ty_def _ _ te c))
  (WF_mtype_ty_0_map_total : forall delta S T, subtype delta S T -> forall T',
    WF_mtype_ty_0_map delta T T' ->  exists S', WF_mtype_ty_0_map delta S S')
  (SLookup_update_eq : forall sigma X ty, SLookup (SUpdate sigma X ty) X ty)
  (SLookup_update_neq : forall sigma Y X ty ty', SLookup sigma X ty -> X <> Y -> 
    SLookup (SUpdate sigma Y ty') X ty)
  (SLookup_update_neq' : forall sigma Y X ty ty', SLookup (SUpdate sigma Y ty') X ty -> X <> Y -> 
    SLookup sigma X ty)
  (SLookup_id : forall sigma X ty ty', SLookup sigma X ty -> SLookup sigma X ty' -> ty = ty')
  (SLookup_dec : forall sigma x, (exists ty, SLookup sigma x ty) \/ (forall ty, ~ SLookup sigma x ty))
  (WF_mtype_Us_map_len : forall delta mce mtye Ds Ds', WF_mtype_Us_map delta mce mtye Ds Ds' ->
    length Ds = length Ds').
  
  Lemma Fresh_List : forall n sigma, exists xs, length xs = n /\ (List_P1 (SFresh sigma) xs) /\ (distinct xs).
    induction n.
    exists nil; simpl; repeat constructor.
    intros; destruct (IHn sigma) as [xs' [len_xs' [Fresh_xs' distinct_xs']]].
    destruct (ex_SFresh (SUpdate_list sigma (map (fun x => (var x, LJ_Val_Wrap Null)) xs'))).
    exists (x :: xs'); repeat constructor.
    simpl; rewrite len_xs'; reflexivity.
    unfold SFresh in *|-*.
    unfold not; intros; generalize H H0 X_eq_dec SLookup_update_eq SLookup_update_neq; clear; 
      induction xs'; simpl; intros; eauto.
    eapply (H _ H0).
    destruct (X_eq_dec a x); subst.
    apply (H (LJ_Val_Wrap Null)); apply SLookup_update_eq.
    apply IHxs'; auto.
    unfold not; intros; apply (H v0).
    apply SLookup_update_neq; auto.
    unfold not; intros G; apply n; injection G; congruence.
    assumption.
    generalize H X_eq_dec SLookup_update_neq SLookup_update_eq; clear; induction xs'; simpl; intros; auto.
    unfold not; intros; destruct H0; subst.
    unfold SFresh in H; apply (H (LJ_Val_Wrap Null)); eauto.
    apply IHxs'; auto.
    destruct (X_eq_dec a x); subst.
    unfold SFresh, not; intros; apply (H (LJ_Val_Wrap Null)); auto.
    unfold SFresh, not; intros; apply (H v); apply SLookup_update_neq; auto.
    unfold not; intros G; apply n; injection G; congruence.
    assumption.
  Qed.
    
  Lemma length_List_P2' : forall (A B : Type) as' bs' (P : A -> B -> Prop),
    List_P2' P as' bs' -> length as' = length bs'.
    induction as'; intros; inversion H; subst; auto.
    simpl; erewrite IHas'; eauto.
  Qed.
  
  Variable mbody_Wrap : forall delta mce m ty mb,
    cFJ.mbody C F M X ty_ext Ty FJ_Ty_Wrap E m_call_ext md_ext
    cld_ext CT Context mbody_build_te mb_ext build_mb_ext
    map_mbody delta mce m ty mb -> mbody delta mce m ty mb.

  Lemma FJ_progress_1_H3 : forall gamma e_0 ty_0 ty_0' U U' m mtye mce Us Us' Ss es WF_e_0 
    ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye, 
    E_Progress_P _ _ _ WF_e_0 -> E_Progress_Q _ _ _ WF_es ->
    E_Progress_P _ _ _ (E_WF_Wrap _ _ _ (T_Invk gamma e_0 ty_0 ty_0' U U' m mtye 
      mce Us Us' Ss es WF_e_0 ty_0_map mtype_m map_Us map_U WF_es sub_Ss_Us' WF_mtye)).
    unfold E_Progress_P; unfold E_Progress_Q; intros.
    rename H into progress_e_0; rename H0 into progress_es; rename H1 into WF_sigma.
    destruct (progress_e_0 _ WF_sigma) as [Val_e_0 | [sigma' [e' red_e]]].
    apply E_Val_invert in Val_e_0; inversion Val_e_0; subst; clear Val_e_0.
    right; destruct (progress_es _ WF_sigma) as [Val_es | [sigma' [es' red_es]]].
    destruct (E_Val_List_map _ Val_es) as [xs eq_es]; subst.
    apply LJ_imp_WF_Config in WF_sigma; destruct WF_sigma as [SWF_sig [HWF_T_sig HWF_F_sig]].
    apply FJ_E_WF_invert in WF_e_0; inversion WF_e_0; subst;
      apply EWrap_inject in H; try discriminate.
    injection H; intros; subst; clear H.
    destruct (SWF_sig _ _ H0) as [x_Null | [oid [x_Oid [ty''' [fnd_oid [sub_ty_ty''' WF_ty''']]]]]].
    eexists _; eexists _; eapply LJ_M_Call_Reduce_Wrap; econstructor; assumption.
    assert (List_P2' (lookup gamma) xs Ss0) by 
      (generalize Ss0 WF_es FJ_E_WF_invert EWrap_inject; clear; induction xs; simpl; intros; 
        inversion WF_es; subst; constructor; first [
          apply FJ_E_WF_invert in H1; inversion H1; apply EWrap_inject in H; try discriminate; 
            injection H; intros; subst; auto | apply IHxs; auto]).
    assert (exists vs, List_P2' (SLookup sigma) xs vs) by
      (generalize Ss0 H SWF_sig; clear; induction xs; simpl; intros; inversion H; subst; 
        first [eexists _; econstructor; fail | 
          destruct (IHxs Bs) as [Bs' Val_xs]; auto;
            destruct (SWF_sig _ _ H2) as [Null_a | [oid [oid_y _]]]; eexists (_ :: _); econstructor;
              eauto]).
    destruct H1 as [vs' Lookup_xs].
    destruct (WF_mtype_ty_0_map_total _ _ _ sub_ty_ty''' _ ty_0_map) as [S' map_ty'''_S'].
    destruct (Lem_2_9 _ _ _ sub_ty_ty''' _ _ _ _ _ _ _ _ _ ty_0_map mtype_m map_U map_Us WF_mtye 
      map_ty'''_S') as [V [Vs [mtye1 [mtype_m_S' [V' [map_V_V' [sub_Vs_Us [sub_V'_U' WF_mtye1]]]]]]]].
    destruct ty'''; rewrite (WF_mtype_ty_0_map_Empty_refl _ _ _ _ map_ty'''_S') in mtype_m_S'.
    destruct (mtype_implies_mbody _ _ _ _ mtype_m_S' mce _ _ _ _ _ (refl_equal _) 
    (refl_equal _) (refl_equal _)) as [mbe [xs' [e [mbody_S' len_xs']]]].
    destruct (Fresh_List (1 + (length xs')) sigma) as [xs'' [len_xs'' [Fresh_xs'' distinct_xs'']]].
    destruct xs'' as [_ | y ys].
    simpl in len_xs''; discriminate.
    inversion Fresh_xs''; subst; clear Fresh_xs''.
    revert len_xs''; intros.
    caseEq (zip ys vs' (fun (x0 : X) (val : Value) => (var x0, val))); intros.
    eexists _; eexists _; eapply LJ_M_Call_Reduce_Wrap; econstructor 2; try eassumption.
    eauto.
    simpl; rewrite H1; reflexivity.
    simpl in len_xs''; injection len_xs''; intros.
    assert (length ys = length vs') by
      (rewrite <- (length_List_P2' _ _ _ _ _ Lookup_xs); rewrite H2; rewrite len_xs';
        rewrite (WF_mtype_Us_map_len _ _ _ _ _ sub_Vs_Us);
          rewrite <- (length_List_P2' _ _ _ _ _ sub_Ss_Us'); 
            rewrite <- (length_List_P2' _ _ _ _ _ H); reflexivity).
    elimtype False; generalize vs' H5 H1; clear; induction ys; destruct vs'; simpl; intros;
      try discriminate.
    caseEq (zip ys vs' (fun (x0 : X) (val : Value) => (var x0, val))); intros; rewrite H in H1; 
      try discriminate.
    eauto.
    eexists _; eexists _; eapply FJ_C_Reduce_Wrap; econstructor 3; eauto.
    right; eexists _; eexists _; eapply FJ_C_Reduce_Wrap; econstructor 2; eauto.
  Qed.

  Definition T_New := cFJ.T_New  _ _ _ _ _ Ty FJ_Ty_Wrap _ _ FJ_E_Wrap mty_ext _ subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map WF_mtype_Us_map WF_mtype_U_map 
    WF_mtype_ext Empty.

  Lemma FJ_progress_1_H4 : forall gamma cl te Ss fds es WF_cl fds_cl WF_es sub_fds,
    E_Progress_Q _ _ _ WF_es -> 
    E_Progress_P _ _ _ (E_WF_Wrap _ _ _ (T_New gamma cl te Ss fds es  WF_cl fds_cl WF_es sub_fds)).
    unfold E_Progress_P; unfold E_Progress_Q; intros.
    rename H into progress_es; rename H0 into WF_sigma.
    right; destruct (progress_es _ WF_sigma) as [Val_es | [sigma' [es' red_es]]].
    destruct (E_Val_List_map _ Val_es) as [xs eq_es]; subst.
    apply LJ_imp_WF_Config in WF_sigma; destruct WF_sigma as [SWF_sig [HWF_T_sig HWF_F_sig]].
    assert (List_P2' (lookup gamma) xs Ss0) by 
      (generalize Ss0 WF_es FJ_E_WF_invert EWrap_inject; clear; induction xs; simpl; intros; 
        inversion WF_es; subst; constructor; first [
          apply FJ_E_WF_invert in H1; inversion H1; apply EWrap_inject in H; try discriminate; 
            injection H; intros; subst; auto | apply IHxs; auto]).
    assert (exists vs, List_P2' (SLookup sigma) xs vs) by
      (generalize Ss0 H SWF_sig; clear; induction xs; simpl; intros; inversion H; subst; 
        first [eexists _; econstructor; fail | 
          destruct (IHxs Bs) as [Bs' Val_xs]; auto;
            destruct (SWF_sig _ _ H2) as [Null_a | [oid [oid_y _]]]; eexists (_ :: _); econstructor;
              eauto]).
    destruct H0 as [vs' Lookup_xs].
    destruct (ex_SFresh sigma); destruct (ex_HFresh sigma).
    assert (length vs' = length fds) by
      (rewrite <- (length_List_P2' _ _ _ _ _ Lookup_xs);
        rewrite <- (length_List_P2' _ _ _ _ _ sub_fds);
          rewrite <- (length_List_P2' _ _ _ _ _ H); reflexivity).
    caseEq (zip fds vs' (fun (fd' : FD) (val : Value) => (match fd' with | fd _ f => f end, val))); intros.
    eexists _; eexists _; eapply LJ_New_Reduce_Wrap; econstructor; try eassumption.
    elimtype False; generalize vs' H2 H3; clear; induction fds; destruct vs'; simpl; intros;
      try discriminate.
    caseEq (zip fds vs' (fun (fd' : FD) (val : Value) => (match fd' with | fd _ f => f end, val))); intros; 
      rewrite H in H3; try discriminate.
    eauto.
    eexists _; eexists _; eapply FJ_C_Reduce_Wrap; econstructor; eauto.
  Qed.

  Lemma FJ_progress_1_H5 : forall gamma, E_Progress_Q gamma nil nil (nil_P2' (E_WF gamma)).
    unfold E_Progress_Q; intros.
    left; constructor.
  Qed.

  Lemma FJ_progress_1_H6 : forall gamma e es ty tys WF_e WF_es,
    E_Progress_P gamma e ty WF_e -> E_Progress_Q gamma es tys WF_es -> 
    E_Progress_Q _ _ _ (cons_P2' _ _ _ _ _ WF_e WF_es).
    unfold E_Progress_P; unfold E_Progress_Q; intros.
    rename H into progress_e_0; rename H0 into progress_es; rename H1 into WF_sigma.
    destruct (progress_e_0 _ WF_sigma) as [Val_e_0 | [sigma' [e' red_e]]].
    destruct (progress_es _ WF_sigma) as [Val_es | [sigma' [es' red_es]]].
    left; constructor; auto.
    apply E_Val_invert in Val_e_0; inversion Val_e_0; subst; clear Val_e_0.
    right; eexists _; eexists _; eapply Reduce_List_Wrap; econstructor 2; eauto.
    right; eexists _; eexists _; eapply Reduce_List_Wrap; econstructor; eauto.
  Qed.

  Definition FJ_E_WF_rect' := FJ_FJ_E_WF_rect' C F M X ty_ext Ty
    FJ_Ty_Wrap E m_call_ext FJ_E_Wrap mty_ext Context subtype WF_Type
    fields mtype E_WF lookup WF_fields_map WF_mtype_ty_0_map
    WF_mtype_Us_map WF_mtype_U_map WF_mtype_ext Empty E_WF_Wrap.

  Definition E_progress := FJ_E_WF_rect' _ _ FJ_progress_1_H1
    FJ_progress_1_H2 FJ_progress_1_H3 FJ_progress_1_H4 FJ_progress_1_H5 FJ_progress_1_H6.

  Variable (E_Progress : forall gamma e ty WF_e, E_Progress_P gamma e ty WF_e)
    (Pop_mb_ext_tot : forall sigma, exists s, exists sigma', Pop_mb_ext sigma s sigma').

  Lemma LJ_progress_H1 : 
    forall gamma v e S T lookup_x WF_e sub_S_T, S_progress_P _ _ (T_Var_Assign gamma v e S T lookup_x WF_e sub_S_T).
    unfold S_progress_P; intros; rename H into WF_sigma.
    caseEq (Check_NPE_Exception sigma); rename H into NPE_except.
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor; assumption.
    destruct (E_Progress _ _ _ WF_e sigma WF_sigma) as [Val_e | [sigma' [e' red_e]]].
    apply E_Val_invert in Val_e; inversion Val_e; subst; clear Val_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    apply LJ_imp_WF_Config in WF_sigma; destruct WF_sigma as [SWF_sig [HWF_T_sig HWF_F_sig]].
    destruct (SWF_sig _ _ H0) as [Null_a | [oid [oid_y _]]];
      eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor 3; eauto.
    destruct (Pop_mb_ext_tot sigma') as [s' [sigma'' Pop_sigma']].
    eexists _; eexists _; apply LJ_C_S_Reduce_Wrap; econstructor; eauto.
  Qed.
    
  Lemma LJ_progress_H2 : forall gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T,
    S_progress_P _ _ (T_Field_Assign gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T).
    unfold S_progress_P; intros; rename H into WF_sigma.
    caseEq (Check_NPE_Exception sigma); rename H into NPE_except.
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor; assumption.
    destruct (E_Progress _ _ _ WF_e sigma WF_sigma) as [Val_e | [sigma' [e' red_e]]].
    apply E_Val_invert in Val_e; inversion Val_e; subst; clear Val_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    apply LJ_imp_WF_Config in WF_sigma; destruct WF_sigma as [SWF_sig [HWF_T_sig HWF_F_sig]].
    destruct (SWF_sig _ _ lookup_x) as [Null_a | [oid [oid_y _]]].
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor 4; eauto.
    destruct (SWF_sig _ _ H0) as [Null_a | [oid' [oid_y' _]]].
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor 5; eauto.
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor 5; eauto.
    destruct (Pop_mb_ext_tot sigma') as [s' [sigma'' Pop_sigma']].
    eexists _; eexists _; apply LJ_C_S_Reduce_Wrap; econstructor; eauto.
  Qed.

  Lemma LJ_progress_H3 : forall gamma ss P1_ss, 
    S_progress_Q gamma ss P1_ss -> S_progress_P _ _ (T_Block gamma ss P1_ss).
    unfold S_progress_P; unfold S_progress_Q; intros; rename H into ss_progress;
      rename H0 into WF_sigma.
    caseEq (Check_NPE_Exception sigma); rename H into NPE_except.
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor; assumption.
    eexists _; eexists _; apply LJ_S_Reduce_Wrap; constructor 2; assumption.
  Qed.    

  Lemma LJ_progress_H4 : forall gamma, S_progress_Q _ _ (Nil (S_WF gamma)).
    unfold S_progress_P; unfold S_progress_Q; intros; rename H into WF_sigma.
    auto.
  Qed.

  Lemma LJ_progress_H5 : forall gamma s ss' WF_s WF_ss', S_progress_P gamma s WF_s ->
    S_progress_Q gamma ss' WF_ss' -> 
    S_progress_Q gamma (s :: ss') (Cons_a _ s ss' WF_s WF_ss').
    unfold S_progress_P; unfold S_progress_Q; intros; rename H into ss_progress;
      rename H0 into WF_sigma.
    right.
    eauto.
  Qed.

  Definition LJ_progress := LJ_S_WF_rect _ _ LJ_progress_H1 LJ_progress_H2 LJ_progress_H3
    LJ_progress_H4 LJ_progress_H5.

  Variable (Conservative_Extension : Context -> Context -> Prop).

  Definition E_preservation_P (sigma : Config) (e : E) (sigma' : Config) (e' : E) 
    (red_e : E_C_Reduce sigma e sigma' e') :=
    forall gamma ty, WF_Config gamma sigma -> E_WF gamma e ty ->
      exists gamma', WF_Config gamma' sigma' /\ exists ty', 
        E_WF gamma' e' ty' /\ subtype gamma' ty' ty /\ 
        (Conservative_Extension gamma gamma').

  Definition E_preservation_Q (sigma : Config) (es : Es) (sigma' : Config) (es' : Es) 
    (red_e : E_C_Reduce_List sigma es sigma' es') :=
    forall gamma tys, WF_Config gamma sigma -> 
      List_P2' (E_WF gamma) es tys ->
      exists gamma', WF_Config gamma' sigma' /\ exists tys', 
        List_P2' (E_WF gamma') es' tys' /\ 
        List_P2' (subtype gamma') tys' tys /\ 
        (Conservative_Extension gamma gamma').

  Variables (WF_Config_Set_NPE : forall gamma sigma, 
    WF_Config gamma sigma -> WF_Config gamma (Set_Exception sigma npe))
  (build_te : cld_ext -> ty_ext -> ty_ext -> ty_ext -> Prop)
  (update : Context -> Var -> Ty -> Context)
  (FJ_subtype_Wrap : forall {gamma : Context} {ty ty' : Ty}, FJ_subtype _ _ _ _ _ Ty 
    FJ_Ty_Wrap E md_ext cld_ext CT Context subtype build_te gamma ty ty' -> 
    subtype gamma ty ty')
  (Conservative_Extension_id : forall gamma, Conservative_Extension gamma gamma)
  (Conservative_Extension_update : forall gamma x ty, (forall ty, ~ lookup gamma x ty) -> 
    Conservative_Extension gamma (update gamma x ty)).

  Lemma SFresh_lookup : forall gamma sigma x ty, 
    (forall (x : Var) (ty : Ty),
            lookup gamma x ty ->
            SLookup sigma x (LJ_Val_Wrap Null) \/
            (exists oid : O,
               SLookup sigma x (LJ_Val_Wrap (Oid oid)) /\
               (exists ty' : FJ_Ty,
                  HLookup_Type sigma oid ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty'))) -> 
    SFresh sigma x -> ~ lookup gamma (var x) ty.
    unfold SFresh; unfold not; intros; rename H into SWF_sig.
    destruct (SWF_sig _ _ H1) as [Null_a | [oid' [oid_y' _]]]; eauto.
  Qed.

  Lemma LJ_Field_Reduce_H1 : forall sigma x f lookup_x, 
    E_preservation_P _ _ _ _ (LJ_Field_Reduce_Wrap _ _ _ _ (R_Field_Read_NPE sigma x f lookup_x)).
    unfold E_preservation_P; intros; rename H into WF_sigma;
      rename H0 into WF_e.
    exists gamma; split; try (exists ty; repeat split; auto).
    eauto.
    apply FJ_subtype_Wrap; constructor.
  Qed.

  Definition update_list := cFJ.update_list _ _ _ update.

  Variable (LJ_Val_invert : forall (v : Value), 
    {v = LJ_Val_Wrap Null} + {exists oid, v = LJ_Val_Wrap (Oid oid)})
  (HLookup_Field_id : forall sigma oid f c c', 
    HLookup_Field sigma oid f c -> HLookup_Field sigma oid f c' -> c = c')
  (HTLookup_SUpdate : forall sigma x v o ty, 
    HLookup_Type sigma o ty -> HLookup_Type (SUpdate sigma x v) o ty)
  (HTLookup_SUpdate' : forall sigma x v o ty, 
    HLookup_Type (SUpdate sigma x v) o ty -> HLookup_Type sigma o ty)
  (HFLookup_SUpdate : forall sigma x v o f v', 
    HLookup_Field sigma o f v' -> HLookup_Field (SUpdate sigma x v) o f v')
  (HFLookup_SUpdate' : forall sigma x v o f v', 
    HLookup_Field (SUpdate sigma x v) o f v' -> HLookup_Field sigma o f v')
  (Subtype_Update_list_id' : forall gamma S T, subtype gamma S T -> forall x ty,
    subtype (update gamma x ty) S T)
  (E_WF_Update_list_id' : forall gamma x ty e T, E_WF gamma e T ->
    E_WF (update gamma x ty) e T)
  (S_WF_Update_list_id' : forall gamma x ty s, S_WF gamma s ->
    S_WF (update gamma x ty) s)
  (WF_Type_update_id : forall gamma ty, WF_Type gamma ty -> 
    forall x ty', WF_Type (update gamma x ty') ty)
  (lookup_update_eq : forall gamma X ty, lookup (update gamma X ty) X ty) 
  (lookup_update_neq : forall gamma Y X ty ty', lookup gamma X ty -> X <> Y -> 
    lookup (update gamma Y ty') X ty)
  (lookup_update_neq' : forall gamma Y X ty ty',     lookup (update gamma Y ty') X ty -> X <> Y -> 
    lookup gamma X ty)
  (lookup_Empty : forall X ty, ~ lookup Empty X ty)
  (lookup_id : forall gamma X ty ty', lookup gamma X ty -> lookup gamma X ty' -> ty = ty')
  (Subtype_Update_list_id : forall (gamma : Context) (S T : Ty) (sub_S_T : subtype gamma S T),
  Subtype_Update_list_id_P X Ty Context subtype update gamma S T sub_S_T)
  (WF_fields_map_update : forall gamma ty ty' x ty'', WF_fields_map gamma ty ty' ->
    WF_fields_map (update gamma x ty'') ty ty').

  Definition WF_Config_SUpdate_Fresh_P gamma sigma :=
    WF_Config gamma sigma -> forall oid f c x' ty, 
      (HLookup_Field sigma oid f (LJ_Val_Wrap Null) \/
        (exists oid' : O,
          HLookup_Field sigma oid f (LJ_Val_Wrap (Oid oid')) /\
          (exists ty' : FJ_Ty,
            HLookup_Type sigma oid' ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty'))) -> 
      HLookup_Field sigma oid f c -> 
      SFresh sigma x' -> 
      WF_Config (update gamma (var x') ty) (SUpdate sigma (var x') c).

  Lemma LJ_WF_Config_SUpdate_Fresh :
    forall gamma sigma,
      LJ_WF_Config gamma sigma -> forall oid f c x' ty, 
        (HLookup_Field sigma oid f (LJ_Val_Wrap Null) \/
          (exists oid' : O,
            HLookup_Field sigma oid f (LJ_Val_Wrap (Oid oid')) /\
            (exists ty' : FJ_Ty,
              HLookup_Type sigma oid' ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty'))) -> 
        HLookup_Field sigma oid f c -> 
        SFresh sigma x' -> 
        LJ_WF_Config (update gamma (var x') ty) (SUpdate sigma (var x') c).
    unfold LJ_WF_Config; intros; destruct H as [WF_S [WF_H WF_H']]; 
      repeat split; intros.
    destruct x.
    destruct (X_eq_dec x x'); subst.
    destruct H0 as [c_Null | [o' [HTLookup_oid [ty' [HTLookup_oid' [sub_ty_ty' WF_ty']]]]]].
    rewrite (HLookup_Field_id _ _ _ _ _ c_Null H1); left; eauto.
    rewrite (HLookup_Field_id _ _ _ _ _ H1 HTLookup_oid); right;
      exists o'; split; eauto.
    exists ty'; repeat split; eauto.
    rewrite (lookup_id _ _ _ _ H (lookup_update_eq _ _ _)); auto.
    eauto.
    assert (cFJ.var X x <> var x') by 
      (unfold not; intros G; apply n; injection G; auto); clear n.
    apply lookup_update_neq' in H; auto.
    destruct (WF_S _ _ H) as [x_Null | [o' [SLookup_x [ty' [HTLookup_o' [sub_ty'_ty WF_ty']]]]]].
    left; eauto.
    right; repeat (eexists _; split); eauto.
    assert (cFJ.this X <> var x') by (unfold not; intros G; discriminate).
    apply lookup_update_neq' in H; auto.
    destruct (WF_S _ _ H) as [x_Null | [o' [SLookup_x [ty' [HTLookup_o' [sub_ty'_ty WF_ty']]]]]].
    left; eauto.
    right; repeat (eexists _; split); eauto.
    apply HFLookup_SUpdate' in H; 
      destruct (WF_H _ _ _ H) as [ty' HLookup_oid]; exists ty'; eauto.
    apply HTLookup_SUpdate' in H.
    destruct (WF_H' _ _ H) as [fds [fields_ty0 H3]]; repeat eexists _; repeat split; eauto; intros.
    destruct (H3 _ _ _ H4) as [Lookup_Null_f | 
      [oid' [Lookup_oid0 [ty' [Lookup_oid' [sub_ty'_ty WF_ty']]]]]].
    left; eauto.
    right; repeat (eexists _; split); try split; eauto.
  Qed.

  Variable (LJ_Val_Wrap_inject : forall v v', LJ_Val_Wrap v = LJ_Val_Wrap v' -> v = v')
    (fields_id : forall delta ty fds ty_fields,
      fields_id_P C F _ Ty FJ_Ty_Wrap _ fields delta ty fds ty_fields)
    (WF_fields_map_sub : forall gamma c tye tye' fds fds', 
      WF_fields_map gamma (FJ_Ty_Wrap (ty_def _ _ tye c)) (FJ_Ty_Wrap (ty_def _ _ tye' c)) ->
      fields Empty (FJ_Ty_Wrap (ty_def _ _ tye c)) fds -> 
      fields Empty (FJ_Ty_Wrap (ty_def _ _ tye' c)) fds' -> 
      List_P2' (fun fd' fd'' => match fd', fd'' with fd S' _, fd T' _ => subtype Empty S' T' end) fds fds')
    (Subtype_Weaken : forall (gamma : Context) (S T : Ty) (sub_S_T : subtype gamma S T),
      Subtype_Weaken_P Ty Context subtype Empty gamma S T sub_S_T)
    (WF_Config_SUpdate_Fresh : forall sigma gamma, WF_Config_SUpdate_Fresh_P sigma gamma)
    (SLookup_HUpdate : forall sigma x v o ty fds_vals, 
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
    (HFLookup_id : forall sigma o f val val',
      HLookup_Field sigma o f val -> HLookup_Field sigma o f val' -> val = val')
    (O_eq_dec : forall (o o' : O), {o = o'} + {o <> o'}).

  Lemma LJ_Field_Reduce_H2 : forall sigma x f oid c x' lookup_x Hlookup_oid Fresh_x, 
    E_preservation_P _ _ _ _ (LJ_Field_Reduce_Wrap _ _ _ _ 
      (R_Field_Read sigma x f oid c x' lookup_x Hlookup_oid Fresh_x)).
    unfold E_preservation_P; intros; rename H into WF_sigma;
      rename H0 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    generalize (LJ_imp_WF_Config _ _ WF_sigma) as WF_sigma'; intros; 
      destruct WF_sigma' as [SWF_sig [HWF_T_sig HWF_F_sig]].
    apply FJ_E_WF_invert in H0; inversion H0; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    destruct (SWF_sig _ _ H4) as [Null_a | [oid' [oid_y' [ty'' [HLookup_oid' [sub_ty''_ty0 WF_ty''']]]]]].
    generalize (SLookup_id _ _ _ _ Null_a lookup_x); intros neq; 
      apply LJ_Val_Wrap_inject in neq; discriminate.
    generalize (SLookup_id _ _ _ _ oid_y' lookup_x); intros eq; 
      apply LJ_Val_Wrap_inject in eq; injection eq; intros; subst; clear eq.
    destruct (Lem_2_8 _ _ _ sub_ty''_ty0 _ _ H1 H2) as [S' [map_ty''' [fds'' [fields_S' sub_fds''_fds']]]].
    destruct ty''; destruct (WF_fields_map_id' _ _ _ _ map_ty'''); subst.
    destruct (HWF_F_sig _ _ HLookup_oid') as [fds' [fds_ty in_fds]].
    assert (exists fd_ty', nth_error fds' i = Some (fd _ _ fd_ty' f) /\ 
      subtype gamma fd_ty' ty ) as ith_fds'.
    generalize (WF_fields_map_sub _ _ _ _ _ _ map_ty''' fds_ty fields_S'); intros. 
    apply P2'_if_P2 in H; destruct H; caseEq (nth_error fds' i).
    destruct (H _ _ H6) as [ty'' [nth_fds'' sub_f0_ty']].
    rewrite (sub_fds''_fds' _ _ H3) in nth_fds''; injection nth_fds''; intros; subst.
    destruct f0; eexists t0; split; try (eapply Subtype_Weaken; eassumption; reflexivity).
    generalize i fds'' H6 (sub_fds''_fds' _ _ H3)
      (WF_fields_map_id _ _ _ fds_ty _ _ _ _ _ (refl_equal _ ) (refl_equal _) fields_S');
      clear; induction fds'; destruct fds''; destruct i; simpl; intros; try discriminate.
    injection H6; injection H; intros; subst; injection H0; intros; subst; auto.
    injection H0; intros; eauto.
    eapply Subtype_Weaken; try eassumption; reflexivity.
    generalize (sub_fds''_fds' _ _ H3); intros; rewrite (H5 _ H6) in H7; discriminate.
    destruct ith_fds' as [fd_Ty' [ith_fds' sub_ty_fd_Ty']].
    generalize (in_fds _ _ _ ith_fds'); intros.
    exists (update gamma (var x') fd_Ty'); split; try (exists fd_Ty'; repeat split; auto).
    eapply WF_Config_SUpdate_Fresh; eauto.
    apply E_WF_Wrap; econstructor; eauto.
    eapply Conservative_Extension_update; intros; eapply SFresh_lookup; eauto.
  Qed.

  Definition WF_Config_SUpdate_Fresh_P' gamma sigma :=
    WF_Config gamma sigma -> 
    forall x' ty o fds_vals fds vals,
      SFresh sigma x' -> 
      HFresh sigma o -> 
      fields Empty (FJ_Ty_Wrap ty) fds -> 
      zip fds vals (fun (fd' : FD) (val : Value) =>
        (match fd' with fd _ f => f end, val)) = Some fds_vals -> 
      (forall f o' n ty, nth_error fds_vals n = Some (f, LJ_Val_Wrap (Oid o')) ->
        nth_error fds n = Some (fd _ _ ty f) -> 
        exists ty', HLookup_Type sigma o' ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty') -> 
      WF_Type gamma ty -> 
      WF_Config (update gamma (var x') (FJ_Ty_Wrap ty))
      (HUpdate (SUpdate sigma (var x') (LJ_Val_Wrap (Oid o))) o ty fds_vals).
  
  Lemma LJ_WF_Config_SUpdate_Fresh' : forall gamma sigma, LJ_WF_Config gamma sigma -> 
    forall x' ty o fds_vals fds vals,
      SFresh sigma x' -> 
      HFresh sigma o -> 
      fields Empty (FJ_Ty_Wrap ty) fds -> 
      zip fds vals (fun (fd' : FD) (val : Value) =>
        (match fd' with fd _ f => f end, val)) = Some fds_vals -> 
      (forall f o' n ty, nth_error fds_vals n = Some (f, LJ_Val_Wrap (Oid o')) ->
        nth_error fds n = Some (fd _ _ ty f) -> 
        exists ty', HLookup_Type sigma o' ty' /\ subtype gamma ty' ty /\ WF_Type gamma ty') -> 
      WF_Type gamma ty -> 
      LJ_WF_Config (update gamma (var x') (FJ_Ty_Wrap ty))
      (HUpdate (SUpdate sigma (var x') (LJ_Val_Wrap (Oid o))) o ty fds_vals).
    unfold LJ_WF_Config; intros; destruct H as [WF_S [WF_H WF_H']]; 
      repeat split; intros.
    destruct x.
    destruct (X_eq_dec x x'); subst.
    right; repeat (eexists _; split); try split; eauto. 
    rewrite (lookup_id _ _ _ _ H (lookup_update_eq _ _ _)); eauto.
    apply FJ_subtype_Wrap; constructor.
    assert (cFJ.var X x <> var x') by 
      (unfold not; intros G; apply n; injection G; auto); clear n.
    apply lookup_update_neq' in H; auto.
    destruct (WF_S _ _ H) as [x_Null | [o' [SLookup_x [ty' [HTLookup_o' [sub_ty'_ty WF_ty']]]]]].
    left; apply SLookup_HUpdate; apply SLookup_update_neq; assumption.
    destruct (O_eq_dec o o'); subst.
    elimtype False; destruct H1 as [H1 _]; eapply (H1 _ HTLookup_o').
    right; exists o'; split; auto.
    exists ty'; repeat split; auto.
    assert (cFJ.this X <> var x') by (unfold not; intros G; discriminate).
    apply lookup_update_neq' in H; auto.
    destruct (WF_S _ _ H) as [x_Null | [o' [SLookup_x [ty' [HTLookup_o' [sub_ty'_ty WF_ty']]]]]].
    left; apply SLookup_HUpdate; apply SLookup_update_neq; assumption.
    destruct (O_eq_dec o o'); subst.
    elimtype False; destruct H1 as [H1 _]; eapply (H1 _ HTLookup_o').
    right; exists o'; split; auto.
    exists ty'; split; auto.
    destruct (O_eq_dec oid o); subst.
    eexists _; auto.
    apply HFLookup_HUpdate_neq' in H; auto; apply HFLookup_SUpdate' in H.
    destruct (WF_H _ _ _ H) as [ty' HLookup_oid]; exists ty'; auto.
    destruct (O_eq_dec o oid); subst.
    rewrite (HTLookup_id _ _ _ _ H (HTLookup_HUpdate_eq _ _ _ _)).
    exists fds; repeat split; auto; intros.
    assert (exists val, nth_error fds_vals n = Some (f, val)) as nth_val by 
      (generalize n vals fds H3 H6; clear; induction fds_vals; destruct n; 
      destruct vals; destruct fds; simpl; intros; try discriminate; 
        first [eexists _; reflexivity| 
          caseEq (zip fds vals
            (fun (fd' : FD) (val : Value) =>
              (match fd' with
                 | fd _ f => f
               end, val))); rewrite H in H3; try discriminate;
          destruct f0; injection H3; injection H6; intros; subst; eauto]);
      destruct nth_val as [val nth_vals].
    destruct (LJ_Val_invert val) as [Null_Val | [o' Oid_Val]]; subst.
    left; eapply HFLookup_HUpdate_eq; try eassumption.
    right; exists o'; split; try (eapply HFLookup_HUpdate_eq; try eassumption).
    destruct (H4 _ _ _ _ nth_vals H6) as [ty' [HTLookup_o' [sub_ty'_ty1 WF_ty']]].
    exists ty'; split.
    destruct (O_eq_dec o' oid); subst.
    elimtype False; destruct H1 as [H1 _]; eapply (H1 _ HTLookup_o').
    apply HTLookup_HUpdate_neq; auto; apply HFLookup_SUpdate'.
    eauto.
    apply HTLookup_HUpdate_neq' in H; auto; apply HTLookup_SUpdate' in H.
    destruct (WF_H' _ _ H) as [fds' [fields_ty fds_sub]].
    exists fds'; repeat split; auto; intros.
    destruct (fds_sub _ _ _ H6) as [VNull | [o' [HFLookup_o' [ty' [HTLookup_o' [WF_ty' sub_ty'_ty1]]]]]].
    left; apply HFLookup_HUpdate_neq; auto; apply HFLookup_SUpdate'.
    right; repeat (eexists _; split).
    apply HFLookup_HUpdate_neq; auto; apply HFLookup_SUpdate; eassumption.
    destruct (O_eq_dec o' o); subst.
    elimtype False; destruct H1 as [H1 _]; eapply (H1 _ HTLookup_o').
    apply HTLookup_HUpdate_neq; auto; apply HTLookup_SUpdate; eassumption.
    eauto.
  Qed.

  Variable (WF_Config_SUpdate_Fresh' : forall gamma sigma, WF_Config_SUpdate_Fresh_P' gamma sigma)
    (Fields_eq : forall gamma ty fds, fields gamma ty fds -> forall gamma' fds', fields gamma' ty fds' -> fds = fds').

  Lemma LJ_R_New_preservation : forall sigma xs ty vals o' x' fds fds_vals
    Fresh_o' Fresh_x' field_ty SLookup_xs build_fd_vals,
    E_preservation_P _ _ _ _ (LJ_New_Reduce_Wrap _ _ _ _ (R_New sigma xs ty vals o' x' fds
      fds_vals Fresh_o' Fresh_x' field_ty SLookup_xs build_fd_vals)).
    unfold E_preservation_P; intros; rename H into WF_sigma;
      rename H0 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    generalize (LJ_imp_WF_Config _ _ WF_sigma) as WF_sigma'; intros; 
      destruct WF_sigma' as [SWF_sig [HWF_T_sig HWF_F_sig]].
    exists (update gamma (var x') (FJ_Ty_Wrap (ty_def C ty_ext te cl))); split; 
      try (exists (FJ_Ty_Wrap (ty_def C ty_ext te cl)); repeat split; eauto).
    assert (List_P2' (lookup gamma) xs Ss0) as Lookup_xs by 
      (apply P2_if_P2'; apply P2'_if_P2 in H2; generalize H2 EWrap_inject FJ_E_WF_invert; clear; 
        unfold List_P2; intros; destruct H2 as [fnd_a nfnd_a]; split; intros;
          first [destruct (fnd_a _ _ (nth_error_map _ _ _ _ _ _ H)) as [b [nth_Ss0 WF_a]];
            apply FJ_E_WF_invert in WF_a; inversion WF_a; apply EWrap_inject in H0; 
              try discriminate; injection H0; intros; subst; clear H0; exists b; auto |
                apply (nfnd_a _ (nth_error_map' _ _ _ _ _ H))]).
    eapply WF_Config_SUpdate_Fresh'; eauto; intros.
    apply P2'_if_P2 in Lookup_xs; destruct Lookup_xs.
    assert (List_P2'
         (fun (fd' : cFJ.FD F Ty) (S : Ty) =>
          match fd' with
          | fd T _ => subtype gamma S T
          end) fds Ss0) as H3' by 
    (apply P2'_if_P2 in H3; generalize H3; rewrite <- (Fields_eq _ _ _ field_ty _ _ H1); 
      clear; intros; apply P2_if_P2'; destruct H3; split; intros;
        caseEq (nth_error Ss0 n);
        first [destruct (H _ _ H2) as [b [nth_fds sub_a_b]]; rewrite H1 in nth_fds; 
          injection nth_fds; intros; subst; exists t; split; auto | 
            rewrite (H0 _ H2) in H1; discriminate | 
              destruct (H _ _ H2) as [b [nth_fds sub_a_b]]; rewrite H1 in nth_fds; try discriminate |
                reflexivity]); clear H3; rename H3' into H3.
    apply P2'_if_P2 in H3; destruct H3.
    apply P2'_if_P2 in SLookup_xs; destruct SLookup_xs.
    caseEq (nth_error xs n).
    destruct (H5 _ _ H10) as [v' [nth_Ss0 lookup_v]].
    destruct (H3 _ _ H4) as [ty' [nth_fds sub_ty'_t]].
    destruct (H8 _ _ H10) as [val [nth_vals SLookup_v']].
    assert (val = LJ_Val_Wrap (Oid o'0)) as val_eq by 
      (generalize n fds_vals vals H build_fd_vals nth_vals; clear; induction fds;
        destruct n; destruct fds_vals; destruct vals; simpl; intros; try discriminate;
          caseEq (zip fds vals
            (fun (fd' : FD) (val : Value) =>
              (match fd' with
                 | fd _ f => f
               end, val))); rewrite H0 in build_fd_vals; try discriminate;
          first [destruct a; injection H; injection build_fd_vals; injection nth_vals; intros; subst; congruence | 
              injection build_fd_vals; intros; subst; eauto; eapply IHfds; try eassumption]); subst.
    destruct (SWF_sig _ _ lookup_v) as [Null_a | [oid' [oid_y' [ty'' [HLookup_oid' [WF_ty'' sub_ty''_ty0]]]]]].
    generalize (SLookup_id _ _ _ _ SLookup_v' Null_a); intros; apply LJ_Val_Wrap_inject in H11; discriminate.
    generalize (SLookup_id _ _ _ _ SLookup_v' oid_y'); intros; apply LJ_Val_Wrap_inject in H11; injection H11;
      intros; subst.
    exists ty''; repeat split; auto.
    rewrite nth_fds in nth_Ss0; injection nth_Ss0; intros; subst.
    apply FJ_subtype_Wrap; econstructor 2; eassumption.
    elimtype False; generalize n vals fds_vals (H9 _ H10) H build_fd_vals; clear; 
      induction fds; destruct vals; simpl; intros; try discriminate.
    injection build_fd_vals; intros; subst; destruct n; simpl in H0; discriminate.
    caseEq (zip fds vals
      (fun (fd' : FD) (val : Value) =>
        (match fd' with
           | fd _ f => f
         end, val))); rewrite H1 in build_fd_vals; try discriminate; destruct a;
    injection build_fd_vals; intros; subst.
    destruct n; simpl in H0, H; try discriminate; eauto.
    apply E_WF_Wrap; constructor; auto.
    apply FJ_subtype_Wrap; constructor.
    eapply Conservative_Extension_update; intros; eapply SFresh_lookup; eauto.
  Qed. 

  Variable (Conservative_WF_fields_map : forall gamma ty ty', WF_fields_map gamma ty ty' -> 
    forall gamma', Conservative_Extension gamma gamma' -> WF_fields_map gamma' ty ty').
  
  Lemma E_C_preservation_H1 : forall sigma e sigma' e' f Red_e_e', 
    E_preservation_P _ _ _ _ Red_e_e' ->
    E_preservation_P _ _ _ _ (RC_Field sigma e sigma' e' f Red_e_e').
    unfold E_preservation_P; intros.
    unfold E_preservation_P; intros; rename H into pres_rect; rename H0 into WF_sigma;
      rename H1 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    destruct (pres_rect _ _ WF_sigma H0) as [gamma' [WF_sigma' [ty'' [WF_e' [sub_ty' Cons_gamma']]]]].
    exists gamma'; split; auto.
    exists ty; repeat split; auto.
    destruct (Lem_2_8 _ _ _ sub_ty' _ _ (Conservative_WF_fields_map _ _ _ H1 _ Cons_gamma')  H2) as 
      [c'' [map_c'_c'' [fds' [fds_c'' nth_fds']]]].
    apply E_WF_Wrap; econstructor; eauto.
    eapply FJ_subtype_Wrap; constructor.
  Qed.

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

  Lemma E_C_preservation_H2 : forall sigma e sigma' e' mce m es Red_e_e',
    E_preservation_P _ _ _ _ Red_e_e' -> 
    E_preservation_P _ _ _ _ (RC_Invk_Recv sigma e sigma' e' mce m es Red_e_e').
    unfold E_preservation_P; intros; rename H into pres_rect; rename H0 into WF_sigma;
      rename H1 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    destruct (pres_rect _ _ WF_sigma H0) as
      [gamma' [WF_sigma' [ty'' [WF_e' [sub_ty' Cons_gamma']]]]].
    destruct (WF_mtype_ty_0_map_total gamma' _ _ sub_ty' ty_0' 
      (Conservative_WF_mtype_ty_0_map _ _ _ H1 _ Cons_gamma')) as [c'' map_c'_c''].
    destruct (Lem_2_9 _ _ _ sub_ty' _ _ _ _ _ _ _ _ _ 
      (Conservative_WF_mtype_ty_0_map _ _ _ H1 _ Cons_gamma') H2
      (Conservative_WF_mtype_U_map _ _ _ _ _ H4 _ Cons_gamma') 
      (Conservative_WF_mtype_Us_map _ _ _ _ _ H3 _ Cons_gamma')
      (Conservative_WF_mtype_ext _ _ _ H7 _ Cons_gamma')
      map_c'_c'') as [V [Vs [mtye1 [mtype_m_c' [V' [map_V_V' [sub_Vs_Us [sub_V'_U' WF_mtye1]]]]]]]].
    exists gamma'; split; auto.
    exists V'; repeat split; auto.
    apply E_WF_Wrap; econstructor; eauto.
    Existential 1 := Ss0.
    apply P2'_if_P2 in H5; destruct H5 as [fnd_es nfnd_es]; apply P2_if_P2'; split; intros.
    destruct (fnd_es _ _ H) as [b [nth_Ss0 WF_a]]; exists b; split; eauto.
    auto.
    apply P2'_if_P2 in H6; destruct H6 as [fnd_es nfnd_es]; apply P2_if_P2'; split; intros.
    destruct (fnd_es _ _ H) as [b [nth_Ss0 WF_a]]; exists b; split; eauto.
    auto.
  Qed.
    
  Lemma E_C_preservation_H3 : forall e mce m sigma es sigma' es' Red_es_es', 
    E_preservation_Q _ _ _ _ Red_es_es' -> 
    E_preservation_P _ _ _ _ (RC_Invk_Arg e mce m sigma es sigma' es' Red_es_es').
    unfold E_preservation_P; unfold E_preservation_Q; intros; rename H into pres_rect; 
      rename H0 into WF_sigma; rename H1 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    destruct (pres_rect _ _ WF_sigma H5) as
      [gamma' [WF_sigma' [ty'' [WF_e' [sub_ty' Cons_gamma']]]]].
    exists gamma'; split; auto.
    exists ty; repeat split; auto.
    apply E_WF_Wrap; econstructor; eauto.
    apply P2'_if_P2 in H6; destruct H6 as [fnd_Ss0 nfnd_Ss0]; 
      apply P2'_if_P2 in sub_ty'; destruct sub_ty' as [fnd_es nfnd_es]; apply P2_if_P2'; split; intros.
    destruct (fnd_es _ _ H) as [b [nth_Ss0 sub_a_b]]; 
      destruct (fnd_Ss0 _ _ nth_Ss0) as [c [nth_Us' sub_b_c]]; exists c; split; eauto.
    apply FJ_subtype_Wrap; econstructor 2; eauto.
    auto.
    apply FJ_subtype_Wrap; constructor.
  Qed.  

  Lemma E_C_preservation_H4 : forall ty sigma es sigma' es' Red_es_es', 
    E_preservation_Q _ _ _ _ Red_es_es' -> 
    E_preservation_P _ _ _ _ (RC_New_Arg ty sigma es sigma' es' Red_es_es').
    unfold E_preservation_P; unfold E_preservation_Q; intros; rename H into pres_rect; 
      rename H0 into WF_sigma; rename H1 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    destruct (pres_rect _ _ WF_sigma H2) as 
      [gamma' [WF_sigma' [ty'' [WF_e' [sub_ty' Cons_gamma']]]]].
    exists gamma'; split; auto.
    exists (FJ_Ty_Wrap (ty_def C ty_ext te cl)); repeat split; auto.
    apply E_WF_Wrap; econstructor; eauto.
    apply P2'_if_P2 in H3; destruct H3 as [fnd_Ss0 nfnd_Ss0]; 
      apply P2'_if_P2 in sub_ty'; destruct sub_ty' as [fnd_es nfnd_es]; apply P2_if_P2'; split; intros.
    destruct (fnd_es _ _ H) as [b [nth_Ss0 sub_a_b]]; 
      destruct (fnd_Ss0 _ _ nth_Ss0) as [c [nth_Us' sub_b_c]]; exists c; split; eauto.
    destruct c; apply FJ_subtype_Wrap; econstructor 2; eauto.
    auto.
    apply FJ_subtype_Wrap; constructor.
  Qed.
    
  Lemma E_C_preservation_H5 : forall e sigma e' sigma' es Red_e_e', 
    E_preservation_P _ _ _ _ Red_e_e' -> 
    E_preservation_Q _ _ _ _ (Reduce_T e sigma e' sigma' es Red_e_e').
    unfold E_preservation_P; unfold E_preservation_Q; intros; rename H into pres_rect; 
      rename H0 into WF_sigma; rename H1 into WF_e.
    inversion WF_e; subst.
    destruct (pres_rect _ _ WF_sigma H1) as [gamma' [WF_sigma' [ty'' [WF_e' [sub_ty' Cons_gamma']]]]].
    exists gamma'; split; auto.
    exists (ty'' :: Bs); repeat split; auto; constructor; auto.
    apply P2'_if_P2 in H3; destruct H3 as [fnd_es nfnd_es]; apply P2_if_P2'; split; intros.
    destruct (fnd_es _ _ H) as [b' [nth_Bs E_WF_b']]; exists b'; split; eauto.
    auto.
    apply P2_if_P2'; split; eauto.
    intros; exists a; split; auto; apply FJ_subtype_Wrap; constructor.
  Qed.
    
  Lemma E_C_preservation_H6 : forall e sigma es sigma' es' Red_es_es', 
    E_preservation_Q _ _ _ _ Red_es_es' -> 
    E_preservation_Q _ _ _ _ (Reduce_P e sigma es sigma' es' Red_es_es').
    unfold E_preservation_P; unfold E_preservation_Q; intros; rename H into pres_rect; 
      rename H0 into WF_sigma; rename H1 into WF_e.          
    inversion WF_e; subst; intros.
    destruct (pres_rect _ _ WF_sigma H3) as [gamma' [WF_sigma' [tys'' [WF_es' [sub_tys' Cons_gamma']]]]].
    exists gamma'; split; auto.
    exists (b :: tys''); repeat split; auto; constructor; eauto.
    apply FJ_subtype_Wrap; constructor.
  Qed.

  Lemma LJ_M_Call_Reduce_H1 : forall sigma mce x m xs SLookup_x,
    E_preservation_P _ _ _ _ (LJ_M_Call_Reduce_Wrap _ _ _ _ (R_Invk_NPE sigma mce x m xs SLookup_x)).
    unfold E_preservation_P; intros; rename H into WF_sigma;
      rename H0 into WF_e.
    exists gamma; split; try (exists ty; repeat split; auto).
    eauto.
    apply FJ_subtype_Wrap; constructor.
  Qed.
  
  Variables (WF_mb_ext : Context -> mb_ext -> Prop)
    (Lem_2_10 : forall (gamma : Context) (e : E) (T : Ty) (WF_e : E_WF gamma e T),
      Term_subst_pres_typ_P _ Ty E Context subtype E_WF update trans gamma e
      T WF_e)
    (Lem_2_12 : forall m C_0 mce mbe xs e,
      mbody Empty mce m C_0 (mb mbe xs e) -> forall C_0' delta Ds Ds' D D' mtye, 
        mtype Empty m C_0' (mty _ _ mtye Ds D) -> 
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

  Definition Lem_2_10_S_P delta' s (WF_s : S_WF delta' s) :=
    forall delta xs ds S T Ss Vars x', delta' = (update_list delta Vars) ->
      zip (this :: xs) (S :: Ss) (@pair _ _) = Some Vars -> 
      List_P2' (fun x => E_WF delta (e_var (var x))) (x' :: ds) ((FJ_Ty_Wrap T) :: Ss) ->
      E_WF delta (e_var (var x')) T -> subtype delta T S -> 
      S_WF delta (S_trans s (this :: xs) (x' :: ds)).

  Definition Lem_2_10_S_Q delta' ss (WF_ss : List_P1 (S_WF delta') ss) :=
    forall delta xs ds S T Ss Vars x', delta' = (update_list delta Vars) ->
      zip (this :: xs) (S :: Ss) (@pair _ _) = Some Vars -> 
      List_P2' (fun x => E_WF delta (e_var (var x))) (x' :: ds) ((FJ_Ty_Wrap T) :: Ss) -> 
      E_WF delta (e_var (var x')) T -> subtype delta T S -> 
      List_P1 (S_WF delta) (map (fun s => S_trans s (this :: xs) (x' :: ds)) ss).

  Variable (S_trans_Wrap : forall s vars es', S_trans (LJ_S_Wrap s) vars es' = LJ_S_trans s vars es').

  Lemma Lem_2_10_S_H1 : forall gamma v e S T lookup_x WF_e sub_S_T, 
    Lem_2_10_S_P _ _ (T_Var_Assign gamma v e S T lookup_x WF_e sub_S_T).
    unfold Lem_2_10_S_P; intros; subst.
    assert (List_P2' (E_WF delta) (map (fun x => FJ_E_Wrap (e_var (var x))) (x' :: ds)) ((FJ_Ty_Wrap T0) :: Ss0)).
    apply P2_if_P2'; apply P2'_if_P2 in H1; destruct H1 as [fnd_ds nfnd_ds]; split; intros.
    caseEq (nth_error (x' :: ds) n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ _ H1) in H;
      injection H; intros; subst; auto.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ H1) in H;
      discriminate.
    caseEq (nth_error (x' :: ds) n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ _ H1) in H;
      discriminate.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ H1) in H; subst; auto.
    clear H1; rename H into H1.
    destruct (Lem_2_10 _ _ _ WF_e _ _ _ _ _ _ (refl_equal _) H0 H1) as [S' [WF_e_S' sub_S0_S']].
    constructor; auto.
    apply P2_if_P2'; split; intros; auto; eexists _; split; eauto; apply FJ_subtype_Wrap; constructor.
    apply LJ_S_WF_Wrap; rewrite S_trans_Wrap; simpl in *|-*; econstructor.
    Existential 2 := T.
    generalize ds Ss0 Vars FJ_E_WF_invert E_WF_Wrap EWrap_inject lookup_x lookup_id lookup_update_eq
      lookup_update_neq lookup_update_neq' H1 H0; clear; induction xs; destruct Ss0; destruct ds; simpl; 
        intros; try discriminate; try (injection H0; intros; subst; inversion H1; assumption).
    injection H0; intros; subst; simpl in lookup_x.
    apply (lookup_update_neq' _ _ _ _ _ lookup_x); unfold not; intros; discriminate.
    injection H0; intros; subst; simpl in lookup_x.
    apply (lookup_update_neq' _ _ _ _ _ lookup_x); unfold not; intros; discriminate.
    caseEq (zip xs Ss0 (@pair _ _)); rewrite H in H0; try discriminate; injection H0;
      intros; subst.
    destruct a.
    destruct (X_eq_dec v x); subst; simpl in *|-*.
    apply lookup_update_neq' in lookup_x.
    inversion H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    inversion H7.
    unfold not; intros; discriminate.
    apply lookup_update_neq' in lookup_x.
    inversion H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    inversion H7.
    unfold not; intros; discriminate.
    apply lookup_update_neq' in lookup_x.
    inversion H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    inversion H7.
    unfold not; intros; discriminate.
    caseEq (zip xs Ss0 (@pair _ _)); rewrite H in H0; try discriminate; injection H0;
      intros; subst.
    destruct a.
    destruct (X_eq_dec v x0); subst; simpl in *|-*.
    apply lookup_update_neq' in lookup_x.
    inversion H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    inversion H7; subst.
    rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)).
    apply FJ_E_WF_invert in H9; inversion H9; subst; apply EWrap_inject in H4;
      try discriminate H4; injection H4; intros; subst.
    assumption.
    unfold not; intros; discriminate.
    apply lookup_update_neq' in lookup_x.
    inversion H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    inversion H7; subst.
    apply (IHxs ds Ss0 ((this, S1) :: l)); auto.
    simpl.
    eapply lookup_update_neq.
    eapply (lookup_update_neq' _ _ _ _ _ lookup_x); unfold not; intros; apply n; injection H4; auto.
    unfold not; intro; discriminate.
    constructor; auto.
    rewrite H; reflexivity.
    unfold not; intro; discriminate.
    apply (IHxs ds Ss0 ((this, S1) :: l)); auto.
    simpl in *|-*.
    eapply lookup_update_neq.
    apply lookup_update_neq' in lookup_x.
    apply lookup_update_neq' in lookup_x.
    assumption.
    unfold not; intro; discriminate.
    unfold not; intro; discriminate.
    unfold not; intro; discriminate.
    inversion H1; subst; inversion H7; subst.
    repeat constructor; auto.
    rewrite H; reflexivity.
    inversion H1; subst; auto.
    eassumption.
    apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    try eapply Subtype_Update_list_id; try eassumption; try reflexivity; eauto.
  Qed.
    
  Variables (WF_fields_map_update_list : forall delta Vars ty ty', 
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
  (WF_mtype_ext_update_list_id : forall delta mce mtye Vars, 
    WF_mtype_ext (update_list delta Vars) mce mtye -> WF_mtype_ext delta mce mtye)
  (WF_Type_update_list_id : forall delta Vars ty, WF_Type (update_list delta Vars) ty ->
    WF_Type delta ty).

  Lemma Lem_2_10_S_H2 : forall gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T,
    Lem_2_10_S_P _ _ 
    (T_Field_Assign gamma x f e S T V V' fds i lookup_x map_V_V' fields_V' fnd_f WF_e sub_S_T).
    unfold Lem_2_10_S_P; intros; subst.
    assert (List_P2' (E_WF delta) (map (fun x => FJ_E_Wrap (e_var (var x))) (x' :: ds)) ((FJ_Ty_Wrap T0) :: Ss0)).
    apply P2_if_P2'; apply P2'_if_P2 in H1; destruct H1 as [fnd_ds nfnd_ds]; split; intros.
    caseEq (nth_error (x' :: ds) n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ _ H1) in H;
      injection H; intros; subst; auto.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ H1) in H;
      discriminate.
    caseEq (nth_error (x' :: ds) n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ _ H1) in H;
      discriminate.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) _ _ H1) in H; subst; auto.
    clear H1; rename H into H1.
    destruct (Lem_2_10 _ _ _ WF_e _ _ _ _ _ _ (refl_equal _) H0 H1) as [S' [WF_e_S' sub_S0_S']].
    constructor; auto.
    apply P2_if_P2'; split; intros; auto; eexists _; split; eauto; apply FJ_subtype_Wrap; constructor.
    destruct x.
    apply LJ_S_WF_Wrap; rewrite S_trans_Wrap; simpl in *|-*; econstructor.
    Existential 3 := V.
    clear WF_e_S'.
    generalize ds Ss0 Vars FJ_E_WF_invert E_WF_Wrap EWrap_inject lookup_x lookup_id lookup_update_eq
      lookup_update_neq lookup_update_neq' H1 H0; clear; induction xs; destruct Ss0; destruct ds; simpl; 
        intros; try discriminate; try (injection H0; intros; subst; inversion H1; assumption).
    injection H0; intros; subst; simpl in lookup_x.
    apply (lookup_update_neq' _ _ _ _ _ lookup_x); unfold not; intros; discriminate.
    injection H0; intros; subst; simpl in lookup_x.
    apply (lookup_update_neq' _ _ _ _ _ lookup_x); unfold not; intros; discriminate.
    caseEq (zip xs Ss0 (@pair _ _)); rewrite H in H0; try discriminate; injection H0;
      intros; subst.
    inversion H1; subst; inversion H7.
    caseEq (zip xs Ss0 (@pair _ _)); rewrite H in H0; try discriminate; injection H0;
      intros; subst.
    destruct a.
    destruct (X_eq_dec x x1); subst; simpl in *|-*.
    inversion  H1; subst; apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H2;
      try discriminate H2; injection H2; intros; subst.
    apply lookup_update_neq' in lookup_x.
    rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)).
    inversion H7; subst.
    apply FJ_E_WF_invert in H9; inversion H9; subst; apply EWrap_inject in H4; try discriminate;
      injection H4; intros; subst; assumption.
    unfold not; intros; discriminate.
    apply (IHxs ds Ss0 ((this, S1) :: l)); auto.
    simpl in *|-*.
    eapply lookup_update_neq.
    apply lookup_update_neq' in lookup_x.
    apply lookup_update_neq' in lookup_x.
    assumption.
    unfold not; intro; apply n; injection H2; auto.
    unfold not; intro; discriminate.
    unfold not; intro; discriminate.
    inversion H1; subst; inversion H7; subst.
    repeat constructor; auto.
    rewrite H; reflexivity.
    inversion H1; subst; auto.
    apply (IHxs ds Ss0 ((this, S1) :: l)); auto.
    simpl in *|-*.
    eapply lookup_update_neq.
    apply lookup_update_neq' in lookup_x.
    apply lookup_update_neq' in lookup_x.
    assumption.
    unfold not; intro; discriminate.
    unfold not; intro; discriminate.
    unfold not; intro; discriminate.
    inversion H1; subst; inversion H7; subst.
    repeat constructor; auto.
    rewrite H; reflexivity.
    eauto.
    eassumption.
    eauto.
    eassumption.
    apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    eapply Subtype_Update_list_id; eauto.
    simpl in H0; caseEq (zip xs Ss0 (@pair _ _)); rewrite H in H0; try discriminate; injection H0;
      intros; subst.    
    rewrite (lookup_id _ _ _ _ lookup_x (lookup_update_eq _ _ _)) in *|-*.
    apply WF_fields_map_update_list in map_V_V'.
    destruct (Lem_2_8 _ _ _ H3 _ _ map_V_V' fields_V') as 
      [S'' [map_ty''' [fds'' [fields_S' sub_fds''_fds']]]].
    apply FJ_E_WF_invert in H2; inversion H2; subst; apply EWrap_inject in H4; try discriminate;
      injection H4; intros; subst; clear H4.
    apply LJ_S_WF_Wrap; rewrite S_trans_Wrap; simpl in *|-*; econstructor.
    eassumption.
    eassumption.
    eassumption.
    eauto.
    eassumption.
    apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    eapply Subtype_Update_list_id with (vars := (this, _) :: l); simpl; try reflexivity; try eassumption.
  Qed.

  Lemma Lem_2_10_S_H3 : forall gamma ss P1_ss, 
    Lem_2_10_S_Q gamma ss P1_ss -> Lem_2_10_S_P _ _ (T_Block gamma ss P1_ss).
    unfold Lem_2_10_S_Q; unfold Lem_2_10_S_P; intros.
    apply LJ_S_WF_Wrap; rewrite S_trans_Wrap; simpl in *|-*; econstructor.
    eapply H; eauto.
  Qed.

  Lemma Lem_2_10_S_H4 : forall gamma, Lem_2_10_S_Q _ _ (Nil (S_WF gamma)).
    unfold Lem_2_10_S_Q; unfold Lem_2_10_S_P; intros.
    constructor.
  Qed.

  Lemma Lem_2_10_S_H5 : forall gamma s ss' WF_s WF_ss', Lem_2_10_S_P gamma s WF_s -> 
    Lem_2_10_S_Q gamma ss' WF_ss' ->
    Lem_2_10_S_Q gamma (s :: ss') (Cons_a _ s ss' WF_s WF_ss').
    unfold Lem_2_10_S_Q; unfold Lem_2_10_S_P; intros.
    constructor; eauto.
    generalize (H0 _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5); clear; induction ss'; simpl; intros; auto.
  Qed.

  Inductive LJ_WF_mb_ext (gamma : Context) : LJ_mb_ext -> Prop :=
    lj_WF_mb_ext : forall ss mbe', List_P1 (S_WF gamma) ss -> LJ_WF_mb_ext gamma (ss, mbe').

  Variable
    (mtype_build_tys : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> list Ty -> list Ty -> Prop)
    (mtype_build_mtye : cld_ext -> ty_ext -> Ty -> list VD -> md_ext -> mty_ext -> Prop)
    (Meth_build_context : cld_ext -> md_ext -> Context -> Context -> Prop)
    (wf_class_ext : Context -> cld_ext -> ty_ext -> Prop)
    (ce_build_cte : cld_ext -> ty_ext -> Prop)
    (map_s_invert : forall ce te mce mde (s : LJ_S) s', 
      map_s ce te mce mde s s' -> LJ_map_S ce te mce mde s s')
    (LJ_S_Wrap_inject : forall s s', LJ_S_Wrap s = LJ_S_Wrap s' -> s = s')
    (L_build_context : cld_ext -> Context -> Prop)
    (L_WF_Ext : Context -> cld_ext -> C -> Prop)
    (Build_S0'' : forall ce me gamma gamma' te te' c vds S0 T0 delta e e' D D' mtye mce
      Ds Ds' Vars (ce_WF : L_WF_Ext gamma' ce c)
      (build_gamma' : L_build_context ce gamma')
      (wf_me : Meth_WF_Ext gamma ce me)
      (build_te' : ce_build_cte ce te'),
      Meth_build_context ce me (update_list Empty ((this, FJ_Ty_Wrap (ty_def _ _ te' (cl _ c))) :: 
        (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
      E_WF gamma e S0 -> subtype gamma S0 T0 -> wf_class_ext delta ce te -> 
      mtype_build_mtye ce te T0 vds me mtye -> 
      map_mbody ce te mce me e e' ->
      mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) -> 
      WF_mtype_U_map delta mce mtye D D' ->
      WF_mtype_ext delta mce mtye ->
      WF_mtype_Us_map delta mce mtye Ds Ds' -> 
      List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
      zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
      (FJ_Ty_Wrap (ty_def _ _ te (cl _ c)) :: Ds') (@pair _ _) = Some Vars ->
      mtype_build_tys ce te T0 vds me (map (fun vd' : VD => match vd' with
                                                              | vd ty _ => ty
                                                            end) vds) Ds -> 
      exists S0'', 
        subtype delta S0'' D' /\ 
        E_WF (update_list delta Vars) e' S0'')
    (Map_S_WF : forall ce me gamma gamma' te te' c vds T0 delta s s' D D' mtye mce
      Ds Ds' Vars (ce_WF : L_WF_Ext gamma' ce c)
      (build_gamma' : L_build_context ce gamma')
      (wf_me : Meth_WF_Ext gamma ce me)
      (build_te' : ce_build_cte ce te'),
      Meth_build_context ce me (update_list Empty ((this, FJ_Ty_Wrap (ty_def _ _ te' (cl _ c))) :: 
        (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma -> 
      S_WF gamma s -> wf_class_ext delta ce te -> 
      mtype_build_mtye ce te T0 vds me mtye -> 
      map_s ce te mce me s s' ->
      mtype_build_tys ce te T0 vds me (T0 :: nil) (D :: nil) -> 
      WF_mtype_U_map delta mce mtye D D' ->
      WF_mtype_ext delta mce mtye ->
      WF_mtype_Us_map delta mce mtye Ds Ds' -> 
      List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds ->
      zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) ) 
      (FJ_Ty_Wrap (ty_def _ _ te (cl _ c)) :: Ds') (@pair _ _) = Some Vars ->
      mtype_build_tys ce te T0 vds me (map (fun vd' : VD => match vd' with
                                                              | vd ty _ => ty
                                                            end) vds) Ds -> 
      S_WF (update_list delta Vars) s').

  (* (Map_WF_S : forall ce me gamma te te' c vds T0 delta s s' D D' mtye mce *)
  (*     Ds Ds' te'' Vars,   *)
  (*     Meth_build_context ce me (update_list Empty ((this, FJ_Ty_Wrap (ty_def _ _ te' (cl _ c))) ::  *)
  (*       (map (fun Tx => match Tx with | vd ty x => (var x, ty) end) vds))) gamma ->  *)
  (*     S_WF gamma s -> WF_Type delta (FJ_Ty_Wrap (ty_def _ _ te (cl _ c))) ->  *)
  (*     map_s (mbody_m_call_map ce te mce me) (mbody_new_map ce te mce me) s s' -> *)
  (*     mtype_build_tys ce te (T0 :: nil) (D :: nil) -> WF_mtype_U_map delta mce mtye D D' -> *)
  (*     WF_mtype_ext delta mce mtye -> *)
  (*     WF_mtype_Us_map delta mce mtye Ds Ds' ->  *)
  (*     List_P1 (fun Tx => match Tx with | vd ty _ => WF_Type gamma ty end) vds -> *)
  (*     zip (this :: (map (fun Tx => match Tx with | vd _ x => var x end) vds) )  *)
  (*     (FJ_Ty_Wrap (ty_def _ _ te'' (cl _ c)) :: Ds') (@pair _ _) = Some Vars -> *)
  (*     mtype_build_tys ce te'' (map (fun vd' : VD => match vd' with *)
  (*                                                     | vd ty _ => ty *)
  (*                                                   end) vds) Ds ->  *)
  (*     S_WF (update_list delta Vars) s'). *)

  Section LJ_Map_S_id.

    Variable (map_mbody_id : forall ce te mce mde e e', map_mbody ce te mce mde e e' -> e = e').      

    Definition LJ_Map_S_id_P (s : S)  :=
      forall ce te mce mde s', map_s ce te mce mde s s' -> s = s'.

    Definition LJ_Map_S_id_Q (ss : list S) :=
      forall ce te mce mde ss', List_P2' (map_s ce te mce mde) ss ss' -> ss = ss'.
    
    Lemma LJ_Map_S_id_H1 : forall var e, LJ_Map_S_id_P (var_assign var e).
      unfold LJ_Map_S_id_P; intros.
      apply map_s_invert in H; inversion H; subst.
      rewrite (map_mbody_id _ _ _ _ _ _ H5); reflexivity.
      apply LJ_S_Wrap_inject in H0; discriminate.
      apply LJ_S_Wrap_inject in H0; discriminate.
    Defined.

    Lemma LJ_Map_S_id_H2 : forall x f e, LJ_Map_S_id_P (field_assign x f e).
      unfold LJ_Map_S_id_P; intros.
      apply map_s_invert in H; inversion H; subst.
      apply LJ_S_Wrap_inject in H0; discriminate.
      rewrite (map_mbody_id _ _ _ _ _ _ H5); reflexivity.
      apply LJ_S_Wrap_inject in H0; discriminate.
    Defined.

    Lemma LJ_Map_S_id_H3 : forall ss, LJ_Map_S_id_Q ss -> LJ_Map_S_id_P (block ss).
      unfold LJ_Map_S_id_P; unfold LJ_Map_S_id_Q; intros.
      apply map_s_invert in H0; inversion H0; subst;
        apply LJ_S_Wrap_inject in H1; try discriminate.
      injection H1; intros; subst.
      rewrite (H _ _ _ _ _ H6); reflexivity.
    Defined.

    Lemma LJ_Map_S_id_H4 : LJ_Map_S_id_Q nil.
      unfold LJ_Map_S_id_Q; intros.
      inversion H; reflexivity.
    Defined.

    Lemma LJ_Map_S_id_H5 : forall s ss', LJ_Map_S_id_P s -> LJ_Map_S_id_Q ss' -> LJ_Map_S_id_Q (s :: ss').
      unfold LJ_Map_S_id_P; unfold LJ_Map_S_id_Q; intros.
      inversion H1; subst.
      rewrite (H0 _ _ _ _ _ H6); rewrite (H _ _ _ _ _  H4); reflexivity.
    Qed.
        
  End LJ_Map_S_id.    
           
(***  Lemma LJ_WF_Build_mb_ext {Meth_WF_Ext' : Context -> cld_ext -> md_def_ext -> Prop} :
    forall (ce : cld_ext) (me : LJ_md_ext) (gamma : Context) (te te' : ty_ext) 
    (c : C) (vds : list (cFJ.VD X Ty)) (T0 : Ty) (delta : Context) 
    (D D' : Ty) (mtye : mty_ext) (mce : m_call_ext) (mbe : LJ_mb_ext) 
    (Ds Ds' : list Ty) (te'' : ty_ext) (Vars : list (cFJ.Var X * Ty)),
    @LJ_Meth_WF_Ext Meth_WF_Ext' gamma ce me -> 
    Meth_build_context ce me (cFJ.update_list X Ty Context update Empty
      ((cFJ.this X, FJ_Ty_Wrap (ty_def C ty_ext te' (cl C c))) :: 
        map (fun Tx : cFJ.VD X Ty => match Tx with
                                       | vd ty x => (cFJ.var X x, ty)
                                     end) vds)) gamma ->
    WF_Type delta (FJ_Ty_Wrap (ty_def C ty_ext te (cl C c))) ->
    LJ_build_mb_ext ce te mce me mbe ->
    mtype_build_tys ce te (T0 :: nil) (D :: nil) ->
    WF_mtype_U_map delta mce mtye D D' ->
    WF_mtype_ext delta mce mtye ->
    WF_mtype_Us_map delta mce mtye Ds Ds' ->
    List_P1 (fun Tx : cFJ.VD X Ty => match Tx with
                                        | vd ty _ => WF_Type gamma ty
                                      end) vds ->
    zip (cFJ.this X :: map (fun Tx : cFJ.VD X Ty => match Tx with
                                                        | vd _ x => cFJ.var X x
                                                      end) vds)
    (FJ_Ty_Wrap (ty_def C ty_ext te'' (cl C c)) :: Ds') (@pair _ _) = Some Vars ->
    mtype_build_tys ce te'' (map (fun vd' : cFJ.VD X Ty => match vd' with
                                                              | vd ty _ => ty
                                                            end) vds) Ds ->
    LJ_WF_mb_ext (cFJ.update_list X Ty Context update delta Vars) mbe.
    unfold LJ_Meth_WF_Ext; intros.
    inversion H2; subst; constructor.
    assert (exists ss'', ss = ss'') as eq_ss'' by (eexists _; reflexivity); 
      destruct eq_ss'' as [ss'' eq_ss'']; rewrite eq_ss'' in H10 at 1; rewrite eq_ss'' in H10 at 1;
        rewrite eq_ss'' in H0, H2; clear eq_ss''.
    assert (exists ss''', ss' = ss''') as eq_ss''' by (eexists _; reflexivity); 
      destruct eq_ss''' as [ss''' eq_ss''']; rewrite eq_ss''' in H2; clear eq_ss'''.
    revert ss'' ss' H10 H H0 H2; induction ss; intros; inversion H10; subst; constructor.
    eapply Map_WF_S; try eassumption.
    simpl in H; destruct H as [WF_a _]; inversion WF_a; subst; eassumption.
    eapply IHss; try eassumption.
    simpl in H; destruct H as [WF_a WF_me']; inversion WF_a; subst; split; eassumption.
  Qed. ***)
  
  Variables (app_context : Context -> Context -> Context)
    (Lookup_app : forall gamma delta x ty, lookup gamma x ty -> lookup (app_context gamma delta) x ty)
    (Lookup_app' : forall gamma delta x ty, (forall ty', ~ lookup gamma x ty') -> lookup delta x ty -> 
      lookup (app_context gamma delta) x ty).

  Definition WF_Config_SUpdate_Fresh_P'' gamma sigma :=
    WF_Config gamma sigma -> 
    forall xs vs xs' xs'_vs xs'_Us',
      List_P2' (SLookup sigma) xs vs -> 
      List_P1 (SFresh sigma) xs' -> 
      distinct xs' -> 
      zip xs' vs (fun (x : X) (val : Value) => (var x, val)) = Some xs'_vs -> 
      (forall n oid' x ty, nth_error vs n = Some (LJ_Val_Wrap (Oid oid')) -> 
        nth_error xs'_Us' n = Some (x, ty) -> exists ty', 
        HLookup_Type sigma oid' ty' /\ subtype gamma ty' ty) -> 
      WF_Config (update_list gamma xs'_Us') (SUpdate_list sigma xs'_vs).

  Variable (Lem_2_10_S : forall gamma s WF_s, Lem_2_10_S_P gamma s WF_s)
    (WF_mb_ext_imp_WF_Ss : forall gamma mbe, 
    WF_mb_ext gamma mbe -> S_WF gamma (MB_ext_S mbe))
  (WF_Config_push : forall gamma sigma s, 
    WF_Config gamma sigma -> S_WF gamma s -> WF_Config gamma (Push_mb_ext sigma s))
  (WF_Config_SUpdate_Fresh'' : forall gamma sigma, WF_Config_SUpdate_Fresh_P'' gamma sigma)
  (WF_mtype_ty_0_map_cl_id'' : forall delta te d S', 
    WF_mtype_ty_0_map delta (FJ_Ty_Wrap (ty_def _ _ te d)) S' -> S' = FJ_Ty_Wrap (ty_def _ _ te d))
  (subtype_ordered : forall gamma S T V, subtype gamma S T -> subtype gamma S V -> 
    (subtype gamma T V \/ subtype gamma V T))
  (Update_WF_mtype_ty_0_map : forall  gamma ty_0 ty_0' x ty, WF_mtype_ty_0_map gamma ty_0 ty_0' -> 
    WF_mtype_ty_0_map (update gamma x ty) ty_0 ty_0')
  (Update_WF_mtype_Us_map : forall gamma mce mtye Us Us' x ty, WF_mtype_Us_map gamma mce mtye Us Us' -> 
    WF_mtype_Us_map (update gamma x ty) mce mtye Us Us') 
  (Update_WF_mtype_U_map : forall gamma mce mtye U U' x ty, WF_mtype_U_map gamma mce mtye U U' -> 
    WF_mtype_U_map (update gamma x ty) mce mtye U U')
  (Update_WF_mtype_ext : forall gamma mce mtye x ty, WF_mtype_ext gamma mce mtye -> 
    WF_mtype_ext (update gamma x ty) mce mtye)
  (Conservative_Extension_trans : forall gamma gamma' gamma'', Conservative_Extension gamma gamma' ->
    Conservative_Extension gamma' gamma'' -> Conservative_Extension gamma gamma'')
  (LJ_S_WF_invert : forall gamma s, S_WF gamma (LJ_S_Wrap s) -> LJ_S_WF gamma s).

  Lemma Update_list_WF_mtype_ty_0_map : forall  gamma ty_0 ty_0' xs_tys, WF_mtype_ty_0_map gamma ty_0 ty_0' -> 
    WF_mtype_ty_0_map (update_list gamma xs_tys) ty_0 ty_0'.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.

  Lemma Update_list_WF_mtype_Us_map : forall gamma mce mtye Us Us' xs_tys, WF_mtype_Us_map gamma mce mtye Us Us'-> 
    WF_mtype_Us_map (update_list gamma xs_tys) mce mtye Us Us'.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.
    
  Lemma Update_list_WF_mtype_U_map : forall gamma mce mtye U U' xs_tys, WF_mtype_U_map gamma mce mtye U U' -> 
    WF_mtype_U_map (update_list gamma xs_tys) mce mtye U U'.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.

  Lemma Update_list_WF_mtype_ext : forall gamma mce mtye xs_tys, WF_mtype_ext gamma mce mtye -> 
    WF_mtype_ext (update_list gamma xs_tys) mce mtye.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.

  Lemma Update_list_subtype : forall gamma ty ty' xs_tys, subtype gamma ty ty' ->
    subtype (update_list gamma xs_tys) ty ty'.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.

  Lemma Update_list_WF_Type : forall gamma ty xs_tys, WF_Type gamma ty ->
    WF_Type (update_list gamma xs_tys) ty.
    induction xs_tys; simpl; intros; auto.
    destruct a; simpl; eauto.
  Qed.

  Lemma zip_length : forall {A B C : Type} (As : list A) (Bs : list B) (f : A -> B -> C) Cs, 
    zip As Bs f = Some Cs -> length As = length Bs /\ length Bs = length Cs.
    induction As; destruct Bs; simpl; intros; try discriminate.
    injection H; intros; subst; simpl; auto.
    caseEq (zip As Bs f); rewrite H0 in H; try discriminate; injection H; intros; subst.
    destruct (IHAs _ _ _ H0); subst; simpl; split; auto.
  Qed.

  Lemma List_P2'_length : forall {A B : Type} (P : A -> B -> Prop) As Bs, 
    List_P2' P As Bs -> length As = length Bs.
    clear; induction As; intros; inversion H; subst; simpl; auto.
  Qed.

  Lemma LJ_M_Call_Reduce_H2 : forall sigma mce x m xs mbe ys e oid ty x' xs' vs y_vs
    SLookup_x HLookup_oid mbody_m SFresh_x' SFresh_xs' distinct_xs' SLookup_xs build_y_vs,
    E_preservation_P _ _ _ _ (LJ_M_Call_Reduce_Wrap _ _ _ _ 
      (R_Invk sigma mce x m xs mbe ys e oid ty x' xs' vs y_vs
    SLookup_x HLookup_oid mbody_m SFresh_x' SFresh_xs' distinct_xs' SLookup_xs build_y_vs)).
    unfold E_preservation_P; intros; rename H into WF_sigma;
      rename H0 into WF_e.
    apply FJ_E_WF_invert in WF_e; inversion WF_e; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    apply FJ_E_WF_invert in H0; inversion H0; subst;
      apply EWrap_inject in H; try discriminate; injection H; intros; subst; clear H.
    generalize (LJ_imp_WF_Config _ _ WF_sigma) as WF_sigma'; intros; 
      destruct WF_sigma' as [SWF_sig [HWF_T_sig HWF_F_sig]].
    destruct (SWF_sig _ _ H8) as [Null_a | [oid' [oid_y' [ty'' [HLookup_oid' [sub_ty''_ty0 WF_ty'']]]]]].
    generalize (SLookup_id _ _ _ _ SLookup_x Null_a); intros SLookup_eq; 
      apply LJ_Val_Wrap_inject in SLookup_eq; discriminate.
    generalize (SLookup_id _ _ _ _ SLookup_x oid_y'); intros SLookup_eq; 
      apply LJ_Val_Wrap_inject in SLookup_eq; injection SLookup_eq; intros; subst; clear SLookup_eq.
    generalize (HTLookup_id _ _ _ _ HLookup_oid' HLookup_oid); intros HTLookup_eq; subst.
    destruct (WF_mtype_ty_0_map_total gamma _ _ sub_ty''_ty0 _ H1) as [c'' map_c'_c''].
    destruct ty; rewrite (WF_mtype_ty_0_map_cl_id'' _ _ _ _ map_c'_c'') in map_c'_c''.
    caseEq (zip (var x' :: (map var xs')) (FJ_Ty_Wrap (ty_def C ty_ext t c) :: Us') (@pair _ _)).
    rename l into xs'_Ss0.
    assert (List_P2' (fun x0 : X => E_WF (update_list gamma xs'_Ss0) (e_var (var x0))) (x' :: xs')
      (FJ_Ty_Wrap (ty_def C ty_ext t c) :: Us')) as WF_xs'.
    generalize H distinct_xs' E_WF_Wrap lookup_update_neq lookup_update_neq' lookup_update_eq; clear.
    assert (forall xs (tys : list Ty) xs_tys, zip (map var xs) tys (@pair _ _) = Some xs_tys -> 
      zip xs tys (fun x ty => (var x, ty)) = Some xs_tys) by 
    (clear; induction xs; destruct tys; simpl; intros; try discriminate; auto;
      caseEq (zip (map var xs) tys (@pair _ _)); rewrite H0 in H; destruct xs_tys; 
        try discriminate; injection H; intros; subst; rewrite (IHxs _ _ H0); auto).
    intro; apply (H (x' :: xs') (_ :: _)) in H0; revert H0.
    assert (exists l1 , l1 = x' :: xs') as H1 by 
      (eexists _; reflexivity); destruct H1 as [l1 l1_eq]; rewrite <- l1_eq.
    assert (exists l2 , l2 = FJ_Ty_Wrap (ty_def C ty_ext t c) :: Us') as H1 by 
      (eexists _; reflexivity); destruct H1 as [l2 l2_eq]; rewrite <- l2_eq.
    intros; assert (List_P2 (map var l1) l2 (lookup (update_list gamma xs'_Ss0))).
    split; intros.
    generalize a l1 l2 xs'_Ss0 H0 H1 distinct_xs' lookup_update_neq lookup_update_neq' 
      lookup_update_eq; clear; induction n; destruct l1; destruct l2; simpl; intros; 
        try discriminate; injection H1; intros; subst; clear H1.
    caseEq (zip l1 l2 (fun (x : X) (ty : Ty) => (var x, ty))); rewrite H in H0; try discriminate;
      injection H0; intros; subst.    
    exists t; split; simpl; auto.
    caseEq (zip l1 l2 (fun (x : X) (ty : Ty) => (var x, ty))); rewrite H1 in H0; try discriminate;
      injection H0; intros; subst.    
    destruct distinct_xs' as [NIn_x distinct_l1].
    assert (a <> (var x)) by 
      (generalize n a H NIn_x; clear; induction l1; destruct n;
        simpl; intros; try discriminate; injection H; intros; subst;
          first [unfold not; intros; apply NIn_x; left; injection H0; auto; fail |
            apply (IHl1 _ _ H0); unfold not; intro; auto]).
    destruct (IHn _ _ _ _ H1 H distinct_l1 lookup_update_neq lookup_update_neq' lookup_update_eq) as
      [b [nth_l2 lookup_l]].
    exists b; simpl; split; auto.
    generalize n l2 xs'_Ss0 H0 H1; clear; induction l1; destruct n; destruct l2; simpl; intros; 
      try discriminate; auto.
    caseEq (zip l1 l2 (fun (x : X) (ty : Ty) => (var x, ty))); rewrite H in H0; try discriminate;
      injection H0; intros; subst; eauto.
    apply P2_if_P2'; destruct H1; split; intros.
    destruct (H1 _ _ (nth_error_map _ _ _ _ _ _ H3)) as [U' [nth_l2 lookup_a]].
    exists U'; split; auto.
    apply E_WF_Wrap; constructor; auto.
    apply (H2 _ (nth_error_map' _ _ _ _ _ H3)).
    apply (Update_list_WF_mtype_ty_0_map _ _ _ xs'_Ss0) in H1.
    apply (Update_list_WF_mtype_U_map _ _ _ _ _ xs'_Ss0) in H4.
    apply (Update_list_WF_mtype_ty_0_map _ _ _ xs'_Ss0) in map_c'_c''.
    apply (Update_list_subtype _ _ _ xs'_Ss0) in sub_ty''_ty0.
    apply (Update_list_WF_mtype_Us_map _ _ _ _ _ xs'_Ss0) in H3.
    apply (Update_list_WF_mtype_ext _ _ _ xs'_Ss0) in H7.
    apply (Update_list_WF_Type _ _ xs'_Ss0) in WF_ty''.
    destruct (Lem_2_9 _ _ _ sub_ty''_ty0 _ _ _ _ _ _ _ _ _ H1 H2 H4 H3 H7 map_c'_c'') 
      as [V [Vs [mtye1 [mtype_c' [V' [map_V_V' [sub_Vs_Us [sub_V'_U' WF_mtye1]]]]]]]].
    destruct (Lem_2_12 _ _ _ _ _ _ mbody_m _ _ _ _ _ _ _ mtype_c' 
      map_c'_c'' WF_ty'' WF_mtye1 sub_Vs_Us map_V_V') as 
      [S' [Vars' [N [zip_eq [sub_N [WF_N [sub_S' [WF_e' WF_mbe]]]]]]]].
    exists (update_list gamma xs'_Ss0); split.
    apply WF_Config_push.
    eapply WF_Config_SUpdate_Fresh''; try assumption.
    apply (cons_P2' _ x (LJ_Val_Wrap (Oid oid')) xs vs); assumption.
    apply (Cons_a _ x' xs'); assumption.
    assumption.
    assumption.
    intros; destruct n; simpl in *|-*; destruct (xs'_Ss0); try discriminate.
    injection H9; injection H10; intros; subst; apply LJ_Val_Wrap_inject in H12; 
      injection H12; intros; subst; clear H9 H10 H12.
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H9 in H; try discriminate;
      injection H; intros; subst; clear H.    
    eexists _; split; try eassumption.
    apply FJ_subtype_Wrap; constructor.
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H11 in H; try discriminate;
      injection H; intros; subst; clear H.
    caseEq (zip (Xs_To_Vars ys) Us' (@pair _ _)); rewrite H in zip_eq; try discriminate;
      injection zip_eq; intros; subst; clear zip_eq.
    apply P2'_if_P2 in SLookup_xs; destruct SLookup_xs as [fnd_xs nfnd_xs].
    caseEq (nth_error xs n).
    destruct (fnd_xs _ _ H12) as [b [nth_vs SLookup_a]].
    rewrite nth_vs in H9; injection H9; intros; subst; clear H9.
    apply P2'_if_P2 in H5; destruct H5 as [fnd_xs' nfnd_xs'].
    destruct (fnd_xs' _ _ (nth_error_map _ _ _ _ _ _ H12)) as [b' [nth_vs' WF_v']].
    apply FJ_E_WF_invert in WF_v'; inversion WF_v'; subst;
      apply EWrap_inject in H5; try discriminate; injection H5; intros; subst; clear H5.
    destruct (SWF_sig _ _ H9) as [Null_a | [oid'' [oid_y'' [ty''' [HLookup_oid'' [sub_ty''_ty0' WF_ty''']]]]]].
    generalize (SLookup_id _ _ _ _ Null_a SLookup_a); intros; apply LJ_Val_Wrap_inject in H5;
      discriminate.
    generalize (SLookup_id _ _ _ _ oid_y'' SLookup_a); intros; apply LJ_Val_Wrap_inject in H5;
      injection H5; intros; subst; clear H5; eexists _; split; try eassumption.
    assert (nth_error Us' n = Some ty) as nth_Ss0' by 
      (generalize Us' n xs'_Ss0 H10 H11; clear; induction xs'; destruct Us'; destruct n; simpl;
        intros; try discriminate; try (injection H11; intros; subst; discriminate);
          caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H in H11; try discriminate;
            injection H11; intros; subst;
              first [injection H10; intros; subst; reflexivity | eauto]).
    apply P2'_if_P2 in H6; destruct H6 as [fnd_Us nfnd_Us].
    destruct (fnd_Us _ _ nth_vs') as [b [Lookup_Ss sub_ty_b]].
    rewrite Lookup_Ss in nth_Ss0'; injection nth_Ss0'; intros; subst.
    apply FJ_subtype_Wrap; econstructor 2; eassumption.
    rewrite (nfnd_xs _ H12) in H9; discriminate.
    (* generalize (WF_mb_ext_imp_WF_Ss _ _ WF_mbe); intros. *)
    eapply Lem_2_10_S; eauto.
    simpl in H; caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H9 in H; try discriminate;
      injection H; intros; subst.
    apply E_WF_Wrap; constructor; simpl; auto.
    destruct (Lem_2_10  _ _ _ WF_e' _ _ _ (map (fun x => FJ_E_Wrap (e_var (var x))) (x' :: xs')) 
      (FJ_Ty_Wrap (ty_def C ty_ext t c) :: Us') _ (refl_equal _) zip_eq) as [S'' [WF_e'_trans sub_S'']].
    inversion WF_xs'; subst.
    simpl; constructor; auto.
    apply P2'_if_P2 in H14; destruct H14 as [fnd_xs' nfnd_xs']; apply P2_if_P2'; split; intros.
    caseEq (nth_error xs' n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) xs' n x0 H10) in H9;
      injection H9; intros; subst; auto.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) xs' n H10) in H9;
      discriminate.
    caseEq (nth_error xs' n).
    rewrite (nth_error_map _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) xs' n x0 H10) in H9;
      discriminate.
    rewrite (nth_error_map' _ _ (fun x : X => FJ_E_Wrap (e_var (var x))) xs' n H10) in H9;
      auto.
    constructor; auto.
    apply P2'_if_P2 in H6; destruct H6 as [fnd_Ss0 nfnd_Ss0]; apply P2_if_P2'; split; intros.
    exists a; split; auto; apply FJ_subtype_Wrap; constructor.
    assumption.
    exists S''; repeat split; auto.
    apply FJ_subtype_Wrap; econstructor 2.
    apply sub_S''.
    apply FJ_subtype_Wrap; econstructor 2; eassumption.
    simpl in H; caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H9 in H; try discriminate;
      injection H; intros; subst.
    apply Conservative_Extension_trans with (gamma' := update_list gamma l).
    destruct distinct_xs' as [_ distinct_xs'].
    generalize Us' l H9 Conservative_Extension_update Conservative_Extension_trans distinct_xs' SFresh_xs' 
      SWF_sig Conservative_Extension_id X_eq_dec lookup_update_neq';
      clear; induction xs'; destruct Us'; simpl; intros; try discriminate;
        try (injection H9; intros; subst; simpl; auto; fail).
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H in H9; try discriminate; 
      injection H9; intros; subst; simpl.
    destruct distinct_xs'; inversion SFresh_xs'; subst;
      apply Conservative_Extension_trans with (gamma' := update_list gamma l0).
    apply (IHxs' _ _ H); auto.
    apply Conservative_Extension_update; intros.
    unfold not; intros; apply H0.
    generalize (fun ty => SFresh_lookup _ _ _ ty SWF_sig H4).
    generalize Us' l0 X_eq_dec lookup_update_neq' H H2; clear; 
      induction xs'; destruct Us'; simpl; intros; try discriminate;
        injection H; intros; subst.
    elimtype False; eapply (H0 _ H2).
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H3 in H; try discriminate; 
      injection H; intros; subst; simpl in *|-*.
    destruct (X_eq_dec a0 a); subst; auto.
    apply (lookup_update_neq' _ _ _ _) in H2.
    right; eauto.
    unfold not; intros; apply n; injection H4; auto.
    simpl.
    simpl; apply Conservative_Extension_update.
    unfold not; intros.
    intros; apply (SFresh_lookup _ _ _ ty SWF_sig SFresh_x').
    destruct distinct_xs' as [NIn_x' _].
    generalize Us' l H9 H10 NIn_x' lookup_update_neq'; clear; induction xs'; destruct Us'; simpl;
      intros; try discriminate.
    injection H9; intros; subst; auto.
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H in H9; try discriminate; 
      injection H9; intros; subst; simpl in *|-*.
    assert (a <> x') by (unfold not; intros; apply NIn_x'; auto).
    apply lookup_update_neq' in H10; eauto.
    unfold not; intros; apply H0; injection H1; auto.
    destruct (zip_length _ _ _ _ build_y_vs).
    generalize (List_P2'_length _ _ _ SLookup_xs); intros.
    generalize (List_P2'_length _ _ _ H5); intros; subst.
    generalize (List_P2'_length _ _ _ H6); intros; subst.
    simpl in H; caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H14 in H; try discriminate;
      subst; simpl in *|-*.
    injection H9; intros; subst; rewrite <- H15 in H9.
    rewrite H13 in H12; rewrite <- H11 in H15;
      elimtype False; generalize xs Us' vs H12 H14 H15; clear; induction xs';
        destruct Us'; destruct xs; simpl; intros; try discriminate.
    caseEq (zip (map var xs') Us' (@pair _ _)); rewrite H in H14; try discriminate;
      subst; simpl in *|-*.
    injection H12; injection H15; subst; intros; eauto.
  Qed.

  Definition S_preservation_P (sigma : Config) (ss : Ss) (sigma' : Config) (ss' : Ss) 
    (red_ss : S_Reduce sigma ss sigma' ss') :=
    forall gamma, WF_Config gamma sigma -> List_P1 (S_WF gamma) ss -> 
      exists gamma', WF_Config gamma' sigma' /\
        List_P1 (S_WF gamma') ss' /\  (Conservative_Extension gamma gamma').

  Lemma S_preservation_H1 : forall sigma ss npe_check, 
    S_preservation_P _ _ _ _ (LJ_S_Reduce_Wrap _ _ _ _ (R_NPE sigma ss npe_check)).
    unfold S_preservation_P; intros.
    exists gamma; repeat split; auto.
    constructor.
  Qed.

  Lemma List_P1_app : forall {A : Type} (P : A -> Prop) As Bs, List_P1 P As -> List_P1 P Bs ->
    List_P1 P (As ++ Bs).
    clear; induction As; simpl; intros; auto.
    inversion H; subst; constructor; auto.
  Qed.

  Lemma S_preservation_H2 : forall sigma ss ss' npe_check,
    S_preservation_P _ _ _ _ (LJ_S_Reduce_Wrap _ _ _ _ (R_Block sigma ss ss' npe_check)).
    unfold S_preservation_P; intros.
    exists gamma; repeat split; auto.
    inversion H0; subst; apply List_P1_app; auto.
    apply LJ_S_WF_invert in H3; inversion H3; subst; apply LJ_S_Wrap_inject in H1;
      try discriminate; injection H1; intros; subst.
    assumption.
  Qed.

  Lemma Var_eq_dec : forall (var' var'' : Var), {var' = var''} + {var' <> var''}.
    destruct var'; destruct var''; try (right; unfold not; intros; discriminate).
    destruct (X_eq_dec x x0); subst.
    left; reflexivity.
    right; unfold not; intros; apply n; injection H; auto.
    left; reflexivity.
  Qed.

  Lemma LJ_WF_Config_SUpdate : forall gamma sigma, LJ_WF_Config gamma sigma -> 
    forall var' v x' S T, lookup gamma var' T -> lookup gamma x' S -> SLookup sigma x' v -> 
      subtype gamma S T -> LJ_WF_Config gamma (SUpdate sigma var' v).
    unfold LJ_WF_Config; intros; destruct H as [WF_S [WF_H WF_H']]; 
      repeat split; intros; auto.
    destruct (Var_eq_dec var' x); subst.
    destruct (WF_S _ _ H1) as [Null_v | [oid [v_oid [S' [HLookup_oid [sub_S'_S WF_S']]]]]].
    left; rewrite (SLookup_id _ _ _ _ Null_v H2); auto.
    right; exists oid; rewrite (SLookup_id _ _ _ _ v_oid H2); repeat split; auto.
    rewrite (lookup_id _ _ _ _ H H0); exists S'; repeat split; auto.
    apply FJ_subtype_Wrap; econstructor 2; eassumption.
    destruct (WF_S _ _ H) as [Null_v | [oid [v_oid [S' [HLookup_oid [sub_S'_S WF_S']]]]]].
    left; auto.
    right; exists oid; split; auto; exists S'; repeat split; auto.
    apply HFLookup_SUpdate' in H; destruct (WF_H _ _ _ H) as [ty HTLookup_oid]; exists ty; auto.
    apply HTLookup_SUpdate' in H;
      destruct (WF_H' _ _ H) as [fds [fds_ty in_fds]]; exists fds; split; auto; intros.
    destruct (in_fds _ _ _ H4) as [Null_lookup | [o [o_lookup [ty' [HTLookup_o [sub_ty'_ty WF_ty']]]]]]; auto.
    right; exists o; split; auto; exists ty'; repeat split; auto.
  Qed.

  Definition WF_Config_SUpdate_P gamma sigma (_ : WF_Config gamma sigma) := 
    forall var' v x' S T, lookup gamma var' T -> lookup gamma x' S -> SLookup sigma x' v -> 
      subtype gamma S T -> WF_Config gamma (SUpdate sigma var' v).

  Variable (WF_Config_SUpdate : forall gamma sigma WF_gamma_sigma, WF_Config_SUpdate_P gamma sigma WF_gamma_sigma).

  Lemma S_preservation_H3 : forall sigma var' x v ss npe_check Lookup_x,
    S_preservation_P _ _ _ _ (LJ_S_Reduce_Wrap _ _ _ _ (R_Var_Assign sigma var' x v ss npe_check Lookup_x)).
    unfold S_preservation_P; intros.
    inversion H0; subst; exists gamma; repeat split; auto.
    apply LJ_S_WF_invert in H3; inversion H3; subst; apply LJ_S_Wrap_inject in H1;
      try discriminate; injection H1; intros; subst.
    apply FJ_E_WF_invert in H5; inversion H5; subst; apply EWrap_inject in H7; 
      try discriminate; injection H7; intros; subst.
    eapply WF_Config_SUpdate; eauto.
  Qed.

  Lemma S_preservation_H4 : forall sigma x f y ss Lookup_null,
    S_preservation_P _ _ _ _ (LJ_S_Reduce_Wrap _ _ _ _ (R_Field_Assign_NPE sigma x f y ss Lookup_null)).
    unfold S_preservation_P; intros.
    exists gamma; repeat split; auto.
    constructor.
  Qed.

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
  (F_eq_dec : forall f f' : F, {f = f'} + {f <> f'})
  (fds_distinct : forall gamma cl' fds, fields gamma cl' fds -> forall (cl1 cl2 : Ty) f m n fds',
    map (fun fd' => match fd' with fd _ f => f end) fds' = map (fun fd' => match fd' with fd _ f => f end) fds ->
    nth_error fds' m = Some (fd _ _ cl1 f) -> nth_error fds n = Some (fd _ _ cl2 f) -> m = n)
  (WF_fields_map_sub' : forall gamma c tye tye' fds fds', 
    WF_fields_map gamma (FJ_Ty_Wrap (ty_def _ _ tye c)) (FJ_Ty_Wrap (ty_def _ _ tye' c)) ->
    fields Empty (FJ_Ty_Wrap (ty_def _ _ tye c)) fds -> 
    fields Empty (FJ_Ty_Wrap (ty_def _ _ tye' c)) fds' -> 
    List_P2' (fun fd' fd'' => match fd', fd'' with fd S' _, fd T' _ => subtype Empty S' T' end) fds' fds).
  
  Lemma LJ_WF_Config_HFUpdate : forall gamma sigma, LJ_WF_Config gamma sigma -> 
    forall x v oid y f S V V' T i fds, WF_fields_map gamma V V' -> 
      SLookup sigma x (LJ_Val_Wrap (Oid oid)) -> 
      fields Empty V' fds -> nth_error fds i = Some (fd _ _ T f) -> 
      lookup gamma x V -> lookup gamma y S -> SLookup sigma y v -> 
      subtype gamma S T -> LJ_WF_Config gamma (HUpdate_Field sigma oid f v).
    unfold LJ_WF_Config; intros; destruct H as [WF_S [WF_H WF_H']]; 
      repeat split; intros; auto.
    destruct (WF_S _ _ H) as [Null_v | [oid' [v_oid' [S' [HLookup_oid' [sub_S'_S WF_S']]]]]].
    left; auto.
    right; exists oid'; split; auto; exists S'; repeat split; auto.
    destruct (O_eq_dec oid0 oid); subst.
    destruct (WF_S _ _ H4) as [Null_v | [oid' [v_oid' [S' [HLookup_oid' [sub_S'_S WF_S']]]]]].
    generalize (SLookup_id _ _ _ _ Null_v H1); intros; apply LJ_Val_Wrap_inject in H8;
      discriminate.
    generalize (SLookup_id _ _ _ _ v_oid' H1); intros; apply LJ_Val_Wrap_inject in H8;
      injection H8; intros; subst.
    exists S'; auto.
    apply HFLookup_HFUpdate_o_neq in H; auto; destruct (WF_H _ _ _ H) as [ty HTLookup_oid];
      exists ty; auto.
    apply HTLookup_HFUpdate' in H.
      destruct (WF_H' _ _ H) as [fds' [fds_ty in_fds]]; exists fds'; split; auto; intros.
    destruct (O_eq_dec oid0 oid); subst.
    destruct (F_eq_dec f0 f); subst.
    destruct (LJ_Val_invert v) as [Null_Val | [o' Oid_Val]]; subst; auto.
    right; exists o'; split; auto.
    destruct (WF_S _ _ H5) as [Null_v | [oid' [v_oid' [S' [HLookup_oid' [sub_S'_S WF_S']]]]]].
    generalize (SLookup_id _ _ _ _ Null_v H6); intros; apply LJ_Val_Wrap_inject in H9;
      discriminate.
    generalize (SLookup_id _ _ _ _ v_oid' H6); intros; apply LJ_Val_Wrap_inject in H9;
      injection H9; intros; subst.
    exists S'; repeat split; auto.
    destruct (WF_S _ _ H4) as [Null_v | [oid'' [v_oid'' [S'' [HLookup_oid'' [sub_S''_S WF_S'']]]]]].
    generalize (SLookup_id _ _ _ _ Null_v H1); intros; apply LJ_Val_Wrap_inject in H10;
      discriminate.
    generalize (SLookup_id _ _ _ _ v_oid'' H1); intros; apply LJ_Val_Wrap_inject in H10;
      injection H10; intros; subst.
    rewrite (HTLookup_id _ _ _ _ HLookup_oid'' H) in *|-*.
    apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    apply FJ_subtype_Wrap; econstructor 2; try eassumption.
    destruct (Lem_2_8 _ _ _ sub_S''_S _ _ H0 H2) as [ty' [WF_Map_ty [fds'' [fields_ty' subset_fds''_fds']]]].
    destruct ty.
    apply subset_fds''_fds' in H3.
    destruct (WF_fields_map_id' _ _ _ _ WF_Map_ty) as [t' eq_ty']; subst.
    generalize (WF_fields_map_id _ _ _ fds_ty _ _ _ _ _ 
      (refl_equal _) (refl_equal _) fields_ty') as map_fds'_fds''; intro.
    rewrite (fds_distinct _ _ _ fields_ty' _ _ _ _ _ _ (sym_eq map_fds'_fds'') H8 H3) in H8; 
      clear n map_fds'_fds''.
    destruct (P2'_if_P2 _ _ _ _ _ (WF_fields_map_sub' _ _ _ _ _ _ WF_Map_ty fds_ty fields_ty'))
      as [fnd_n nfnd_n].
    destruct (fnd_n _ _ H3) as [ty0' [nth_fds' sub_T_ty0']].
    eapply Subtype_Weaken; destruct ty0'; try reflexivity; apply FJ_subtype_Wrap; 
      econstructor 2; try eassumption.
    generalize FJ_subtype_Wrap fds' nth_fds' H8; clear.
    induction i; destruct fds'; simpl; intros; try discriminate.
    injection nth_fds'; injection H8; intros; subst; injection H0; intros; subst.
    apply FJ_subtype_Wrap; constructor.
    eapply IHi; eassumption.
    destruct (in_fds _ _ _ H8) as [HLookup_Null | HLookup_Val].
    left; eapply HFLookup_HFUpdate_f_neq'; eassumption.
    right; destruct HLookup_Val as [oid' [HFLookup_oid [ty' [HTLookup_oid' [sub_ty'_ty0 WF_ty']]]]];
      repeat (eexists _; repeat split); try eassumption.
    eapply HFLookup_HFUpdate_f_neq'; eassumption.
    eapply HTLookup_HFUpdate; eassumption.
    destruct (in_fds _ _ _ H8) as [HLookup_Null | HLookup_Val].
    left; eapply HFLookup_HFUpdate_o_neq'; eassumption.
    right; destruct HLookup_Val as [oid' [HFLookup_oid [ty' [HTLookup_oid' [sub_ty'_ty0 WF_ty']]]]];
      repeat (eexists _; repeat split); try eassumption.
    eapply HFLookup_HFUpdate_o_neq'; eassumption.
    eapply HTLookup_HFUpdate; eassumption.
  Qed.
  
  Variable (WF_Config_HFUpdate : forall gamma sigma, WF_Config gamma sigma -> 
    forall x v oid y f S V V' T i fds, WF_fields_map gamma V V' -> 
      SLookup sigma x (LJ_Val_Wrap (Oid oid)) -> 
      fields Empty V' fds -> nth_error fds i = Some (fd _ _ T f) -> 
      lookup gamma x V -> lookup gamma y S -> SLookup sigma y v -> 
      subtype gamma S T -> WF_Config gamma (HUpdate_Field sigma oid f v)).

  Lemma S_preservation_H5 : forall sigma x f y oid ss v check_npe SLookup_x SLookup_y,
    S_preservation_P _ _ _ _ (LJ_S_Reduce_Wrap _ _ _ _ 
      (R_Field_Assign sigma x f y oid ss v check_npe SLookup_x SLookup_y)).
    unfold S_preservation_P; intros.
    inversion H0; subst; clear H0; exists gamma; repeat split; auto.
    apply LJ_S_WF_invert in H3; inversion H3; subst; apply LJ_S_Wrap_inject in H0;
      try discriminate; injection H0; intros; subst.
    apply FJ_E_WF_invert in H7; inversion H7; subst; apply EWrap_inject in H9; 
      try discriminate; injection H9; intros; subst.
    eapply WF_Config_HFUpdate; try eassumption.
  Qed.

  Variable (E_preservation : forall sigma e sigma' e' red_e, E_preservation_P sigma e sigma' e' red_e)
    (WF_Config_Pop : forall gamma sigma s sigma', WF_Config gamma sigma -> Pop_mb_ext sigma s sigma' -> 
      WF_Config gamma sigma')
    (WF_S_Pop : forall gamma sigma s sigma', WF_Config gamma sigma -> Pop_mb_ext sigma s sigma' -> 
      S_WF gamma s)
    (Conservative_Extension_Lookup : forall gamma gamma' x v, lookup gamma x v -> Conservative_Extension gamma gamma' -> 
      lookup gamma' x v)
    (Conservative_Extension_S_WF : forall gamma gamma' s, S_WF gamma s -> Conservative_Extension gamma gamma' -> 
      S_WF gamma' s).    

  Lemma S_C_preservation_H1 : forall sigma sigma' sigma'' x f e e' ss s' check_npe reduce_e pop_s',
    S_preservation_P _ _ _ _ (LJ_C_S_Reduce_Wrap _ _ _ _ 
      (R_C_Field_Assign sigma sigma' sigma'' x f e e' ss s' check_npe reduce_e pop_s')).
    unfold S_preservation_P; intros.
    inversion H0; subst.
    apply LJ_S_WF_invert in H3; inversion H3; subst; apply LJ_S_Wrap_inject in H1; try discriminate;
      injection H1; intros; subst.
    destruct (E_preservation _ _ _ _ reduce_e _ _ H H8) as 
      [gamma' [WF_gamma [ty' [WF_e [sub_e conservative_gamma']]]]].
    exists gamma'; repeat split; eauto.
    repeat constructor.
    eauto.
    apply LJ_S_WF_Wrap; econstructor; eauto.
    eapply FJ_subtype_Wrap; econstructor 2; eauto.
    generalize Conservative_Extension_S_WF H4 conservative_gamma'; clear; induction ss; 
      intros; econstructor; inversion H4; subst; eauto.
  Qed.
  
  Lemma S_C_preservation_H2 : forall sigma sigma' sigma'' var e e' ss s' check_npe red_e pop_s',
    S_preservation_P _ _ _ _ (LJ_C_S_Reduce_Wrap _ _ _ _ 
      (R_C_Var_Assign sigma sigma' sigma'' var e e' ss s' check_npe red_e pop_s')).
    unfold S_preservation_P; intros.
    inversion H0; subst.
    apply LJ_S_WF_invert in H3; inversion H3; subst; apply LJ_S_Wrap_inject in H1; try discriminate;
      injection H1; intros; subst.
    destruct (E_preservation _ _ _ _ red_e _ _ H H5) as 
      [gamma' [WF_gamma [ty' [WF_e [sub_e conservative_gamma']]]]].
    exists gamma'; repeat split; eauto.
    repeat constructor.
    eauto.
    apply LJ_S_WF_Wrap; econstructor; eauto.
    eapply FJ_subtype_Wrap; econstructor 2; eauto.
    generalize Conservative_Extension_S_WF H4 conservative_gamma'; clear; induction ss; 
      intros; econstructor; inversion H4; subst; eauto.
  Qed.
    
End State.
