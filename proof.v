(* Test *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Arith.EqNat.
Require Import Maps.

Fixpoint list_rel { A : Type } (rel : A -> A -> Prop) (l l' : list A) : Prop :=
  match l, l' with
  | nil, nil => True
  | nil, _ => False
  | _, nil => False
  | x::xs, y::ys => rel x y /\ list_rel rel xs ys
  end.

Definition var_id := id.
Definition class_id := id.
Definition obj_id : class_id := Id 0.
Inductive var : Type :=
| Var : var_id -> var
| This : var.
Definition field_id := id.
Definition method_id := id.
Inductive expr : Type :=
| E_Var : var -> expr
| E_Field : expr -> field_id -> expr
| E_Invk : expr -> method_id -> list expr -> expr
| E_New : class_id -> list expr -> expr
| E_Cast : class_id -> expr -> expr.

Theorem expr_ind_list :
  forall P : expr -> Prop,
       (forall v : var, P (E_Var v)) ->
       (forall e : expr, P e -> forall f0 : field_id, P (E_Field e f0)) ->
       (forall e : expr, P e -> forall (m : method_id) (l : list expr), Forall P l -> P (E_Invk e m l)) ->
       (forall (c : class_id) (l : list expr), Forall P l -> P (E_New c l)) ->
       (forall (c : class_id) (e : expr), P e -> P (E_Cast c e)) -> forall e : expr, P e.
  intros P H H0 H1 H2 H3 e. apply expr_rect.
  - apply H.
  - apply H0.
  - admit.
  - admit.
  - admit.
Admitted.

Definition context := var -> class_id.

Definition params := list (class_id * var_id).
Inductive constr : Type :=
| Constr : class_id -> params -> list var_id -> list (field_id * var_id) -> constr.
Inductive method := Method : class_id -> method_id -> params -> expr -> method.

Inductive class : Type :=
| Obj : class
| C : class_id -> class_id -> list (class_id * field_id) -> constr -> list method -> class.

Definition class_table : Type := partial_map class * partial_map class.


Definition lookup (ct : class_table) (i : class_id) : option class :=
  match ct with (app, lib) =>
                match app i with
                | Some c => Some c
                | None => lib i
                end
  end.
Definition lookup_field (c : class) (f : field_id) : option class_id :=
  match c with
  | Obj => None
  | C _ _ fs _ _ => match find (fun fp => beq_id (snd fp) f) fs with
                   | None => None
                   | Some (ci, _) => Some ci
                   end
  end.
Definition lookup_method (c : class) (mi : method_id) : option method :=
  match c with
  | Obj => None
  | C _ _ _ _ ms => find (fun m => match m with Method _ mi' _ _ => beq_id mi mi' end) ms
  end.
Definition id_of (c : class) : class_id :=
  match c with
  | Obj => obj_id
  | C ci _ _ _ _ => ci
  end.

Definition par_id_of (c : class) : option class_id :=
  match c with
  | Obj => None
  | C _ di _ _ _ => Some di
  end.

Definition in_lib_id (ct : class_table) (i : class_id) : Prop :=
  match ct with (_, lib) => lib i <> None end.
                
Definition in_app_id (ct : class_table) (i : class_id) : Prop :=
  match ct with (app, _) => app i <> None end.

Definition in_lib (ct : class_table) (c : class) : Prop :=
  match ct with (_, lib) => lib (id_of c) <> None end.
                
Definition in_app (ct : class_table) (c : class) : Prop :=
  match ct with (app, _) => app (id_of c) <> None end.

Definition in_table_id (ct : class_table) (i : class_id) : Prop :=
  in_app_id ct i \/ in_lib_id ct i.

Definition in_table (ct : class_table) (c : class) : Prop :=
  in_app ct c \/ in_lib ct c.

Lemma in_app_in_table : forall (ct : class_table) (c : class),
    in_app ct c -> in_table ct c.
Proof. intros. unfold in_table. left. apply H. Qed.
Lemma in_lib_in_table : forall (ct : class_table) (c : class),
    in_lib ct c -> in_table ct c.
Proof. intros. unfold in_table. right. apply H. Qed.

Definition extends (ct : class_table) (c d : class) : Prop :=
  match c with
  | Obj => False
  | C _ di _ _ _ => lookup ct di = Some d
  end.

Definition extends_id (ct : class_table) (ci di : class_id) : Prop :=
  match lookup ct ci with
  | None => False
  | Some Obj => False
  | Some (C _ di' _ _ _) => di = di'
  end.

Inductive subtype (ct : class_table) : class -> class -> Prop :=
| S_Ref : forall (c : class), subtype ct c c
| S_Trans : forall (c d e : class), subtype ct c d -> subtype ct d e -> subtype ct c e
| S_Sub : forall (c d : class), extends ct c d -> subtype ct c d.

Inductive subtype_id (ct : class_table) : class_id -> class_id -> Prop :=
| SI_Ref : forall ci, in_table_id ct ci -> subtype_id ct ci ci
| SI_Sub : forall ci di, extends_id ct ci di -> subtype_id ct ci di
| SI_Trans : forall ci di ei, subtype_id ct ci di -> subtype_id ct di ei -> subtype_id ct ci ei.

Inductive valid_class (ct : class_table) : class -> Type :=
| ValidObj : in_lib ct Obj -> ~ in_app ct Obj -> lookup ct obj_id = Some Obj -> valid_class ct Obj
| ValidParent : forall c d,
    valid_class ct d -> extends ct c d ->
    ~ (in_lib ct c /\ in_app ct c) ->
    (in_lib ct d /\ in_table ct c) \/ (in_app ct d /\ in_app ct c)  ->
    lookup ct (id_of c) = Some c ->
    valid_class ct c.

Fixpoint mtype (ct : class_table) (mi : method_id) (c : class) (pfc : valid_class ct c) :
  option (list class_id * class_id) :=
  match pfc with
  | ValidObj _ _ _ _ => None
  | ValidParent _ d pfd _ _ _ _ _ =>
    match lookup_method c mi with
    | None => None
    | Some (Method ci _ l_arg _) => Some (map fst l_arg, ci) 
    end
  end.

Fixpoint fields (ct : class_table) (c : class) (pfc : valid_class ct c) : list class_id :=
  match pfc, c with
  | ValidObj _ _ _ _, _ => nil
  | ValidParent _ _ d pfd _ _ _ _ , C _ _ fs _ _ => map fst fs ++ fields ct d pfd
  | _, _ => nil
  end.

Inductive type_of (ct : class_table) (gamma : context) : expr -> class_id -> Prop :=
| T_Var : forall x, type_of ct gamma (E_Var x) (gamma x)
| T_Field : forall e c di f,
    type_of ct gamma e (id_of c) -> lookup_field c f = Some di ->
    type_of ct gamma (E_Field e f) di
| T_Invk : forall e0 c0 ci0 pfc0 ld ret mi le lc,
    id_of c0 = ci0 -> type_of ct gamma e0 ci0 -> mtype ct mi c0 pfc0 = Some (ld, ret) ->
    length ld = length le -> length le = length lc ->
    Forall (fun p => type_of ct gamma (fst p) (snd p)) (combine le lc) ->
    Forall (fun p => subtype_id ct (fst p) (snd p)) (combine lc ld) ->
    type_of ct gamma (E_Invk e0 mi le) ci0
| T_New : forall c ci pfc le lc ld,
    id_of c = ci -> fields ct c pfc = ld ->
    length ld = length le -> length le = length lc ->
    Forall (fun p => type_of ct gamma (fst p) (snd p)) (combine le lc) ->
    Forall (fun p => subtype_id ct (fst p) (snd p)) (combine lc ld) ->
    type_of ct gamma (E_New ci le) ci
| T_Cast : forall e0 ci di, type_of ct gamma e0 di -> type_of ct gamma (E_Cast ci e0) ci.

Inductive type_checks (ct : class_table) (gamma : context) : expr -> Prop :=
| TC_Var : forall x, in_table_id ct (gamma x) -> type_checks ct gamma (E_Var x)
| TC_Field : forall e f di, type_of ct gamma (E_Field e f) di -> in_table_id ct di -> type_checks ct gamma e ->
                       type_checks ct gamma (E_Field e f)
| TC_Invk : forall e m le di, type_of ct gamma (E_Invk e m le) di -> in_table_id ct di ->
                      type_checks ct gamma e -> Forall (type_checks ct gamma) le ->
                      type_checks ct gamma (E_Invk e m le)
| TC_New : forall ci le, in_table_id ct ci -> Forall (type_checks ct gamma) le -> type_checks ct gamma (E_New ci le)
| TC_Cast : forall e di, in_table_id ct di -> type_checks ct gamma e -> type_checks ct gamma (E_Cast di e).
(*  exists c, type_of ct gamma e c /\ in_table_id ct c. *)

  
Definition valid_table (ct : class_table) : Type :=
  forall c, in_table ct c -> valid_class ct c.

Lemma extends_injective : forall ct c d d',
    valid_class ct c -> extends ct c d -> extends ct c d' -> d = d'.
Proof.
  intros ct c d d' pfc c_ext_d c_ext_d'.
  unfold extends in c_ext_d, c_ext_d'. destruct c as [| ci di k ms fs].
  - inversion c_ext_d.
  - rewrite c_ext_d in c_ext_d'. inversion c_ext_d'. reflexivity.
Qed.

Definition dmethods (c : class) : list method_id :=
  match c with
  | Obj => nil
  | C _ _ _ _ ms => map (fun m => match m with Method _ id _ _ => id end) ms
  end.

Fixpoint mresolve (ct : class_table) (m : method_id) (c : class) (pfc : valid_class ct c) : option class :=
  match pfc with
  | ValidObj _ _ _ _ => None
  | ValidParent _ _ d pfd _ _ _ _ => if (existsb (fun m' => beq_id m m') (dmethods c))
                                      then Some c
                                      else mresolve ct m d pfd
  end.

Lemma mres_lib_in_lib : forall (ct : class_table) (m : method_id) (c e : class) (pfc : valid_class ct c),
    in_lib ct c -> mresolve ct m c pfc = Some e -> in_lib ct e.
  intros ct m c e pfc c_in_lib c_res_e.
  induction pfc.
  - inversion c_res_e.
  - unfold mresolve in c_res_e. destruct (existsb (fun m' : id => beq_id m m') (dmethods c)) in c_res_e.
    + inversion c_res_e. rewrite <- H0. apply c_in_lib.
    + fold mresolve in c_res_e. apply IHpfc.
      * destruct o.
        -- destruct H. apply H.
        -- destruct n. split. apply c_in_lib. destruct H. apply H0.
      * apply c_res_e.
Qed.

Inductive ave_rel (ct ct' : class_table) : Prop :=
  | AveRel :  valid_table ct -> valid_table ct' ->
              (forall c, in_app ct c <-> in_app ct' c) ->
              (forall c d, extends ct c d -> in_table ct' c -> extends ct' c d) ->
              (forall c d, extends ct c d -> in_lib ct d -> in_table ct' c -> in_lib ct' d) ->
              ave_rel ct ct'.

Lemma lib'_subset_lib : forall (ct ct' : class_table) (c : class),
    ave_rel ct ct' -> in_table ct' c -> in_lib ct c -> in_lib ct' c.
Proof.
  intros. inversion H. unfold in_table in H0. destruct H0.
  - apply H2 in H0. unfold valid_table in X.
    assert (in_table ct c). { apply in_app_in_table. apply H0. }
    apply X in H5. inversion H5.
    + rewrite <- H9 in H0. unfold not in H7. apply H7 in H0. inversion H0.
    + destruct H8. split. apply H1. apply H0. 
  - apply H0.
Qed.

Inductive alpha (ct ct' : class_table) (pft : ave_rel ct ct') : expr * expr -> Prop :=
| Rel_Field : forall e e' f, alpha ct ct' pft (e, e') -> alpha ct ct' pft (E_Field e f, E_Field e' f)
| Rel_Invk : forall e e' le le' m, alpha ct ct' pft (e, e') -> length le = length le' -> Forall (alpha ct ct' pft) (combine le le') ->
                              alpha ct ct' pft (E_Invk e m le, E_Invk e' m le')
| Rel_New : forall ci le le', in_table_id ct' ci -> length le = length le' ->
                         Forall (alpha ct ct' pft) (combine le le') ->
                         alpha ct ct' pft (E_New ci le, E_New ci le')
| Rel_Cast : forall e e' c, alpha ct ct' pft (e, e') -> alpha ct ct' pft (E_Cast c e, E_Cast c e').

Definition subst := var -> expr.

Fixpoint do_sub (sig : subst) (e : expr) : expr :=
 match e with
 | E_Var v => sig v
 | E_Field e' f => E_Field (do_sub sig e') f
 | E_Invk e' m es => E_Invk (do_sub sig e') m (map (do_sub sig) es)
 | E_New c es => E_New c (map (do_sub sig) es)
 | E_Cast c e' => E_Cast c (do_sub sig e')
 end.

Lemma lemma1 : forall (ct : class_table) (c e : class) (m : method_id) (pfc : valid_class ct c),
    mresolve ct m c pfc = Some e -> in_app ct e -> in_app ct c.
Proof.
  intros ct c e m pfc c_res_e e_in_app. induction pfc as [ | c d pfd IHd c_ext_d not_lib_app sca look].
  - unfold mresolve in c_res_e. inversion c_res_e.
  - unfold mresolve in c_res_e. destruct (existsb (fun m' : id => beq_id m m') (dmethods c)) in c_res_e.
    + inversion c_res_e. apply e_in_app.
    + fold mresolve in c_res_e. apply IHd in c_res_e. destruct sca.
      * inversion pfd.
        -- rewrite <- H3 in c_res_e. unfold not in H1. apply H1 in c_res_e. inversion c_res_e.
        -- destruct H2. split. destruct H. apply H. apply c_res_e.
      * destruct H. apply H0.
Qed.

Lemma lemma2 : forall (ct ct' : class_table) (c e e' : class) (m : method_id)
                 (pfc : valid_class ct c) (pfc' : valid_class ct' c),
    in_app ct c -> mresolve ct m c pfc = Some e -> mresolve ct' m c pfc' = Some e'  -> ave_rel ct ct' ->
    in_app ct e \/ in_lib ct' e'.
Proof.
  intros ct ct' c e e' m pfc pfc' c_in_app c_res_e c_res_e' rel.
  induction pfc as [| c d pfd IHd c_ext_d not_lib_app app_ext_app].
  (* c is Obj *)
  - unfold mresolve in c_res_e. inversion c_res_e.
  (* c extends d *)
  - unfold mresolve in c_res_e; fold mresolve in c_res_e.
    destruct (existsb (fun m' : id => beq_id m m') (dmethods c)) eqn:m_res.
    (* m-res *)
    + inversion c_res_e; left; rewrite <- H0; eauto. 
    (* m-res-inh *)
    + inversion rel as [ct_val ct'_val keep_app keep_ext keep_lib].
      unfold mresolve in c_res_e'.
      (* can't induct on pfc and pfc' simultaneously,
         so manually destruct pfc' and show that it's the same parent *)
      destruct pfc' as [| c0 d0 pfd' c_ext_d'] eqn:pfc''.
      * inversion c_res_e'.
      * fold mresolve in c_res_e'. rewrite m_res in c_res_e'.
        assert (d = d0) as deq.
        { apply extends_injective with (ct := ct') (c := c0).
          -- apply pfc'.
          -- apply keep_ext.
             ++ apply c_ext_d.
             ++ apply in_app_in_table. apply keep_app. apply c_in_app.
          -- apply c_ext_d'. }
        destruct app_ext_app as [[d_in_lib _] | [d_in_app _]].
        (* d in lib - use averroes transformation properties *)
        -- right. apply mres_lib_in_lib with (m := m) (c := d0) (pfc := pfd').
           ++ apply keep_lib with (c := c0).
              ** rewrite <- deq. apply c_ext_d.
              ** rewrite <- deq. apply d_in_lib.
              ** apply in_app_in_table. apply keep_app. apply c_in_app.
           ++ apply c_res_e'.
        (* d in app - use induction hypothesis *)
        -- assert (forall pfc' : valid_class ct' d,
                      in_app ct d ->
                      mresolve ct' m d pfc' = Some e' -> in_app ct e \/ in_lib ct' e') as IHd'.
           { intros pfc'0 _ mres'. apply IHd with (pfc' := pfc'0).
             apply d_in_app. apply c_res_e. apply mres'. }
           rewrite deq in IHd'.
           apply IHd' with (pfc' := pfd').
           ++ rewrite <- deq. apply d_in_app.
           ++ apply c_res_e'.
Qed.

(* Lemma Forall_imp : forall (A : type) (l : list A)  *)

Lemma lemma3 : forall (ct ct' : class_table) (pft : ave_rel ct ct')
                 (sig sig' : subst) (gamma : context) (e0 : expr),
    (forall v, alpha ct ct' pft (sig v, sig' v)) -> type_checks ct' gamma e0 ->
    alpha ct ct' pft (do_sub sig e0, do_sub sig' e0).
Proof.
  intros ct ct' pft sig sig' gamma e0 rel typ_chk. induction e0 using expr_ind_list.
  - eauto.
  - simpl; apply Rel_Field. inversion typ_chk; eauto. 
  - simpl; apply Rel_Invk.
    + inversion typ_chk; eauto. 
    + rewrite map_length, map_length; reflexivity.
    + inversion typ_chk. clear H2; clear H3; clear typ_chk; induction l.
      * apply Forall_nil. 
      * inversion H; inversion H6. apply Forall_cons; eauto; eauto.
  - simpl. inversion typ_chk. apply Rel_New.
    + eauto.
    + rewrite map_length, map_length; reflexivity.
    + clear typ_chk; clear H1; induction l.
      * apply Forall_nil.
      * inversion H; inversion H3. apply Forall_cons; eauto; eauto.
  - apply Rel_Cast; inversion typ_chk; eauto.
Qed.
