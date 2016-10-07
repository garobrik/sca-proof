(* Test *)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Arith.EqNat.
Require Import Maps.
Require Import Program.Equality.

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

Inductive exprl : Type :=
| EL_Expr : expr -> exprl
| EL_Lib : exprl.

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

Definition empty_map {A : Type} : partial_map A := fun _ => None.
Definition ct_app (ct : class_table) : class_table :=
  match ct with (app, _) => (app, empty_map) end.
Definition ct_lib (ct : class_table) : class_table :=
  match ct with (_, lib) => (empty_map, lib) end.
Definition lookup (ct : class_table) (i : class_id) : option class :=
  match ct with (app, lib) =>
                match app i with
                | Some c => Some c
                | None => lib i
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
Lemma in_app_in_table_id : forall (ct : class_table) (ci : class_id),
    in_app_id ct ci -> in_table_id ct ci.
Proof. intros. unfold in_table_id. left. apply H. Qed.
Lemma in_lib_in_table_id : forall (ct : class_table) (ci : class_id),
    in_lib_id ct ci -> in_table_id ct ci.
Proof. intros. unfold in_table_id. right. apply H. Qed.

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

Inductive subtype (ct : class_table) : class -> class -> Type :=
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
  | ValidParent _ _ d pfd _ _ _ _  =>
    match lookup_method c mi with
    | None => mtype ct mi d pfd
    | Some (Method ci _ l_arg _) => Some (map fst l_arg, ci) 
    end
  end.

Fixpoint fields (ct : class_table) (c : class) (pfc : valid_class ct c) : list class_id :=
  match pfc, c with
  | ValidParent _ _ d pfd _ _ _ _ , C _ _ fs _ _ => map fst fs ++ fields ct d pfd
  | _, C _ _ fs _ _ => map fst fs
  | _, _ => nil
  end.

Definition lookup_field (ct : class_table) (c : class) (pfc : valid_class ct c) (f : field_id) : option class_id :=
  find (beq_id f) (fields ct c pfc).
Inductive type_of (ct : class_table) (gamma : context) : expr -> class_id -> Prop :=
| T_Var : forall x, type_of ct gamma (E_Var x) (gamma x)
| T_Field : forall e c pfc di f,
    type_of ct gamma e (id_of c) -> lookup_field ct c pfc f = Some di ->
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

Check type_of_ind.
Theorem type_of_ind_list : forall (ct : class_table) (gamma : context) (P : expr -> class_id -> Prop),
       (forall x : var, P (E_Var x) (gamma x)) ->
       (forall (e : expr) (c : class) (pfc : valid_class ct c) (di : class_id) (f0 : field_id),
        type_of ct gamma e (id_of c) -> P e (id_of c) -> lookup_field ct c pfc f0 = Some di -> P (E_Field e f0) di) ->
       (forall (e0 : expr) (c0 : class) (ci0 : class_id) (pfc0 : valid_class ct c0) (ld : list class_id)
          (ret : class_id) (mi : method_id) (le : list expr) (lc : list class_id),
        id_of c0 = ci0 ->
        type_of ct gamma e0 ci0 ->
        P e0 ci0 ->
        mtype ct mi c0 pfc0 = Some (ld, ret) ->
        length ld = length le ->
        length le = length lc ->
        Forall (fun p : expr * class_id => type_of ct gamma (fst p) (snd p)) (combine le lc) ->
        Forall (fun p : expr * class_id => P (fst p) (snd p)) (combine le lc) ->
        Forall (fun p : class_id * class_id => subtype_id ct (fst p) (snd p)) (combine lc ld) ->
        P (E_Invk e0 mi le) ci0) ->
       (forall (c : class) (ci : class_id) (pfc : valid_class ct c) (le : list expr) (lc ld : list class_id),
        id_of c = ci ->
        fields ct c pfc = ld ->
        length ld = length le ->
        length le = length lc ->
        Forall (fun p : expr * class_id => type_of ct gamma (fst p) (snd p)) (combine le lc) ->
        Forall (fun p : expr * class_id => P (fst p) (snd p)) (combine le lc) ->
        Forall (fun p : class_id * class_id => subtype_id ct (fst p) (snd p)) (combine lc ld) -> P (E_New ci le) ci) ->
       (forall (e0 : expr) (ci di : class_id), type_of ct gamma e0 di -> P e0 di -> P (E_Cast ci e0) ci) ->
       forall (e : expr) (c : class_id), type_of ct gamma e c -> P e c.
  admit.
Admitted.

Inductive type_checks (ct : class_table) (gamma : context) : expr -> Prop :=
| TC_Var : forall x, in_table_id ct (gamma x) -> type_checks ct gamma (E_Var x)
| TC_Field : forall e f di, type_of ct gamma (E_Field e f) di -> in_table_id ct di -> type_checks ct gamma e ->
                       type_checks ct gamma (E_Field e f)
| TC_New : forall ci le, in_table_id ct ci -> Forall (type_checks ct gamma) le -> type_checks ct gamma (E_New ci le)
| TC_Invk : forall e m le di, type_of ct gamma (E_Invk e m le) di -> in_table_id ct di ->
                      type_checks ct gamma e -> Forall (type_checks ct gamma) le ->
                      type_checks ct gamma (E_Invk e m le)
| TC_Cast : forall e di, in_table_id ct di -> type_checks ct gamma e -> type_checks ct gamma (E_Cast di e).

Definition dfields (c : class) : list field_id :=
  match c with
  | Obj => nil
  | C _ _ fs _ _ => map snd fs
  end.
Fixpoint declaring_class (ct : class_table) (c : class) (pfc : valid_class ct c) (f : field_id) : option class_id :=
  match pfc with
  | ValidObj _ _ _ _ => None
  | ValidParent _ _ d pfd _ _ _ _ => if (existsb (fun f' => beq_id f' f) (dfields c))
                                    then Some (id_of c)
                                    else declaring_class ct d pfd f
  end.
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

Inductive valid_expr (ct : class_table) (gamma : context) : expr -> Prop :=
| Val_Var : forall x, type_checks ct gamma (E_Var x) -> valid_expr ct gamma (E_Var x)
| Val_Field : forall e f ci c pfc,
    type_checks ct gamma (E_Field e f) ->
    type_of ct gamma e ci -> id_of c = ci ->
    declaring_class ct c pfc f <> None ->
    valid_expr ct gamma e ->
    valid_expr ct gamma (E_Field e f)
| Val_New : forall ci le,
    type_checks ct gamma (E_New ci le) ->
    Forall (valid_expr ct gamma) le ->
    valid_expr ct gamma (E_New ci le)
| Val_Invk : forall e m le ci c pfc,
    type_checks ct gamma (E_Invk e m le) ->
    valid_expr ct gamma e ->
    Forall (valid_expr ct gamma) le ->
    type_of ct gamma e ci -> id_of c = ci ->
    mresolve ct m c pfc <> None ->
    valid_expr ct gamma (E_Invk e m le)
| Val_Cast : forall ci e,
    type_checks ct gamma (E_Cast ci e) -> valid_expr ct gamma e -> valid_expr ct gamma (E_Cast ci e).
Inductive valid_table : class_table -> Prop :=
| VT : forall ct, (forall c, in_table ct c -> valid_class ct c) ->
             (forall c ci, lookup ct ci = Some c -> id_of c = ci) ->
             valid_table ct.

Lemma extends_injective : forall ct c d d',
    valid_class ct c -> extends ct c d -> extends ct c d' -> d = d'.
Proof.
  intros ct c d d' pfc c_ext_d c_ext_d'.
  unfold extends in c_ext_d, c_ext_d'. destruct c as [| ci di k ms fs].
  - inversion c_ext_d.
  - rewrite c_ext_d in c_ext_d'. inversion c_ext_d'. reflexivity.
Qed.

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
  - apply H4 in H0. destruct H2.
    assert (in_table ct c). { apply in_app_in_table. apply H0. }
    apply H2 in H8. inversion H8.
    + rewrite <- H12 in H0. unfold not in H10. apply H10 in H0. inversion H0.
    + destruct H11. split. apply H1. apply H0. 
  - apply H0.
Qed.

Inductive alpha (ct ct' : class_table) (pft : ave_rel ct ct') (gamma : context) : exprl * exprl -> Prop :=
| Rel_Field : forall e e' f,
    alpha ct ct' pft gamma (EL_Expr e, EL_Expr e') ->
    alpha ct ct' pft gamma (EL_Expr (E_Field e f), EL_Expr (E_Field e' f))
| Rel_Lib_Field : forall e ci c pfc f,
    alpha ct ct' pft gamma (EL_Expr e, EL_Lib) ->
    declaring_class ct c pfc f = Some ci -> in_lib_id ct ci ->
    type_of ct gamma e (id_of c) ->
    alpha ct ct' pft gamma (EL_Expr (E_Field e f), EL_Lib)
| Rel_New : forall ci le le', in_table_id ct' ci -> length le = length le' ->
                         Forall (alpha ct ct' pft gamma) (combine (map EL_Expr le) (map EL_Expr le')) ->
                         alpha ct ct' pft gamma (EL_Expr (E_New ci le), EL_Expr (E_New ci le'))
| Rel_Lib_New : forall ci le,
    in_lib_id ct ci -> Forall (fun e => alpha ct ct' pft gamma (EL_Expr e, EL_Lib)) le ->
    alpha ct ct' pft gamma (EL_Expr (E_New ci le), EL_Lib)
| Rel_Invk : forall e e' le le' m,
    alpha ct ct' pft gamma (EL_Expr e, EL_Expr e') ->
    length le = length le' ->
    Forall (alpha ct ct' pft gamma) (combine (map EL_Expr le) (map EL_Expr le')) ->
    alpha ct ct' pft gamma (EL_Expr (E_Invk e m le), EL_Expr (E_Invk e' m le'))
| Rel_Lib_Invk : forall e le mi,
    (exists c, in_lib ct c /\ In mi (dmethods c)) ->
    alpha ct ct' pft gamma (EL_Expr e, EL_Lib) ->
    Forall (fun e' => alpha ct ct' pft gamma (EL_Expr e', EL_Lib)) le ->
    alpha ct ct' pft gamma (EL_Expr (E_Invk e mi le), EL_Lib)
| Rel_Cast : forall e e' c, alpha ct ct' pft gamma (EL_Expr e, EL_Expr e') ->
                       alpha ct ct' pft gamma (EL_Expr (E_Cast c e), EL_Expr (E_Cast c e'))
| Rel_Lib_Cast : forall e ci,
    alpha ct ct' pft gamma (EL_Expr e, EL_Lib) -> alpha ct ct' pft gamma (EL_Expr (E_Cast ci e), EL_Lib).
    

Definition subst := var -> expr.

Fixpoint do_sub (sig : subst) (e : expr) : expr :=
 match e with
 | E_Var v => sig v
 | E_Field e' f => E_Field (do_sub sig e') f
 | E_Invk e' m es => E_Invk (do_sub sig e') m (map (do_sub sig) es)
 | E_New c es => E_New c (map (do_sub sig) es)
 | E_Cast c e' => E_Cast c (do_sub sig e')
 end.

Axiom sub_keep_typ : forall (ct : class_table) (sig : subst) (gamma : context) (e : expr) (c : class_id),
    type_of ct gamma e c -> type_of ct gamma (do_sub sig e) c.
Lemma eq_valid : forall (ct : class_table) (c d : class) (pfc : valid_class ct c),
    c = d -> valid_class ct d.
Proof.
  intros ct c d pfc cdeq.
  destruct pfc.
  - rewrite <- cdeq. apply ValidObj. trivial. trivial. trivial.
  - apply ValidParent with d0.
    + trivial.
    + rewrite <- cdeq. trivial.
    + rewrite <- cdeq. trivial.
    + rewrite <- cdeq. trivial.
    + rewrite <- cdeq. trivial.
Qed.

Lemma id_eq : forall (ct : class_table) c d (pfc : valid_class ct c) (pfd : valid_class ct d),
    id_of c = id_of d -> c = d.
Proof.
  intros ct c d pfc pfd eq_id.
  inversion pfc.
  - inversion pfd.
    + reflexivity.
    + rewrite <- H2 in eq_id; unfold id_of at 1 in eq_id; rewrite <- eq_id in H7.
      rewrite H1 in H7; inversion H7; reflexivity.
  - inversion pfd.
    + rewrite <- H8 in eq_id; unfold id_of at 2 in eq_id; rewrite eq_id in H3.
      rewrite H3 in H7; inversion H7; reflexivity.
    + rewrite eq_id in H3. rewrite H9 in H3. inversion H3. reflexivity.
Qed.

Lemma valid_in_table : forall (ct : class_table) (c : class) (pfc : valid_class ct c),
    in_table ct c.
Proof.
  intros ct c pfc. inversion pfc.
  - apply in_lib_in_table. apply H.
  - destruct H2.
    * apply H2.
    * apply in_app_in_table. apply H2.
Qed.

Lemma in_ct_lib_in_lib : forall (ct : class_table) (c : class),
    in_table (ct_lib ct) c -> in_lib ct c.
Proof.
  intros ct c in_ct_lib.
  unfold ct_lib, in_table in in_ct_lib; unfold in_lib; destruct ct.
  destruct in_ct_lib.
  - unfold in_app in H. unfold empty_map in H. destruct H. reflexivity.
  - unfold in_lib in H. apply H.
Qed.

Lemma valid_table_valid_lib : forall ct,
    valid_table ct -> valid_table (ct_lib ct).
Proof.
  intros. destruct H.
  apply VT.
  - intros.
    assert (valid_class ct c) as pfc.
    { apply H. apply in_lib_in_table. apply in_ct_lib_in_lib. trivial. }
    destruct ct as [app lib]. induction pfc.
    + apply ValidObj.
      * simpl. simpl in i. trivial.
      * simpl. unfold empty_map. unfold not. intros. apply H2. trivial.
      * simpl. simpl in e. simpl in n. destruct (app obj_id); trivial.
        unfold not in n. assert False. { apply n. intros. inversion H2. } contradiction.
    + apply ValidParent with d.
      * apply IHpfc. unfold in_table. simpl. right. inversion pfc; trivial.
        destruct o as [[don _] | [_ con]]; trivial.
        destruct n. split; trivial. apply in_ct_lib_in_lib. trivial.
      * destruct c; trivial.
        simpl. simpl in e. destruct (app c0) eqn:d_in_app; trivial.
        inversion e. rewrite H3 in d_in_app. destruct o.
        -- inversion pfc.
           ++ simpl in H5.
              assert (lookup (app, lib) c0 = Some d).
              { simpl. rewrite d_in_app. reflexivity. }
              apply H0 in H8. destruct H5. rewrite <- H7 in H8. simpl in H8. rewrite <- H8 in d_in_app.
              rewrite d_in_app. unfold not. intros. inversion H5.
           ++ destruct H2. destruct H6. split; trivial.
              simpl.
              assert (id_of d = c0).
              { apply H0. simpl. rewrite d_in_app. reflexivity. }
              rewrite H6. rewrite d_in_app. unfold not. intros. inversion H11.
        -- simpl in H1. unfold in_table in H1. destruct H1.
           ++ unfold empty_map in H1. simpl in H1. destruct H1. trivial.
           ++ simpl in H1. destruct H2. simpl in H4. destruct n. split; trivial.
      * simpl. unfold empty_map. unfold not. intros. destruct H2. apply H3. trivial.
      * left. split; trivial.
        destruct o; destruct H2; trivial.
        apply in_ct_lib_in_lib in H1. destruct n. split; trivial.
      * simpl. simpl in e0. destruct (app (id_of c)) eqn:c_in_app; trivial.
        apply in_ct_lib_in_lib in H1. destruct n. split; trivial.
        simpl. unfold not. intros. rewrite H2 in c_in_app. inversion c_in_app.
  - destruct ct as [app lib].
    intros. simpl in H1. apply H0. simpl. destruct (app ci) eqn:c_in_app; trivial.
    assert (id_of c0 = ci).
    { apply H0. simpl. rewrite c_in_app. reflexivity. }
    assert (valid_class (app, lib) c0).
    { apply H. unfold in_table. simpl. left. rewrite H2.
      unfold not. intro. rewrite c_in_app in H3. inversion H3. }
    inversion H3.
    + rewrite <- H7 in H2. simpl in H2. rewrite <- H2 in c_in_app. simpl in H5. destruct H5.
      unfold not. intro. rewrite H5 in c_in_app. inversion c_in_app.
    + destruct H6. simpl. split.
      * rewrite H2. unfold not. intro. rewrite H1 in H6. inversion H6.
      * rewrite H2. unfold not. intro. rewrite c_in_app in H6. inversion H6.
Qed.

Lemma in_ct_lib_in_lib_id : forall (ct : class_table) (ci : class_id),
    in_table_id (ct_lib ct) ci -> in_lib_id ct ci.
Proof.
  intros ct c in_ct_lib_id.
  unfold ct_lib, in_table_id in in_ct_lib_id; unfold in_lib_id; destruct ct.
  destruct in_ct_lib_id.
  - unfold in_app_id in H. unfold empty_map in H. destruct H. reflexivity.
  - unfold in_lib_id in H. apply H.
Qed.

Lemma valid_obj_Valid_Obj : forall ct (pfc : valid_class ct Obj), exists h1 h2 h3,
    pfc = ValidObj ct h1 h2 h3.
Proof.
  intros ct pfc. dependent destruction pfc.
  - exists i, n, e. reflexivity.
  - inversion e.
Qed.

Lemma lookup_self :
  forall ct c (pfc : valid_class ct c),
    lookup ct (id_of c) = Some c.
Proof. intros. inversion pfc; trivial. Qed.

Lemma ext_in_lib_ext_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (c d : class) (pfd : valid_class ct d),
    extends (ct_lib ct) c d -> extends ct c d.
Proof.
  intros ct pft c d pfd ext_in_lib.
  destruct c.
  - inversion ext_in_lib.
  - simpl. simpl in ext_in_lib.
    assert (id_of d = c0).
    { apply valid_table_valid_lib in pft. inversion pft. apply H0. trivial. }
    rewrite <- H. apply lookup_self. trivial.
Qed.

Lemma ext_in_lib_ext_in_ct_id :
  forall (ct : class_table) (pft : valid_table ct) (ci di : class_id),
    in_table_id ct ci -> extends_id (ct_lib ct) ci di -> extends_id ct ci di.
Proof.
  intros ct pft ci di ci_in_ct ext_in_lib.
  
Admitted.

Lemma valid_in_lib_in_lib : forall ct c (pfc : valid_class (ct_lib ct) c),
    in_lib ct c.
Proof.
  intros ct c pfc.
  destruct ct as [app lib]. simpl.
  apply valid_in_table in pfc. unfold in_table in pfc. destruct pfc.
  - simpl in H. unfold empty_map in H. destruct H. trivial.
  - simpl in H. trivial.
Qed.

Lemma decl_in_lib_in_lib : forall ct c (pfc : valid_class (ct_lib ct) c) f di,
    declaring_class (ct_lib ct) c pfc f = Some di -> in_lib_id ct di.
Proof.
  intros ct c pfc f di decl_in_lib.
  remember pfc as pfc'.
  induction pfc'.
  - simpl in decl_in_lib. inversion decl_in_lib.
  - simpl in decl_in_lib. destruct (existsb (fun f' : id => beq_id f' f) (dfields c)).
    + inversion decl_in_lib. destruct ct as [app lib]. simpl. clear Heqpfc'.
      apply valid_in_lib_in_lib in pfc. simpl in pfc. trivial.
    + apply IHpfc' with pfc'. trivial. trivial.
Qed.

Lemma supertype_valid : forall (ct : class_table) (c d : class) (pfc : valid_class ct c),
    subtype ct c d -> valid_class ct d.
Proof.
  intros ct c d pfc subtyp. induction subtyp.
  - eauto. 
  - eauto. 
  - inversion pfc.
    + rewrite <- H2 in e. unfold extends in e. inversion e.
    + assert (d = d0).
      { apply extends_injective with (c := c) (ct := ct). eauto. eauto. eauto. }
      rewrite H5; eauto.
Qed.

Lemma supertype_lib_in_lib : forall (ct : class_table) (c d : class) (pfc : valid_class ct c), 
    subtype ct c d -> in_lib ct c -> in_lib ct d.
Proof.
  intros ct c d pfc subtyp c_in_lib. induction subtyp.
  - apply c_in_lib.
  - apply IHsubtyp2.
    apply supertype_valid with (c := c). eauto. eauto.
    apply IHsubtyp1. eauto. eauto.
  - inversion pfc.
    + rewrite <- H2 in e. unfold extends in e. inversion e.
    + assert (d = d0).
      { apply extends_injective with (c:= c) (ct := ct). eauto. eauto. eauto. }
      destruct H2.
      * destruct H2. rewrite H5. eauto.
      * destruct H2. destruct H1. split. apply c_in_lib. apply H6.
Qed.

Lemma lib_par_same : forall ct (pft : valid_table ct) c d pfc_l pfd_l ext nla sca lk pfc,
    pfc_l = ValidParent (ct_lib ct) c d pfd_l ext nla sca lk ->
    exists ext' nla' sca' lk' pfd, pfc = ValidParent ct c d pfd ext' nla' sca' lk'.
Proof.
  intros. remember pfc as pfc'. destruct pfc.
  - inversion ext.
  - assert (d = d0) as deq.
    { apply extends_injective with ct c; trivial.
      - inversion pft. apply ext_in_lib_ext_in_ct; trivial.
         apply H0. apply in_lib_in_table. apply valid_in_lib_in_lib. trivial. }
    rewrite deq.
    exists e, n, o, e0, pfc. trivial.
Qed.

Lemma simul_induct_lib :
  forall (ct : class_table) (pft : valid_table ct) (P : forall ct c, valid_class (ct_lib ct) c -> valid_class ct c -> Prop),
    (forall o1 o2 o3 o1' o2' o3', P ct Obj (ValidObj (ct_lib ct) o1 o2 o3) (ValidObj ct o1' o2' o3')) ->
    (forall c d pfd_l pfd ext nla sca lk ext' nla' sca' lk',
        P ct d pfd_l pfd ->
        P ct c (ValidParent (ct_lib ct) c d pfd_l ext nla sca lk) (ValidParent ct c d pfd ext' nla' sca' lk')) ->
    forall c pfc_l pfc, P ct c pfc_l pfc.
Proof. 
  intros ct pft P Hobj Hind c pfc_l. 
  remember pfc_l as pfc_lr. induction pfc_l.
  - intros. assert (exists h1 h2 h3, pfc = ValidObj ct h1 h2 h3). apply valid_obj_Valid_Obj.
    destruct H as [x [y [z id]]]. rewrite id. rewrite Heqpfc_lr. apply Hobj.
  - intros. assert (exists ext' nla' sca' lk' pfd, pfc = ValidParent ct c d pfd ext' nla' sca' lk').
    { apply lib_par_same with pfc_lr pfc_l e n o e0; trivial. }
    destruct H as [ext' [nla' [sca' [lk' [pfd H']]]]].
    rewrite H'. rewrite Heqpfc_lr. apply Hind. apply IHpfc_l. trivial.
Qed.
Lemma rel_par_same : forall ct ct' (rel : ave_rel ct ct') c d pfc pfd ext nla sca lk pfc',
    pfc = ValidParent ct c d pfd ext nla sca lk ->
    exists ext' nla' sca' lk' pfd', pfc' = ValidParent ct' c d pfd' ext' nla' sca' lk'.
Proof.
  intros. remember pfc' as pfc''. inversion rel as [val_ct val_ct' keep_app keep_ext keep_lib]. destruct pfc'.
  - inversion ext.
  - assert (d = d0) as deq.
    { apply extends_injective with ct' c.
      - trivial.
      - apply keep_ext.
        + trivial.
        + destruct o.
          * apply a.
          * apply in_app_in_table. apply a.
      - trivial. }
    rewrite deq.
    exists e, n, o, e0, pfc'. trivial.
Qed.

Lemma simul_induct :
  forall (ct ct' : class_table) (rel : ave_rel ct ct') 
    (P : forall ct ct' rel c, valid_class ct c -> valid_class ct' c -> Prop),
    (forall o1 o2 o3 o1' o2' o3', P ct ct' rel Obj (ValidObj ct o1 o2 o3) (ValidObj ct' o1' o2' o3')) ->
    (forall c d pfd pfd' ext nla sca lk ext' nla' sca' lk', P ct ct' rel d pfd pfd' ->
        P ct ct' rel c (ValidParent ct c d pfd ext nla sca lk) (ValidParent ct' c d pfd' ext' nla' sca' lk')) ->
    forall c pfc pfc', P ct ct' rel c pfc pfc'.
Proof. 
  intros ct ct' rel P Hobj Hind c pfc. inversion rel as [val_ct val_ct' keep_app keep_ext keep_lib].
  remember pfc as pfc_r. induction pfc.
  - intros. assert (exists h1 h2 h3, pfc' = ValidObj ct' h1 h2 h3). apply valid_obj_Valid_Obj.
    destruct H as [x [y [z id]]]. rewrite id. rewrite Heqpfc_r. apply Hobj.
  - intros. assert (exists ext' nla' sca' lk' pfd, pfc' = ValidParent ct' c d pfd ext' nla' sca' lk').
    { apply rel_par_same with ct pfc_r pfc e n o e0.
      - trivial.
      - trivial. }
    destruct H as [ext' [nla' [sca' [lk' [pfd' H']]]]].
    rewrite H'. rewrite Heqpfc_r. apply Hind. apply IHpfc. trivial.
Qed.

Lemma pft_left : forall ct, valid_table ct -> (forall c, in_table ct c -> valid_class ct c).
Proof. intros ct H. admit. Admitted.
                         
Lemma val_in_lib_val_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (c : class) (pfc : valid_class (ct_lib ct) c),
    valid_class ct c.
Proof.
  intros ct pft c pfc.
  apply pft_left; trivial. apply in_lib_in_table. apply valid_in_lib_in_lib. trivial.
Qed.

Lemma fields_in_lib_fields_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (c : class) (pfc_l : valid_class (ct_lib ct) c) (pfc : valid_class ct c),
    fields (ct_lib ct) c pfc_l = fields ct c pfc.
Proof.
  intros ct pft c pfc_l pfc.
  apply simul_induct_lib with (ct := ct) (c := c) (pfc_l := pfc_l) (pfc := pfc); trivial.
  intros. simpl. destruct c0; trivial.
  rewrite H. trivial.
Qed.

Lemma mtype_in_lib_mtype_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (c : class) (pfc_l : valid_class (ct_lib ct) c) (pfc : valid_class ct c) mi,
    mtype (ct_lib ct) mi c pfc_l = mtype ct mi c pfc.
Proof.
  intros ct pft c pfc_l pfc mi.
  apply simul_induct_lib with (ct := ct) (c := c) (pfc_l := pfc_l) (pfc := pfc); trivial.
  intros. simpl. destruct (lookup_method c0 mi); trivial.
Qed.

Lemma subtyp_id_lib_sybtyp_id_ct : forall (ct : class_table) (ci : class_id) (di : class_id),
    valid_table ct -> subtype_id (ct_lib ct) ci di -> subtype_id ct ci di.
Proof.
  intros ct ci di pft subtyp_id_lib.
  induction subtyp_id_lib.
  - apply SI_Ref. apply in_lib_in_table_id. apply in_ct_lib_in_lib_id. trivial.
  - apply SI_Sub. apply ext_in_lib_ext_in_ct_id; trivial.
  - apply SI_Trans with di; trivial.
Qed.

Lemma typ_in_lib_typ_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (gamma : context) (e : expr) (ci : class_id),
    type_of (ct_lib ct) gamma e ci -> type_of ct gamma e ci.
Proof.
  intros ct pft gamma e ci typ_in_lib.
  induction typ_in_lib using type_of_ind_list.
  - apply T_Var.
  - apply val_in_lib_val_in_ct in pfc as pfc'; trivial.
    apply T_Field with c pfc'; trivial.
    unfold lookup_field. unfold lookup_field in H.
    assert (fields (ct_lib ct) c pfc = fields ct c pfc'). { apply fields_in_lib_fields_in_ct; trivial. }
    rewrite <- H0. trivial.
  - apply val_in_lib_val_in_ct in pfc0 as pfc0'; trivial.
    apply T_Invk with c0 pfc0' ld ret lc; trivial.
    * assert (mtype (ct_lib ct) mi c0 pfc0 = mtype ct mi c0 pfc0').
      { apply mtype_in_lib_mtype_in_ct; trivial. }
      rewrite <- H6. trivial.
    * apply Forall_impl with (P := (fun p : class_id * class_id => subtype_id (ct_lib ct) (fst p) (snd p))); trivial.
      intros a H6. apply subtyp_id_lib_sybtyp_id_ct; trivial.
  - apply val_in_lib_val_in_ct in pfc as pfc'; trivial.
    apply T_New with c pfc' lc ld; trivial.
    + rewrite <- fields_in_lib_fields_in_ct with (pfc_l := pfc); trivial.
    + apply Forall_impl with (P := (fun p : class_id * class_id => subtype_id (ct_lib ct) (fst p) (snd p))); trivial.
      intros. apply subtyp_id_lib_sybtyp_id_ct; trivial.
  - apply T_Cast with di; trivial.
Qed.

Lemma decl_in_lib_decl_in_ct :
  forall (ct : class_table) (pft : valid_table ct) (c : class) (pfc : valid_class ct c) (pfc_l : valid_class (ct_lib ct) c) f d,
    declaring_class (ct_lib ct) c pfc_l f = Some d -> declaring_class ct c pfc f = Some d.
  intros ct pft c pfc pfc_l.
  apply simul_induct_lib with (ct := ct) (c := c) (pfc_l := pfc_l) (pfc := pfc); trivial.
  - clear c pfc pfc_l. intros c d pfd_l pfd ext nla sca lk ext' nla' sca' lk' IHd f e decl_l.
    simpl in decl_l. simpl. destruct (existsb (fun f' : id => beq_id f' f) (dfields c)); trivial.
    apply IHd. trivial.
Qed.

Lemma invk_valid_in_lib_m_in_lib : forall (ct : class_table) e le m (gamma : context),
    valid_expr (ct_lib ct) gamma (E_Invk e m le) -> exists c, in_lib ct c /\ In m (dmethods c).
Proof.
  intros ct e le m gamma val_e.
  inversion val_e. clear H6. remember pfc as pfc'. induction pfc.
  - rewrite Heqpfc' in H7. simpl in H7. destruct H7. trivial.
  - simpl in H7. destruct (existsb (fun m' : id => beq_id m m') (dmethods c)) eqn:exstb. 
    + exists c. split.
      * apply in_ct_lib_in_lib. apply valid_in_table. trivial.
      * rewrite existsb_exists in exstb. destruct exstb as [m' [Inm' Heqm]].
        rewrite beq_id_true_iff in Heqm. rewrite Heqm. trivial.
    + apply IHpfc with pfc; trivial.
      rewrite Heqpfc' in H7. simpl in H7. rewrite exstb in H7. trivial.
Qed.

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

Lemma lemma2 : forall ct ct' (pft : ave_rel ct ct') c pfc pfc' e e' m,
      in_app ct c -> mresolve ct m c pfc = Some e -> mresolve ct' m c pfc' = Some e' ->
      (in_app ct e \/ in_lib ct' e').
Proof.
  intros ct ct' pft c pfc pfc'. 
  apply simul_induct with (ct := ct) (ct' := ct') (c := c) (pfc := pfc) (pfc' := pfc'); trivial.
  (* c is Obj *)
  - contradiction.
  (* c extends d *)
  - clear c pfc pfc'. intros c d pfd pfd' ext nla sca lk ext' nla' sca' lk' IHd e e' m c_in_app mres_e mres_e'.
    inversion pft as [ct_val ct'_val keep_app keep_ext keep_lib].
    simpl in mres_e. destruct (existsb (fun m' : id => beq_id m m') (dmethods c)) eqn:exst.
    (* m-res *)
    + left. inversion mres_e. rewrite <- H0. trivial.
    (* m-res-inh *)
    + simpl in mres_e'. rewrite exst in mres_e'. 
      destruct sca as [[d_in_lib _] | [d_in_app _]].
      (* d in lib - use averroes transformation properties *)
      * right. apply mres_lib_in_lib with m d pfd'; trivial.
        apply keep_lib with c; trivial. apply in_app_in_table; apply keep_app; trivial.
      (* d in app - use induction hypothesis *)
      * apply IHd with m; trivial. 
Qed.

Lemma lemma3 : forall (ct ct' : class_table) (pft : ave_rel ct ct')
                 (sig sig' : subst) (gamma : context) (e0 : expr),
    (forall v, alpha ct ct' pft gamma (EL_Expr (sig v), EL_Expr (sig' v))) -> type_checks ct' gamma e0 ->
    alpha ct ct' pft gamma (EL_Expr (do_sub sig e0), EL_Expr (do_sub sig' e0)).
Proof.
  intros ct ct' pft sig sig' gamma e0 rel typ_chk. induction e0 using expr_ind_list.
  (* Case Var *)
  - eauto.
  (* Case Field *)
  - simpl; apply Rel_Field. inversion typ_chk; eauto. 
  (* Case Invk *)
  - simpl; apply Rel_Invk.
    + inversion typ_chk; eauto. 
    + rewrite map_length, map_length; reflexivity.
    + inversion typ_chk. clear H2; clear H3; clear typ_chk; induction l.
      * apply Forall_nil. 
      * inversion H; inversion H6. apply Forall_cons; eauto; eauto.
  (* Case New *)
  - simpl. inversion typ_chk. apply Rel_New.
    + eauto.
    + rewrite map_length, map_length; reflexivity.
    + clear typ_chk; clear H1; induction l.
      * apply Forall_nil.
      * inversion H; inversion H3. apply Forall_cons; eauto; eauto.
  (* Case Cast *)
  - apply Rel_Cast; inversion typ_chk; eauto.
Qed.

Lemma lemma4 : forall (ct ct' : class_table) (pft : ave_rel ct ct')
                 (sig : subst) (gamma : context) (e0 : expr),
    (forall v, alpha ct ct' pft gamma (EL_Expr (sig v), EL_Lib)) -> valid_expr (ct_lib ct) gamma e0 ->
    alpha ct ct' pft gamma (EL_Expr (do_sub sig e0), EL_Lib).
Proof.
  intros ct ct' pft sig gamma e0 rel val_e_lib. induction e0 using expr_ind_list.
  (* Case Var *)
  - eauto.
  (* Case Field *)
  - simpl. inversion val_e_lib as [|x y di0 d0 pfd0 typ_chk_ef0 e_typ_d0 di_d0 f_def val_e0_lib | | |];
    clear x y H H0.
    inversion typ_chk_ef0 as [| x y di e_typ_d z typ_chk_e0 | | | ]; clear x y z H H0.
    remember (declaring_class (ct_lib ct) d0 pfd0 f0) as f_decl in f_def. destruct f_decl. 
    + inversion pft. assert (valid_class ct d0) as pfd0'.
      { apply val_in_lib_val_in_ct. trivial. trivial. }
      apply Rel_Lib_Field with (ci := c) (c := d0) (pfc := pfd0').
      * apply IHe0. inversion val_e_lib. trivial.
      * apply decl_in_lib_decl_in_ct with pfd0; trivial. eauto.
      * apply decl_in_lib_in_lib with d0 pfd0 f0. eauto.
      * apply typ_in_lib_typ_in_ct. trivial. apply sub_keep_typ. rewrite di_d0. trivial.
    + destruct f_def. reflexivity.
  (* Case Invk *)
  - simpl. inversion val_e_lib.
    apply Rel_Lib_Invk.
    + apply invk_valid_in_lib_m_in_lib with e0 l gamma. trivial.
    + apply IHe0. trivial.
    (* clean up using Forall principles? *) 
    + clear H3 H2 val_e_lib. induction l.
      * simpl. apply Forall_nil.
      * simpl. apply Forall_cons.
        -- inversion H. apply H9. inversion H5. trivial.
        -- apply IHl.
           ++ inversion H. trivial.
           ++ inversion H5. trivial.
  (* Case New *)
  - simpl. inversion val_e_lib.
    apply Rel_Lib_New.
    + apply in_ct_lib_in_lib_id. inversion H2. trivial.
    + clear H2 H1 val_e_lib. induction l.
      * simpl. apply Forall_nil.
      * simpl. apply Forall_cons.
        -- inversion H. apply H4. inversion H3. trivial. 
        -- apply IHl.
           ++ inversion H. trivial.
           ++ inversion H3. trivial.
  (* Case Cast *)
  - simpl. inversion val_e_lib.
    apply Rel_Lib_Cast. apply IHe0. apply H2.
Qed.