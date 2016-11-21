Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Arith.EqNat.
Require Import Program.Equality.

Module E.
  Require Coq.Sets.Ensembles.
  Include Ensembles.
End E.

Section generic_defs.
  Definition set := E.Ensemble.
  Definition empty_set {A : Type} := E.Empty_set A.
  Definition set_In {A : Type} (a : A) (s : set A) := E.In A s a.
  Definition add {A : Type} (a : A) (s : set A) := E.Add A s a.
  Definition union {A : Type} := E.Union A.
  Definition union_introl {A : Type} := E.Union_introl A.
  Definition union_intror {A : Type} := E.Union_intror A.
  Definition subset {A : Type} := E.Included A.
  Fixpoint set_from_list {A : Type} (l : list A) :=
    match l with
    | nil => empty_set
    | h :: l' => add h (set_from_list l')
    end.
  Fixpoint index_of {A : Type} (f : A -> bool) (l : list A) : option nat :=
    match l with
    | nil => None
    | a :: l' => if f a then Some 0 else option_map S (index_of f l')
    end.
  Fixpoint first_n {A : Type} (l : list A) (n : nat) :=
    match n, l with
    | S n', h :: l' => h :: (first_n l' n')
    | _, _ => nil
    end.
  Fixpoint remove_last {A : Type} (l : list A) :=
    match l with
    | nil => nil
    | _ :: nil => nil
    | h :: l' => h :: (remove_last l')
    end.

  Fixpoint last_error {A : Type} (l : list A) :=
    match l with
    | nil => None
    | h :: nil => Some h
    | _ :: l' => last_error l'
    end.

  Fixpoint zip_with_ind_h {A : Type} (l : list A) (n : nat) :=
    match l with
    | nil => nil
    | h :: l' => (n, h) :: zip_with_ind_h l' (S n)
    end.
  Definition zip_with_ind {A : Type} (l : list A) := zip_with_ind_h l 0.

End generic_defs.

Notation "a 'U' b" := (union a b) (at level 65, right associativity).
Section generic_thms.
  Theorem Forall_list_impl : forall (A : Type) (P Q : A -> Prop) (l : list A),
    Forall P l -> Forall (fun a => P a -> Q a) l -> Forall Q l.
  Proof.
    intros A P Q l fp fimp. induction l. apply Forall_nil.
    inversion fp. inversion fimp.
    apply Forall_cons.
    - apply H5; trivial.
    - apply IHl; trivial.
  Qed.

  Theorem Forall_map_swap : forall (A : Type) (P : A -> Prop) (f : A -> A) (l : list A),
      Forall P (map f l) <-> Forall (fun a => P (f a)) l.
  Proof.
    intros A P f l.
    induction l.
    - simpl. split; intros; apply Forall_nil.
    - simpl. split; intros; inversion H; apply Forall_cons; trivial; apply IHl; trivial.
  Qed.

  Theorem Forall_In : forall (A : Type) (P : A -> Prop) (l : list A) (a : A),
      Forall P l -> In a l -> P a.
  Proof.
    induction l.
    - intros. inversion H0.
    - intros. destruct H0; inversion H; eauto.
      rewrite <- H0. eauto.
  Qed.

  Theorem find_pair_in_zip : forall (A B : Type) (f : A -> bool) (la : list A) (lb lb' : list B) p p',
      find (fun p => f (fst p)) (combine la lb) = Some p ->
      find (fun p => f (fst p)) (combine la lb') = Some p' ->
      In (snd p, snd p') (combine lb lb').
  Proof.
    induction la.
    - intros. inversion H.
    - intros. destruct lb; destruct lb'.
      + inversion H.
      + inversion H.
      + inversion H0.
      + simpl in H. simpl in H0. destruct (f a).
        * inversion H. inversion H0. simpl. left. reflexivity.
        * simpl. right; eauto.
  Qed.

  Theorem extract_combine : forall {A B : Type} (f : A -> bool) (la : list A) (lb : list B),
      length la = length lb -> find (fun p => f (fst p)) (combine la lb) = None -> find f la = None.
  Proof.
    induction la.
    - reflexivity.
    - intros. destruct lb.
      + inversion H.
      + simpl in H0. simpl. destruct (f a).
        * inversion H0.
        * apply IHla with lb; eauto.
  Qed.

  Theorem zip_In_l : forall {A B : Type} (la : list A) (lb : list B) a b,
      In (a, b) (combine la lb) -> In a la.
  Proof.
    induction la; intros.
    - inversion H.
    - destruct lb.
      + inversion H.
      + simpl in H. simpl. destruct H.
        * inversion H. eauto.
        * right. apply IHla with lb b. eauto.
  Qed.

  Theorem zip_In_r : forall {A B : Type} (la : list A) (lb : list B) a b,
      In (a, b) (combine la lb) -> In b lb.
  Proof.
    intros A B la lb. generalize dependent la. induction lb; intros.
    - destruct la; inversion H.
    - destruct la.
      + inversion H.
      + simpl in H. simpl. destruct H.
        * inversion H. eauto.
        * right. apply IHlb with la a0. eauto.
  Qed.

  Theorem get_nth : forall {A : Type} (l : list A) (m n : nat),
      length l = n -> m < n -> exists a, nth_error l m = Some a.
  Proof.
    induction l; intros; simpl in H.
    - rewrite <- H in H0. inversion H0.
    - destruct n; inversion H.
      destruct m.
      + exists a. reflexivity.
      + simpl. apply IHl with n; trivial.
        apply Lt.lt_S_n. trivial.
  Qed.

  Lemma union_comm : forall {A : Type} (s1 s2 : set A),
      s1 U s2 = s2 U s1.
  Proof.
    intros. apply E.Extensionality_Ensembles.
    unfold E.Same_set. unfold E.Included.
    split; unfold union; intros; inversion H;
      solve [apply union_introl; trivial | apply union_intror; trivial].
  Qed.

  Lemma union_addl : forall A (s1 s2 : set A) (a : A),
      add a s1 U s2 = add a (s1 U s2).
    intros. apply E.Extensionality_Ensembles.
    unfold E.Same_set. unfold E.Included. unfold union. unfold add. 
    split; intros; inversion H; try (inversion H0);
      solve [apply union_intror; trivial
            | apply union_introl; solve [apply union_introl; trivial
                                        | apply union_intror; solve [trivial | reflexivity]]].
  Qed.

  Lemma union_addr : forall A (s1 s2 : set A) (a : A),
      s1 U add a s2 = add a (s1 U s2).
    intros. apply E.Extensionality_Ensembles.
    unfold E.Same_set. unfold E.Included. unfold union. unfold add.
    split; intros; inversion H; try (inversion H0);
      solve [ apply union_introl; solve [ apply union_introl; reflexivity || trivial
                                        | apply union_intror; reflexivity || trivial
                                        | reflexivity || trivial]
            | apply union_intror; solve [ apply union_introl; reflexivity || trivial
                                        | apply union_intror; reflexivity || trivial
                                        | reflexivity || trivial]].
  Qed.

  Lemma union_assoc : forall {A: Type} (s1 s2 s3 : set A),
      (s1 U s2) U s3 = s1 U s2 U s3.
  Proof.
    intros. apply E.Extensionality_Ensembles. unfold E.Same_set. unfold E.Included. unfold union.
    split; intros; inversion H; try (inversion H0);
      solve [ apply union_introl; solve [ apply union_introl; reflexivity || trivial
                                        | apply union_intror; reflexivity || trivial
                                        | reflexivity || trivial]
            | apply union_intror; solve [ apply union_introl; reflexivity || trivial
                                        | apply union_intror; reflexivity || trivial
                                        | reflexivity || trivial]].
  Qed.

  Lemma union_same : forall {A : Type} (s : set A),
      s U s = s.
  Proof.
    intros. apply E.Extensionality_Ensembles. unfold E.Same_set. unfold E.Included. unfold union.
    split; intros; try (inversion H); trivial. apply union_introl. apply H.
  Qed.

  Lemma union_include : forall {A : Type} (s1 s2 : set A),
      subset s1 s2 -> s2 = s2 U s1.
  Proof.
    intros. apply E.Extensionality_Ensembles.
    unfold E.Same_set. unfold subset in H. unfold E.Included. unfold E.Included in H.
    split; intros.
    - apply union_introl. apply H0.
    - destruct H0.
      + apply H0.
      + apply H. apply H0.
  Qed.

  Lemma In_list_set_In_list : forall {A : Type} (l : list A) (a : A),
      In a l -> set_In a (set_from_list l).
  Proof.
    induction l; intros; inversion H.
    - subst a0. simpl. apply union_intror. apply E.In_singleton.
    - simpl. apply union_introl. apply IHl. apply H0.
  Qed.

  Lemma nth_error_first_n : forall {A : Type} (l : list A) (a : A) (n : nat),
      nth_error l n = Some a -> nth_error (first_n l (S n)) n = Some a.
  Proof.
    induction l; intros; destruct n; inversion H.
    - subst a0. reflexivity.
    - simpl. rewrite H1. apply IHl. apply H1.
  Qed.

  Lemma remove_last_length : forall {A : Type} (l : list A) (n : nat),
      length l = S n -> length (remove_last l) = n.
  Proof.
    induction l; intros; inversion H.
    destruct l; try reflexivity.
    simpl. simpl in IHl. rewrite IHl with (length l); reflexivity.
  Qed.

  Lemma remove_last_first_n : forall {A : Type} (l : list A) (n : nat),
      n < length l -> first_n l n = first_n (remove_last l) n.
  Proof.
    induction l; intros.
    - inversion H.
    - destruct l.
      + simpl in H. inversion H. reflexivity. inversion H1.
      + destruct n; try reflexivity.
        simpl. f_equal. unfold first_n in IHl. fold (@first_n A) in IHl.
        unfold remove_last in IHl. fold (@remove_last A) in IHl.
        apply IHl. apply Lt.lt_S_n. apply H.
  Qed.

  Lemma remove_last_nth_error : forall {A : Type} (l : list A) (n : nat),
      S n < length l -> nth_error l n = nth_error (remove_last l) n.
  Proof.
    induction l; intros.
    - inversion H.
    - destruct n.
      + destruct l.
        * inversion H. inversion H1.
        * reflexivity.
      + destruct l.
        * inversion H. inversion H1.
        * simpl. simpl in IHl. apply IHl. apply Lt.lt_S_n. apply H.
  Qed.

  Lemma first_n_length : forall {A : Type} (l : list A),
      first_n l (length l) = l.
  Proof.
    induction l; try reflexivity.
    simpl. rewrite IHl. reflexivity.
  Qed.
  Lemma last_error_In : forall {A : Type} (l : list A) (a : A),
      last_error l = Some a -> In a l.
  Proof.
    induction l.
    - intros. inversion H.
    - destruct l.
      + intros. inversion H. left. reflexivity.
      + intros. right. apply IHl. apply H.
  Qed.

  Lemma zip_with_ind_h_length : forall {A : Type} (l : list A) (n : nat),
      length (zip_with_ind_h l n) = length l.
  Proof.
    induction l.
    - reflexivity.
    - intros. simpl. f_equal. apply IHl.
  Qed.

  Lemma zip_with_ind_length : forall {A : Type} (l : list A),
      length (zip_with_ind l) = length l.
  Proof. intros. apply zip_with_ind_h_length. Qed.

  Lemma last_repeat : forall {A : Type} (a : A) (n : nat),
      last_error (repeat a (S n)) = Some a.
  Proof.
    induction n.
    - reflexivity.
    - simpl. apply IHn.
  Qed.

  Lemma last_error_map : forall {A B : Type} (f : A -> B) (l : list A) (a : A),
      last_error l = Some a -> last_error (map f l) = Some (f a).
  Proof.
    induction l.
    - intros. inversion H.
    - intros. destruct l.
      + inversion H. subst a0. reflexivity.
      + simpl. apply IHl. apply H.
  Qed.

  Lemma last_error_zip_with_ind_h : forall {A : Type} (l : list A) (n : nat) (m : nat) (a : A),
      length l = S m -> last_error l = Some a ->
      last_error (zip_with_ind_h l n) = Some (m + n, a).
  Proof.
    induction l.
    - intros. inversion H.
    - intros. destruct l.
      + inversion H0. subst a0. inversion H. reflexivity.
      + destruct m. inversion H. simpl. rewrite plus_n_Sm. apply IHl.
        * simpl. f_equal. inversion H. reflexivity.
        * apply H0.
  Qed.

  Lemma last_error_zip_with_ind : forall {A : Type} (l : list A) (n : nat) (a : A),
      length l = S n -> last_error l = Some a ->
      last_error (zip_with_ind l) = Some (n, a).
  Proof.
    intros. unfold zip_with_ind. rewrite (plus_n_O n). apply last_error_zip_with_ind_h; trivial.
  Qed.

  Lemma nth_error_map : forall {A B : Type} (l : list A) (f : A -> B) (a : A) (n : nat),
      nth_error l n = Some a -> nth_error (map f l) n = Some (f a).
  Proof.
    induction l; intros; destruct n; inversion H.
    - subst a0. reflexivity.
    - rewrite <- IHl with (n := n); try reflexivity. apply H.
  Qed.

  Lemma nth_error_zip_with_ind_h : forall {A : Type} (l : list A) (n : nat) (m : nat) (a : A),
      nth_error l m = Some a -> nth_error (zip_with_ind_h l n) m = Some (n + m, a).
  Proof.
    induction l; intros; destruct m; inversion H.
    - subst a0. rewrite PeanoNat.Nat.add_comm. reflexivity.
    - simpl. rewrite <- plus_n_Sm. replace (S (n + m)) with (S n + m) by reflexivity.
      apply IHl. trivial.
  Qed.

  Lemma nth_error_zip_with_ind : forall {A : Type} (l : list A) (m : nat) (a : A),
      nth_error l m = Some a -> nth_error (zip_with_ind l) m = Some (m, a).
  Proof.
    intros. apply nth_error_zip_with_ind_h. trivial.
  Qed.

  Lemma nth_error_better_Some : forall {A : Type} (l : list A) (n : nat),
      n < length l -> exists a, nth_error l n = Some a.
  Proof.
    intros. assert (nth_error l n <> None) by (apply nth_error_Some; trivial).
    destruct (nth_error l n) eqn:ntherr.
    - exists a. reflexivity.
    - destruct H0; reflexivity.
  Qed.

End generic_thms.
Section defs.
  Definition field_id := nat.
  Definition var_id := nat.
  Definition method_id := nat.

  Inductive var : Type :=
  | Var : var_id -> var
  | This : var.

  Inductive class : Type :=
  | Obj : class
  | C : class ->
        list (class * field_id) ->
        list (class * var_id) ->
        list method -> class
  with expr : Type :=
       | E_Var : var -> expr
       | E_Field : expr -> field_id -> expr
       | E_New : class -> list expr -> expr
       | E_Invk : expr -> method_id -> list expr -> expr
       | E_Cast : class -> expr -> expr
       | E_Lib : expr
  with method : Type :=
       | Method : class -> method_id -> list (class * var_id) -> expr -> method.
  Definition exprlpt : Type := expr * set expr.

End defs.
Section table_defs.
  Definition empty_map : class -> Prop := fun c => False.
  Definition class_table : Type := (class -> Prop) * (class -> Prop).
  Definition in_app (ct : class_table) c :=
    match ct with (app, _) => app c end.
  Definition in_lib (ct : class_table) c :=
    match ct with (_, lib) => lib c end.
  Definition in_table ct c := in_app ct c \/ in_lib ct c.
  Definition ct_lib (ct : class_table) : class_table :=
    match ct with (app, lib) => (empty_map, lib) end.

  Inductive expr_In : var -> expr -> Prop :=
  | EIn_Var : forall v, expr_In v (E_Var v)
  | EIn_Field : forall v e f, expr_In v e -> expr_In v (E_Field e f)
  | EIn_New : forall v le c, Exists (expr_In v) le ->  expr_In v (E_New c le)
  | EIn_Invk : forall v e m le, Exists (expr_In v) le \/ expr_In v e -> expr_In v (E_Invk e m le)
  | EIn_Cast : forall v e c, expr_In v e -> expr_In v (E_Cast c e).

  Definition valid_method (m : method) : Prop :=
    match m with
    | Method _ _ lcv e =>
      forall v, expr_In v e -> v = This \/ In v (map Var (map snd lcv))
    end.

  Inductive valid_class (ct : class_table) : class -> Prop :=
  | V_Obj : ~ in_app ct Obj -> in_lib ct Obj -> valid_class ct Obj
  | V_Class : forall d l l' lm,
      valid_class ct d ->
      ~ (in_lib ct (C d l l' lm) /\ in_app ct (C d l l' lm)) ->
      ((in_app ct d /\ in_app ct (C d l l' lm)) \/ (in_table ct (C d l l' lm) /\ in_lib ct d)) ->
      Forall valid_method lm ->
      valid_class ct (C d l l' lm).
  Definition valid_table ct : Prop :=
    forall c, in_table ct c -> valid_class ct c.
End table_defs.
Section auxiliary_defs.
  Definition beq_var (v v' : var) : bool :=
    match v, v' with
    | This, This => true
    | Var vi, Var vi' => beq_nat vi vi'
    | _, _ => false
    end.

  Theorem beq_var_refl : forall v, true = beq_var v v.
  Proof. intros. destruct v; eauto. simpl. apply beq_nat_refl. Qed.
  Theorem beq_var_true : forall v v', v = v' <-> true = beq_var v v'.
  Proof.
    intros. split; intro; destruct v; destruct v'; inversion H; eauto.
    - apply beq_var_refl.
    - symmetry in H1. apply beq_nat_true in H1. eauto.
  Qed.

  Definition subst := list (var * expr).
  Fixpoint do_sub (sig : subst) (e : expr) : expr :=
    match e with
    | E_Var v => match find (fun p => beq_var (fst p) v) sig with
                | Some (_, e') => e'
                | None => e
                end
    | E_Field e' f => E_Field (do_sub sig e') f
    | E_New c es => E_New c (map (do_sub sig) es)
    | E_Invk e' m es => E_Invk (do_sub sig e') m (map (do_sub sig) es)
    | E_Cast c e' => E_Cast c (do_sub sig e')
    | E_Lib => E_Lib
    end.

  Definition context := var -> class.

End auxiliary_defs.
Section auxiliary_functions.

  Definition mid (m : method) : method_id := match m with Method _ mi _ _ => mi end.
  Definition args (m : method) : list var :=
    match m with
    | Method _ _ l _ => map Var (map snd l)
    end.
  Definition body (m : method) : expr := match m with Method _ _ _ e => e end.
  Fixpoint fields (c : class) : list (class * field_id) :=
    match c with
    | Obj => nil
    | C d fs _ _ => fs ++ fields d
    end.

  Definition dfields (c : class) : list (class * field_id) :=
    match c with
    | Obj => nil
    | C d fs _ _ => fs
    end.

  Definition lookup_field (fi : field_id) (c : class) : option class :=
    option_map fst (find (fun p => match p with (_, fi') => beq_nat fi fi' end) (fields c)).

  Fixpoint declaring_class (fi : field_id) (c : class) : option class :=
    match c with
    | Obj => None
    | C d fs _ _ => if existsb (fun p => beq_nat fi (snd p)) fs
                   then Some c
                   else declaring_class fi d
    end.

  Definition dmethods (c : class) : list method :=
    match c with
    | Obj => nil
    | C _ _ _ ms => ms
    end.

  Definition dmethods_id (c : class) : list method_id :=
    match c with
    | Obj => nil
    | C _ _ _ ms => map (fun m => match m with Method _ mi _ _ => mi end) ms
    end.

  Definition lookup_method (mi : method_id) (c : class) : option method :=
    match c with
    | Obj => None
    | C _ _ _ ms => find (fun m => match m with Method _ mi' _ _ => beq_nat mi mi' end) ms
    end.

  Fixpoint find_method (mi : method_id) (c : class) : option method :=
    match c with
    | Obj => None
    | C d _ _ _ => match lookup_method mi c with
                  | Some m => Some m
                  | None => find_method mi d
                  end
    end.
  Fixpoint mtype (mi : method_id) (c : class) : option (list class * class) :=
    match find_method mi c with
    | Some (Method ret _ par _) => Some (map fst par, ret)
    | None => None
    end.

  Fixpoint mparams (mi : method_id) (c : class) : option (list var_id) :=
    match find_method mi c with
    | Some (Method ret _ par _) => Some (map snd par)
    | None => None
    end.

  Fixpoint mbody (mi : method_id) (c : class) : option (list var_id * expr) :=
    match find_method mi c with
    | Some (Method _ _ par bod) => Some (map snd par, bod)
    | None => None
    end.

  Fixpoint mresolve (m : method_id) (c : class) : option class :=
    match c with
    | Obj => None
    | C d _ _ _ =>
      if (existsb (fun m' => beq_nat m m') (dmethods_id c))
      then Some c
      else mresolve m d
    end.

  Definition extends (c d : class) : Prop :=
    match c with
    | Obj => False
    | C d' _ _ _ => d = d'
    end.

  (*Fixpoint subst_from_list (l : list (expr * var)) : subst :=
    match l with
    | nil => fun _ => None
    | (e, v) :: l' => fun v' => if beq_var v v' then Some e else subst_from_list l' v'
    end.*)

End auxiliary_functions.
Section auxiliary_lemmas.
  Lemma decl_of_lib_in_lib : forall ct c d f,
    valid_table ct -> in_lib ct c -> declaring_class f c = Some d -> in_lib ct d.
  Proof.
    intros ct c d f pft c_in_lib decl.
    induction c.
    - inversion decl.
    - simpl in decl. destruct (existsb (fun p : class * nat => PeanoNat.Nat.eqb f (snd p)) l).
      + inversion decl; trivial.
      + assert (valid_class ct (C c l l0 l1)).
        { apply pft. unfold in_table. right. trivial. }
        inversion H. destruct H6 as [[par_app ch_app] | [ch_tab par_lib]].
        * destruct H5. split; trivial.
        * apply IHc; trivial.
  Qed.

  Lemma mresolve_in_methods : forall c d m,
      mresolve m c = Some d -> In m (dmethods_id d).
  Proof.
    intros. induction c.
    - inversion H.
    - unfold mresolve in H.
      destruct (existsb (fun m' : nat => PeanoNat.Nat.eqb m m') (dmethods_id (C c l l0 l1))) eqn:exst; eauto.
      inversion H. rewrite existsb_exists in exst. destruct exst as [x [in_eqb]].
      apply beq_nat_true in H0. rewrite H0. trivial.
  Qed.

End auxiliary_lemmas.
Section props.
  Definition ave_rel (ct ct' : class_table) : Prop :=
    valid_table ct /\ valid_table ct' /\
    (forall c, in_app ct c <-> in_app ct' c) /\
    (forall c d, extends c d -> in_lib ct d -> in_table ct' c -> in_lib ct' d).

  Inductive subtype : class -> class -> Prop :=
  | S_Ref : forall c, subtype c c
  | S_Trans : forall c d e, subtype c d -> subtype d e -> subtype c e
  | S_Sub : forall c d, extends c d -> subtype c d.
  
  Inductive type_of (gamma : context) : expr -> class -> Prop :=
  | T_Var : forall x, type_of gamma (E_Var x) (gamma x)
  | T_Field : forall e c d f,
      type_of gamma e c -> lookup_field f c = Some d ->
      type_of gamma (E_Field e f) d
  | T_New : forall c le lc ld,
      map fst (fields c) = ld ->
      length ld = length le -> length le = length lc ->
      Forall (fun p => type_of gamma (fst p) (snd p)) (combine le lc) ->
      Forall (fun p => subtype (fst p) (snd p)) (combine lc ld) ->
      type_of gamma (E_New c le) c
  | T_Invk : forall e0 c0 ld ret mi le lc,
      type_of gamma e0 c0 -> mtype mi c0 = Some (ld, ret) ->
      length ld = length le -> length le = length lc ->
      Forall (fun p => type_of gamma (fst p) (snd p)) (combine le lc) ->
      Forall (fun p => subtype (fst p) (snd p)) (combine lc ld) ->
      type_of gamma (E_Invk e0 mi le) ret
  | T_Cast : forall e0 c d, type_of gamma e0 d -> type_of gamma (E_Cast c e0) c.

  Inductive alpha (ct ct' : class_table) (gamma : context) : expr -> expr -> set expr -> Prop :=
  | Rel_Field : forall e e' f lpt,
      alpha ct ct' gamma e e' lpt ->
      alpha ct ct' gamma (E_Field e f) (E_Field e' f) lpt
  | Rel_Lib_Field : forall e c d f lpt,
      alpha ct ct' gamma e E_Lib lpt ->
      declaring_class f c = Some d -> in_lib ct d ->
      type_of gamma e c ->
      alpha ct ct' gamma (E_Field e f) E_Lib lpt
  | Rel_New : forall c le le' lpt,
      in_table ct' c -> length le = length le' ->
      Forall (fun p => alpha ct ct' gamma (fst p) (snd p) lpt) (combine le le') ->
      alpha ct ct' gamma (E_New c le) (E_New c le') lpt
  | Rel_Lib_New : forall c le lpt,
      in_lib ct c -> Forall (fun e => alpha ct ct' gamma e E_Lib lpt) le ->
      alpha ct ct' gamma (E_New c le) E_Lib lpt
  | Rel_Invk : forall e e' le le' m lpt,
      alpha ct ct' gamma e e' lpt ->
      length le = length le' ->
      Forall (fun p => alpha ct ct' gamma (fst p) (snd p) lpt) (combine le le') ->
      alpha ct ct' gamma (E_Invk e m le) (E_Invk e' m le') lpt
  | Rel_Lib_Invk : forall e le mi lpt,
      (exists c, in_lib ct c /\ In mi (dmethods_id c)) ->
      alpha ct ct' gamma e E_Lib lpt ->
      Forall (fun e' => alpha ct ct' gamma e' E_Lib lpt) le ->
      alpha ct ct' gamma (E_Invk e mi le) E_Lib lpt
  | Rel_Cast : forall e e' c lpt,
      alpha ct ct' gamma e e' lpt ->
      alpha ct ct' gamma (E_Cast c e) (E_Cast c e') lpt
  | Rel_Lib_Cast : forall e ci lpt,
      alpha ct ct' gamma e E_Lib lpt -> alpha ct ct' gamma (E_Cast ci e) E_Lib lpt
  | Rel_Lpt : forall e e' lpt,
      alpha ct ct' gamma e e' lpt -> set_In e' lpt -> alpha ct ct' gamma e E_Lib lpt.

  Inductive type_checks (ct : class_table) (gamma : context) : expr -> Prop :=
  | TC_Var : forall x, in_table ct (gamma x) -> type_checks ct gamma (E_Var x)
  | TC_Field : forall e f d, type_of gamma (E_Field e f) d -> in_table ct d -> type_checks ct gamma e ->
                        type_checks ct gamma (E_Field e f)
  | TC_New : forall c le, in_table ct c -> Forall (type_checks ct gamma) le -> type_checks ct gamma (E_New c le)
  | TC_Invk : forall e m le d, type_of gamma (E_Invk e m le) d -> in_table ct d ->
                          type_checks ct gamma e -> Forall (type_checks ct gamma) le ->
                          type_checks ct gamma (E_Invk e m le)
  | TC_Cast : forall e d, in_table ct d -> type_checks ct gamma e -> type_checks ct gamma (E_Cast d e).

  Inductive fj_expr : expr -> Prop :=
  | FJ_Var : forall x, fj_expr (E_Var x)
  | FJ_Field : forall e f, fj_expr e -> fj_expr (E_Field e f)
  | FJ_New : forall c le, Forall fj_expr le -> fj_expr (E_New c le)
  | FJ_Invk : forall e m le, 
      fj_expr e -> Forall fj_expr le ->
      fj_expr (E_Invk e m le)
  | FJ_Cast : forall e d, fj_expr e -> fj_expr (E_Cast d e).

  Inductive valid_expr (ct : class_table) (gamma : context) : expr -> Prop :=
  | Val_Var : forall x, type_checks ct gamma (E_Var x) -> valid_expr ct gamma (E_Var x)
  | Val_Field : forall e f c,
      type_checks ct gamma (E_Field e f) ->
      type_of gamma e c -> 
      (exists d, declaring_class f c = Some d) ->
      valid_expr ct gamma e ->
      valid_expr ct gamma (E_Field e f)
  | Val_New : forall c le,
      type_checks ct gamma (E_New c le) ->
      Forall (valid_expr ct gamma) le ->
      valid_expr ct gamma (E_New c le)
  | Val_Invk : forall e m le c,
      type_checks ct gamma (E_Invk e m le) ->
      valid_expr ct gamma e ->
      Forall (valid_expr ct gamma) le ->
      type_of gamma e c -> 
      (exists d, mresolve m c = Some d) ->
      valid_expr ct gamma (E_Invk e m le)
  | Val_Cast : forall c e,
      type_checks ct gamma (E_Cast c e) -> valid_expr ct gamma e -> valid_expr ct gamma (E_Cast c e)
  | Val_Lib : valid_expr ct gamma E_Lib.

  Definition calP (ct : class_table) (gamma : context) (e : expr) (lpt : set expr) :=
    type_checks ct gamma e /\ (forall e0, set_In e0 lpt -> type_checks ct gamma e0).

End props.
Section prop_lemmas.
  Axiom sub_keep_type : forall (gamma : context) (sig : subst) (e : expr) (c : class),
    type_of gamma e c -> type_of gamma (do_sub sig e) c.

  Lemma type_of_fn : forall gamma e c d,
    type_of gamma e c -> type_of gamma e d -> c = d.
  Proof.
    intros gamma e c d fc fd. generalize dependent d.
    induction fc; intros d0 fd0; inversion fd0; trivial.
    - assert (c = c0). apply IHfc; trivial.
      rewrite <- H5 in H4. rewrite H4 in H. inversion H. trivial.
    - assert (c0 = c1). apply IHfc; trivial.
      rewrite H14 in H. rewrite H in H8. inversion H8; trivial.
  Qed.

End prop_lemmas.

Section list_inductions.
  Definition expr_rect_list := 
    fun (P : expr -> Type) (Q : list expr -> Type)
      (g : Q nil) (h : forall e l, P e -> Q l -> Q (e :: l))
      (f : forall v : var, P (E_Var v))
      (f0 : forall e : expr, P e -> forall f0 : field_id, P (E_Field e f0))
      (f1 : forall (c : class) (l : list expr), Q l -> P (E_New c l))
      (f2 : forall e : expr, P e -> forall (m : method_id) (l : list expr), Q l -> P (E_Invk e m l))
      (f3 : forall (c : class) (e : expr), P e -> P (E_Cast c e)) (f4 : P E_Lib) =>
      fix F (e : expr) : P e :=
      match e as e0 return (P e0) with
      | E_Var v => f v
      | E_Field e0 f5 => f0 e0 (F e0) f5
      | E_New c l => f1 c l (list_rect Q g (fun u r => h u r (F u)) l)
      | E_Invk e0 m l => f2 e0 (F e0) m l (list_rect Q g (fun u r => h u r (F u)) l)
      | E_Cast c e0 => f3 c e0 (F e0)
      | E_Lib => f4
      end.

  Definition expr_ind_list :=
    fun (P : expr -> Prop) 
      (f : forall v : var, P (E_Var v))
      (f0 : forall e : expr, P e -> forall f0 : field_id, P (E_Field e f0))
      (f1 : forall (c : class) (l : list expr), Forall P l -> P (E_New c l))
      (f2 : forall e : expr, P e -> forall (m : method_id) (l : list expr), Forall P l -> P (E_Invk e m l))
      (f3 : forall (c : class) (e : expr), P e -> P (E_Cast c e))
      (f4 : P E_Lib) =>
      fix F (e : expr) : P e :=
      match e as e0 return (P e0) with
      | E_Var v => f v
      | E_Field e0 f5 => f0 e0 (F e0) f5
      | E_New c l => f1 c l (list_rect (Forall P) (Forall_nil P) (fun u _ => (Forall_cons u (F u))) l)
      | E_Invk e0 m l => f2 e0 (F e0) m l (list_rect (Forall P) (Forall_nil P) (fun u _ => Forall_cons u (F u)) l)
      | E_Cast c e0 => f3 c e0 (F e0)
      | E_Lib => f4
      end.

  Print Forall_list_impl.
  Print Forall.
  Definition alpha_ind_list :=
    fun (ct ct' : class_table) (gamma : context) (P : expr -> expr -> set expr -> Prop)
      (f : forall (e e' : expr) (f : field_id) (lpt : set expr),
          alpha ct ct' gamma e e' lpt -> P e e' lpt -> P (E_Field e f) (E_Field e' f) lpt)
      (f0 : forall (e : expr) (c d : class) (f0 : field_id) (lpt : set expr),
          alpha ct ct' gamma e E_Lib lpt ->
          P e E_Lib lpt ->
          declaring_class f0 c = Some d -> in_lib ct d -> type_of gamma e c -> P (E_Field e f0) E_Lib lpt)
      (f1 : forall (c : class) (le le' : list expr) (lpt : set expr),
          in_table ct' c ->
          length le = length le' ->
          Forall (fun p : expr * expr => alpha ct ct' gamma (fst p) (snd p) lpt) (combine le le') ->
          Forall (fun p : expr * expr => P (fst p) (snd p) lpt) (combine le le') ->
          P (E_New c le) (E_New c le') lpt)
      (f2 : forall (c : class) (le : list expr) (lpt : set expr),
          in_lib ct c ->
          Forall (fun e : expr => alpha ct ct' gamma e E_Lib lpt) le ->
          Forall (fun e : expr => P e E_Lib lpt) le ->
          P (E_New c le) E_Lib lpt)
      (f3 : forall (e e' : expr) (le le' : list expr) (m : method_id) (lpt : set expr),
          alpha ct ct' gamma e e' lpt ->
          P e e' lpt ->
          length le = length le' ->
          Forall (fun p : expr * expr => alpha ct ct' gamma (fst p) (snd p) lpt) (combine le le') ->
          Forall (fun p : expr * expr => P (fst p) (snd p) lpt) (combine le le') ->
          P (E_Invk e m le) (E_Invk e' m le') lpt)
      (f4 : forall (e : expr) (le : list expr) (mi : method_id) (lpt : set expr),
          (exists c : class, in_lib ct c /\ In mi (dmethods_id c)) ->
          alpha ct ct' gamma e E_Lib lpt ->
          P e E_Lib lpt ->
          Forall (fun e' : expr => alpha ct ct' gamma e' E_Lib lpt) le ->
          Forall (fun e : expr => P e E_Lib lpt) le ->
          P (E_Invk e mi le) E_Lib lpt)
      (f5 : forall (e e' : expr) (c : class) (lpt : set expr),
          alpha ct ct' gamma e e' lpt -> P e e' lpt -> P (E_Cast c e) (E_Cast c e') lpt)
      (f6 : forall (e : expr) (ci : class) (lpt : set expr),
          alpha ct ct' gamma e E_Lib lpt -> P e E_Lib lpt -> P (E_Cast ci e) E_Lib lpt)
      (f7 : forall (e e' : expr) (lpt : set expr),
          alpha ct ct' gamma e e' lpt -> P e e' lpt -> set_In e' lpt -> P e E_Lib lpt) =>
      fix F (e e0 : expr) (s : set expr) (a : alpha ct ct' gamma e e0 s) {struct a} : P e e0 s :=
      match a in (alpha _ _ _ e1 e2 s0) return (P e1 e2 s0) with
      | Rel_Field _ _ _ e1 e' f8 lpt a0 => f e1 e' f8 lpt a0 (F e1 e' lpt a0)
      | Rel_Lib_Field _ _ _ e1 c d f8 lpt a0 e2 i t => f0 e1 c d f8 lpt a0 (F e1 E_Lib lpt a0) e2 i t
      | Rel_New _ _ _ c le le' lpt i e1 f8 =>
        f1 c le le' lpt i e1 f8
           (let Q := (fun p => alpha ct ct' gamma (fst p) (snd p) lpt) in
            let P' := (fun p => P (fst p) (snd p) lpt) in
            (fix f_impl (l : list (expr * expr)) (F_Q : Forall Q l) : Forall P' l :=
               match F_Q with
               | Forall_nil _ => Forall_nil P'
               | @Forall_cons _ _ p l' Qp Ql' => Forall_cons p (F (fst p) (snd p) lpt Qp) (f_impl l' Ql')
               end) (combine le le') f8)
      | Rel_Lib_New _ _ _ c le lpt i f8 =>
        f2 c le lpt i f8
           (let Q := (fun e => alpha ct ct' gamma e E_Lib lpt) in
            let P' := (fun e => P e E_Lib lpt) in
            (fix f_impl (l : list expr) (F_Q : Forall Q l) : Forall P' l :=
               match F_Q with
               | Forall_nil _ => Forall_nil P'
               | @Forall_cons _ _ e l' Qe Ql' => Forall_cons e (F e E_Lib lpt Qe) (f_impl l' Ql')
               end) le f8)
      | Rel_Invk _ _ _ e1 e' le le' m lpt a0 e2 f8 =>
        f3 e1 e' le le' m lpt a0 (F e1 e' lpt a0) e2 f8
           (let Q := (fun p => alpha ct ct' gamma (fst p) (snd p) lpt) in
            let P' := (fun p => P (fst p) (snd p) lpt) in
            (fix f_impl (l : list (expr * expr)) (F_Q : Forall Q l) : Forall P' l :=
               match F_Q with
               | Forall_nil _ => Forall_nil P'
               | @Forall_cons _ _ p l' Qp Ql' => Forall_cons p (F (fst p) (snd p) lpt Qp) (f_impl l' Ql')
               end) (combine le le') f8)
      | Rel_Lib_Invk _ _ _ e1 le mi lpt e2 a0 f8 =>
        f4 e1 le mi lpt e2 a0 (F e1 E_Lib lpt a0) f8
           (let Q := (fun e => alpha ct ct' gamma e E_Lib lpt) in
            let P' := (fun e => P e E_Lib lpt) in
            (fix f_impl (l : list expr) (F_Q : Forall Q l) : Forall P' l :=
               match F_Q with
               | Forall_nil _ => Forall_nil P'
               | @Forall_cons _ _ e l' Qe Ql' => Forall_cons e (F e E_Lib lpt Qe) (f_impl l' Ql')
               end) le f8)
      | Rel_Cast _ _ _ e1 e' c lpt a0 => f5 e1 e' c lpt a0 (F e1 e' lpt a0)
      | Rel_Lib_Cast _ _ _ e1 ci lpt a0 => f6 e1 ci lpt a0 (F e1 E_Lib lpt a0)
      | Rel_Lpt _ _ _ e1 e' lpt a0 s0 => f7 e1 e' lpt a0 (F e1 e' lpt a0) s0
      end.

Section ct_lib_lemmas.
  Lemma in_lib_in_ct_lib : forall ct c,
    in_lib ct c -> in_table (ct_lib ct) c.
  Proof.
    intros ct c in_lib. destruct ct as [app lib].
    simpl in in_lib. unfold in_table. right. simpl. trivial.
  Qed.

  Lemma in_ct_lib_in_lib : forall (ct : class_table) (c : class),
      in_table (ct_lib ct) c -> in_lib ct c.
  Proof.
    intros ct c in_ct_lib.
    unfold in_table in in_ct_lib. destruct ct as [app lib].
    destruct in_ct_lib.
    - inversion H.
    - simpl. simpl in H. trivial.
  Qed.

  Lemma valid_table_valid_lib : forall (ct : class_table),
    valid_table ct -> valid_table (ct_lib ct).
  Proof.
    unfold valid_table. intros ct val_ct c in_ct_lib. destruct ct as (app, lib).
    apply in_ct_lib_in_lib in in_ct_lib as in_lib; trivial. 
    induction c as [|d].
    - apply V_Obj; eauto. 
    - simpl.
      assert (valid_class (app, lib) (C d l l0 l1)) as pfc.
      { apply val_ct. unfold in_table. right. trivial. }
      dependent destruction pfc. 
      assert (lib d).
      { destruct H0.
        - destruct H0. destruct H. split; trivial.
        - apply H0. }
      apply V_Class; eauto.
      + apply IHd; eauto. apply in_lib_in_ct_lib. eauto.
      + unfold not. intros. destruct H3. contradiction.
  Qed.

  Lemma type_checks_lib_ct : forall (ct : class_table) (gamma : context) (e : expr),
      valid_table ct -> type_checks (ct_lib ct) gamma e -> type_checks ct gamma e.
  Proof.
    intros ct gamma e pft typ_lib. 
    induction e using expr_ind_list; inversion typ_lib;
      try constructor; try apply TC_Field with d; try apply TC_Invk with d;
        try (unfold in_table; right; apply in_ct_lib_in_lib; trivial);
        try apply IHe; try (apply Forall_list_impl with (P := type_checks (ct_lib ct) gamma)); trivial.
  Qed.

  Lemma valid_expr_lib_ct : forall (ct : class_table) (gamma : context) (e : expr),
      valid_table ct -> valid_expr (ct_lib ct) gamma e -> valid_expr ct gamma e.
  Proof.
    intros ct gamma e pft val_lib.
    induction e using expr_ind_list; try inversion val_lib;
      try constructor; try (apply Val_Field with c); try (apply Val_Invk with c);
        try apply IHe; try apply type_checks_lib_ct;
          try (apply Forall_list_impl with (P := valid_expr (ct_lib ct) gamma)); trivial.
  Qed.

  Lemma typ_check_in_lib_typ_in_lib : forall ct gamma e c,
      type_checks (ct_lib ct) gamma e -> type_of gamma e c -> in_lib ct c.
  Proof.
    intros ct gamma e c typ_chk typ.
    destruct e; inversion typ; inversion typ_chk.
    - apply in_ct_lib_in_lib; trivial.
    - assert (c = d0). apply type_of_fn with gamma (E_Field e f); trivial.
      rewrite H9. apply in_ct_lib_in_lib; trivial.
    - rewrite <- H5. apply in_ct_lib_in_lib; trivial.
    - assert (c = d). apply type_of_fn with gamma (E_Invk e m l); trivial.
      rewrite H16. apply in_ct_lib_in_lib; trivial.
    - rewrite <- H0. apply in_ct_lib_in_lib; trivial.
  Qed.
End ct_lib_lemmas.
Section lemmas.
  Lemma mres_lib_in_lib : forall (ct : class_table) (m : method_id) (c e : class),
    valid_class ct c -> in_lib ct c -> mresolve m c = Some e -> in_lib ct e.
  Proof.
    intros ct m c e pfc c_in_app c_res_e.
    induction c as [|d].
    - inversion c_res_e.
    - unfold mresolve in c_res_e. destruct (existsb (fun m' : nat => beq_nat m m') (dmethods_id (C d l l0 l1))).
      + inversion c_res_e; trivial.
      + fold mresolve in c_res_e. dependent destruction pfc. apply IHd; trivial.
        destruct H0 as [[_ con] | [_ x]]; trivial.
        destruct H. split; trivial.
  Qed.

  Lemma find_In_var : forall lv v,
      In v lv <-> find (fun v' => beq_var v' v) lv <> None.
  Proof.
    split; induction lv; intros; eauto; simpl; simpl in H.
    - destruct H.
      + rewrite H. rewrite <- beq_var_refl. unfold not. intro. inversion H0.
      + destruct (beq_var a v); eauto. unfold not. intro. inversion H0.
    - apply H. reflexivity.
    - destruct (beq_var a v) eqn:beq_av.
      + left. apply beq_var_true. eauto.
      + right. apply IHlv. trivial.
  Qed.

End lemmas.

Section eq_dec.
  Lemma eq_var_dec : forall v v' : var, {v = v'} + {v <> v'}.
  Proof.
    intros. destruct v; destruct v'; try solve [right; unfold not; intro; inversion H].
    - assert ({v = v0} + {v <> v0}) by apply PeanoNat.Nat.eq_dec.
      destruct H.
      + left. rewrite e. reflexivity.
      + right. unfold not. intros. inversion H. contradiction.
    - left. trivial.
  Qed.


  Inductive Forallt {A : Set} (P : A -> Set) : list A -> Set :=
  | Forallt_nil : Forallt P nil
  | Forallt_cons : forall a l, P a -> Forallt P l -> Forallt P (a :: l).

  Lemma eq_expr_class_dech : forall (e e' : expr) (c c' : class), ({e = e'} + {e <> e'}) * ({c = c'} + {c <> c'}).
  Proof.
    induction e using expr_rect_list with (Q := fun l => forall e', Forallt (fun e : expr => {e = e'} + {e <> e'}) l).
    - intros. apply Forallt_nil.
    - intros. assert (({e = e'} + {e <> e'}) * ({Obj = Obj} + {Obj <> Obj})). apply IHe.
      destruct H. apply Forallt_cons; eauto.
    - intros. destruct e'.
      + assert ({ v = v0 } + {v <> v0}) by apply eq_var_dec.
        destruct H.
        * Admitted. (*left. rewrite e. reflexivity.
                     * right. unfold not. intros. inversion H. contradiction.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
  - intros. destruct e'.
    + right. unfold not. intro. inversion H.
    + assert ({f = f0} + {f <> f0}) by apply PeanoNat.Nat.eq_dec.
      assert ({e = e'} + {e <> e'}) by apply IHe.
      destruct H; destruct H0.
      * left. rewrite e0. rewrite e1. reflexivity.
      * right. unfold not. intros. inversion H. contradiction.
      * right. unfold not. intros. inversion H. symmetry in H2. contradiction.
      * right. unfold not. intros. inversion H. contradiction.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
  - intros. destruct e'.
    + right. unfold not. intro. inversion H.
    + right. unfold not. intro. inversion H.
    + (* assert ({c = c0} + {c <> c0}) by apply PeanoNat.Nat.eq_dec. *)
Admitted. *)

  Lemma eq_class_dec : forall c c' : class, {c = c'} + {c <> c'}.
  Proof.
    intros.
    assert (({E_Var This = E_Var This} + {E_Var This <> E_Var This}) * ({c = c'} + {c <> c'})).
    apply eq_expr_class_dech.
    destruct H.
    apply s0.
  Qed.

  Lemma eq_expr_dec : forall e e' : expr, {e = e'} + {e <> e'}.
  Proof.
    intros e.
    induction e using expr_rect_list with (Q := fun l => forall e', Forallt (fun e : expr => {e = e'} + {e <> e'}) l).
    - intros. apply Forallt_nil.
    - intros. apply Forallt_cons; eauto.
    - intros. destruct e'.
      + assert ({ v = v0 } + {v <> v0}) by apply eq_var_dec.
        destruct H.
        * left. rewrite e. reflexivity.
        * right. unfold not. intros. inversion H. contradiction.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
    - intros. destruct e'.
      + right. unfold not. intro. inversion H.
      + assert ({f = f0} + {f <> f0}) by apply PeanoNat.Nat.eq_dec.
        assert ({e = e'} + {e <> e'}) by apply IHe.
        destruct H; destruct H0.
        * left. rewrite e0. rewrite e1. reflexivity.
        * right. unfold not. intros. inversion H. contradiction.
        * right. unfold not. intros. inversion H. symmetry in H2. contradiction.
        * right. unfold not. intros. inversion H. contradiction.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
    - intros. destruct e'.
      + right. unfold not. intro. inversion H.
      + right. unfold not. intro. inversion H.
      + (* assert ({c = c0} + {c <> c0}) by apply PeanoNat.Nat.eq_dec. *)
  Admitted.

End eq_dec.
Section reduction_rules.
  Inductive FJ_reduce : expr -> expr -> Prop :=
  | R_Field : forall c f le ei n,
      index_of (fun p => beq_nat f (snd p)) (fields c) = Some n ->
      nth_error le n = Some ei ->
      FJ_reduce (E_New c le) ei
  | R_Invk : forall c m mi le newle,
      valid_method m -> find_method mi c = Some m ->
      FJ_reduce (E_Invk (E_New c newle) mi le)
                (do_sub ((This, (E_New c newle)) :: (combine (args m) le)) (body m))
  | R_Cast : forall c d le,
      subtype c d -> FJ_reduce (E_Cast d (E_New c le)) (E_New c le)
  | RC_Field : forall e e' f,
      FJ_reduce e e' -> FJ_reduce (E_Field e f) (E_Field e' f)
  | RC_Invk_Recv : forall e e' m le,
      FJ_reduce e e' -> FJ_reduce (E_Invk e m le) (E_Invk e' m le)
  | RC_Invk_Arg : forall e m le le' e0 e0' n,
      nth_error le n = Some e0 -> nth_error le' n = Some e0' ->
      FJ_reduce e0 e0' -> FJ_reduce (E_Invk e m le) (E_Invk e m le')
  | RC_New_Arg : forall c le le' e0 e0' n,
      nth_error le n = Some e0 -> nth_error le' n = Some e0' ->
      FJ_reduce e0 e0' -> FJ_reduce (E_New c le) (E_New c le')
  | RC_Cast : forall c e e',
      FJ_reduce e e' -> FJ_reduce (E_Cast c e) (E_Cast c e').

  Variable f : nat -> set nat.
  Variable a : set nat.
  Check (a U a).
  Inductive AVE_reduce (ct : class_table) : expr -> set expr -> expr -> set expr -> Prop :=
  | RA_FJ : forall e e' lpt,
      FJ_reduce e e' -> AVE_reduce ct e lpt e' lpt
  | RA_Field : forall f c d e lpt,
      declaring_class f c = Some d -> in_lib ct d ->
      AVE_reduce ct e lpt e (add (E_Field E_Lib f) lpt)
  | RA_New : forall c e lpt,
      in_lib ct c ->
      AVE_reduce ct e lpt e (add (E_New c (repeat E_Lib (length (fields c)))) lpt)
  | RA_Invk : forall m c e lpt,
      In m (dmethods c) -> in_lib ct c ->
      AVE_reduce ct e lpt e (add (E_Invk E_Lib (mid m) (repeat E_Lib (length (args m)))) lpt)
  | RA_Cast : forall c lpt, AVE_reduce ct (E_Cast c E_Lib) lpt E_Lib lpt
  | RA_Lib_Invk : forall mi c newle largs d lpt,
      mresolve mi c = Some d -> in_lib ct d ->
      AVE_reduce ct
                 (E_Invk (E_New c newle) mi largs)
                 lpt
                 E_Lib
                 (add (E_New c newle) (set_from_list largs U lpt))
  | RA_Return : forall e lpt,
      set_In e lpt -> AVE_reduce ct E_Lib lpt e lpt
  | RA_Sub : forall e e' lpt lpt' d,
      set_In e lpt -> AVE_reduce ct e lpt e' lpt' ->
      AVE_reduce ct d lpt d (add e' (lpt' U lpt))
  | RAC_Field : forall e e' lpt lpt' f,
      AVE_reduce ct e lpt e' lpt' ->
      AVE_reduce ct (E_Field e f) lpt (E_Field e' f) (lpt' U lpt)
  | RAC_Invk_Recv : forall e e' m le lpt lpt',
      AVE_reduce ct e lpt e' lpt' ->
      AVE_reduce ct (E_Invk e m le) lpt (E_Invk e' m le) (lpt' U lpt)
  | RAC_Invk_Arg : forall e m le le' e0 e0' n lpt lpt',
      nth_error le n = Some e0 -> nth_error le' n = Some e0' ->
      AVE_reduce ct e0 lpt e0' lpt' ->
      AVE_reduce ct (E_Invk e m le) lpt (E_Invk e m le') (lpt' U lpt)
  | RAC_New_Arg : forall c le le' e0 e0' n lpt lpt',
      nth_error le n = Some e0 -> nth_error le' n = Some e0' ->
      AVE_reduce ct e0 lpt e0' lpt' ->
      AVE_reduce ct (E_New c le) lpt (E_New c le') (lpt' U lpt)
  | RAC_Cast : forall c e e' lpt lpt',
      AVE_reduce ct e lpt e' lpt' ->
      AVE_reduce ct (E_Cast c e) lpt (E_Cast c e') (lpt' U lpt).

  Inductive AVE_reduce' (ct : class_table) : expr -> set expr -> expr -> set expr -> Prop :=
  | RA'_refl : forall e lpt, AVE_reduce' ct e lpt e lpt
  | RA'_step : forall e lpt e' lpt' e'' lpt'',
      AVE_reduce ct e lpt e' lpt' ->
      AVE_reduce' ct e' lpt' e'' lpt'' ->
      AVE_reduce' ct e lpt e'' lpt''.

End reduction_rules.
Lemma lemma1 : forall (ct : class_table) (c e : class) (m : method_id),
    valid_class ct c -> mresolve m c = Some e -> in_app ct e -> in_app ct c.
Proof.
  intros ct c e m pfc c_res_e e_in_app. induction c as [| d].
  - intros. inversion c_res_e.
  - unfold mresolve in c_res_e. destruct (existsb (fun m' : nat => beq_nat m m') (dmethods_id (C d l l0 l1))).
    + inversion c_res_e. rewrite H0. trivial.
    + fold mresolve in c_res_e. dependent destruction pfc.
      assert (in_app ct d). apply IHd; trivial.
      destruct H0.
      * apply H0.
      * destruct d.
        -- inversion pfc. contradiction.
        -- inversion pfc. destruct H8. split; eauto. apply H0.
Qed.

Lemma lemma2 : forall ct ct' c m e,
    ave_rel ct ct' -> valid_class ct c -> valid_class ct' c ->
    in_app ct c -> mresolve m c = Some e ->
    in_app ct e \/ in_lib ct' e.
Proof.
  intros ct ct' c m e rel pfc pfc' c_in_app c_res_e.
  induction c as [|d].
  (* C is Obj *)
  - inversion pfc. contradiction.
  (* c extends d *)
  - unfold mresolve in c_res_e. destruct (existsb (fun m' : nat => beq_nat m m') (dmethods_id (C d l l0 l1))).
    (* m-res *)
    + left. inversion c_res_e. trivial.
    (* m-res-inh *)
    + fold mresolve in c_res_e. dependent destruction pfc. dependent destruction pfc'.
      destruct H0 as [[d_in_app _] | [_ d_in_lib]].
      (* d in app - use induction hypothesis *)
      * apply IHd; trivial.
      (* d in lib - use averroes transformation properties *)
      * right. apply mres_lib_in_lib with m d; trivial.
        inversion rel as [_ [_ [keep_app keep_lib]]].
        apply keep_lib with (C d l l0 l1); simpl; trivial.
        unfold in_table. left. apply keep_app. trivial.
Qed.

Lemma lemma3 : forall ct ct' lv le le' gamma e0 lpt,
    ave_rel ct ct' ->
    (length lv = length le) -> (length lv = length le') ->
    (forall v, expr_In v e0 -> In v lv) ->
    (Forall (fun p => alpha ct ct' gamma (fst p) (snd p) lpt) (combine le le')) ->
    type_checks ct' gamma e0 -> fj_expr e0 ->
    alpha ct ct' gamma (do_sub (combine lv le) e0) (do_sub (combine lv le') e0) lpt.
Proof.
  intros ct ct' lv le le' gamma e0 lpt rel lenve lenve' valid_body sub_rel typ_chk fj_expr.
  induction e0 using expr_ind_list.
  (* Case Var *)
  - simpl. destruct (find (fun p : var * expr => beq_var (fst p) v) (combine lv le)) eqn:sigv.
    + destruct (find (fun p0 : var * expr => beq_var (fst p0) v) (combine lv le')) eqn:sigv'.
      * assert (In (snd p, snd p0) (combine le le')).
        { apply find_pair_in_zip with (la := lv) (f := (fun v' => beq_var v' v)); trivial. }
        destruct p. destruct p0. simpl in H. 
        assert (alpha ct ct' gamma (fst (e, e0)) (snd (e, e0)) lpt).
        { apply Forall_In with (l := combine le le') (a := (e, e0)); trivial. }
        eauto.
      * apply (extract_combine (fun v' => beq_var v' v) lv le' lenve') in sigv'.
        assert (In v lv). apply valid_body. apply EIn_Var.
        apply find_In_var in H. contradiction.
    + apply (extract_combine (fun v' => beq_var v' v) lv le lenve) in sigv.
      assert (In v lv). apply valid_body. apply EIn_Var.
      apply find_In_var in H. contradiction.
  (* Case Field *)
  - simpl. inversion typ_chk. inversion fj_expr. apply Rel_Field; eauto. apply IHe0; eauto.
    intros. apply EIn_Field with (f := f0) in H7. apply valid_body; trivial.
  (* Case New *)
  - simpl. inversion typ_chk. inversion fj_expr. apply Rel_New; eauto.
    + rewrite map_length, map_length. reflexivity.
    + clear typ_chk H1 H6 fj_expr. induction l.
      * apply Forall_nil.
      * inversion H. inversion H3. inversion H5. apply Forall_cons; eauto.
        -- simpl. apply H7; eauto.
           intros. apply valid_body; eauto.
           apply EIn_New; eauto.
        -- apply IHl; eauto.
           intros. apply valid_body. apply EIn_New. inversion H17.
           apply Exists_cons_tl; eauto.
  (* Case Invk *)
  - simpl. inversion typ_chk. inversion fj_expr. apply Rel_Invk; eauto.
    + apply IHe0; eauto. intros. apply valid_body. apply EIn_Invk; eauto.
    + rewrite map_length, map_length. reflexivity.
    + clear H2 H3 typ_chk fj_expr H10. induction l.
      * apply Forall_nil.
      * inversion H. inversion H6. inversion H11. apply Forall_cons; eauto.
        -- simpl. apply H10; eauto.
           intros. apply valid_body; eauto.
           apply EIn_Invk; eauto.
        -- apply IHl; eauto.
           intros. apply valid_body. apply EIn_Invk. inversion H21. destruct H24; eauto.
  - simpl. inversion typ_chk. inversion fj_expr. apply Rel_Cast; eauto.
    apply IHe0; eauto. intros. apply valid_body. apply EIn_Cast; eauto.
  - inversion fj_expr.
Qed.

Lemma lemma4 : forall ct ct' lv le gamma e0 lpt,
    ave_rel ct ct' ->
    length lv = length le ->
    (forall v, expr_In v e0 -> In v lv) ->
    (Forall (fun e => alpha ct ct' gamma e E_Lib lpt) le) ->
    valid_expr (ct_lib ct) gamma e0 -> fj_expr e0 ->
    alpha ct ct' gamma (do_sub (combine lv le) e0) E_Lib lpt.
Proof. 
  intros ct ct' lv le gamma e0 lpt rel lenve valid_body sub_rel val_in_lib fj_expr.
  apply valid_expr_lib_ct in val_in_lib as val_in_ct. inversion rel as [pft [pft' [keep_app keep_lib]]].
  induction e0 using expr_ind_list; eauto.
  - simpl. destruct (find (fun p : var * expr => beq_var (fst p) v) (combine lv le)) eqn:sigv.
    + apply find_some in sigv. destruct sigv. destruct p. apply zip_In_r in H.
      apply Forall_In with (l := le) (a := e); eauto.
    + apply (extract_combine (fun v' => beq_var v' v) lv le lenve) in sigv.
      assert (In v lv). apply valid_body. apply EIn_Var.
      apply find_In_var in H. contradiction.
  - simpl. inversion val_in_lib. inversion val_in_ct. inversion fj_expr. destruct H3 as [d decl].
    apply Rel_Lib_Field with c d; eauto.
    + apply IHe0; eauto.
      intros. apply valid_body. apply EIn_Field. eauto.
    + assert (in_lib ct c). inversion H1. apply typ_check_in_lib_typ_in_lib with gamma e0; trivial.
      apply decl_of_lib_in_lib with c f0; trivial.
    + apply sub_keep_type; trivial.
  - simpl. inversion val_in_lib. inversion val_in_ct. inversion fj_expr. 
    apply Rel_Lib_New; eauto.
    + inversion H2. apply in_ct_lib_in_lib; trivial.
    + assert (Forall (fun e0 => (forall v : var, expr_In v e0 -> In v lv)) l).
      { apply Forall_forall. intros. apply valid_body.
        apply EIn_New. apply Exists_exists; eauto. }
      apply Forall_list_impl with (P := fun e0 => (forall v, expr_In v e0 -> In v lv)) in H; trivial.
      apply Forall_list_impl with (P := valid_expr (ct_lib ct) gamma) in H; trivial.
      apply Forall_list_impl with (P := valid_expr ct gamma) in H; trivial.
      apply Forall_list_impl with (P := Top.fj_expr) in H; trivial.
      rewrite Forall_map_swap. trivial.
  - simpl. inversion val_in_lib. inversion val_in_ct. inversion fj_expr. 
    apply Rel_Lib_Invk; eauto.
    + destruct H7 as [d mres_d]. exists d.
      assert (in_lib ct c).
      { inversion H3. apply typ_check_in_lib_typ_in_lib with gamma e0; trivial. }
      split.
      * apply mres_lib_in_lib with m c; trivial.
        apply pft. unfold in_table. right; trivial.
      * apply mresolve_in_methods with c; trivial.
    + apply IHe0; eauto. intros. apply valid_body. apply EIn_Invk. eauto.
    + assert (Forall (fun e0 => (forall v : var, expr_In v e0 -> In v lv)) l).
      { apply Forall_forall. intros. apply valid_body.
        apply EIn_Invk. left. apply Exists_exists; eauto. }
      apply Forall_list_impl with (P := fun e0 => (forall v, expr_In v e0 -> In v lv)) in H; trivial.
      apply Forall_list_impl with (P := valid_expr (ct_lib ct) gamma) in H; trivial.
      apply Forall_list_impl with (P := valid_expr ct gamma) in H; trivial.
      apply Forall_list_impl with (P := Top.fj_expr) in H; trivial.
      rewrite Forall_map_swap. trivial.
  - simpl. inversion val_in_lib. inversion val_in_ct. inversion fj_expr. 
    apply Rel_Lib_Cast. apply IHe0; eauto.
    intros. apply valid_body. apply EIn_Cast. eauto.
  - inversion fj_expr.
  - inversion rel; trivial.
Qed.

Lemma lemma5 : forall ct ct' gamma e e' lpt lpt',
    alpha ct ct' gamma e e' lpt -> alpha ct ct' gamma e e' (lpt U lpt').
Proof.
  intros ct ct' gamma e e' lpt lpt' rel.
  induction rel using alpha_ind_list; try constructor;
    try apply Rel_Lib_Field with c d; try apply Rel_Lpt with e'; try apply union_introl; trivial.
Qed.

(*

Definition not_derived_by_Rel_Lpt
           {ct ct' : class_table} {gamma : context}
           {e : expr} {y' : expr} {lpt : set expr}
           (rel : alpha ct ct' gamma e y' lpt) : Prop :=
  match y' as y return alpha ct ct' gamma e y lpt -> Prop with
  | E_Lib => fun rel => ~ exists pfe ine, rel = Rel_Lpt ct ct' gamma e E_Lib lpt pfe ine
  | _ => fun _ => True
  end rel.

Inductive eg : Prop :=
| eg1 : eg
| eg2 : eg.

Lemma silly : eg1 <> eg2.
Proof. unfold not. intros. discriminate H.

Definition eg_rect := 
fun (P : forall n : nat, eg n -> Prop) (f : forall n : nat, P (S n) (eg1 n)) (f0 : P 5 eg2) (n : nat) (e : eg n) =>
match e as e0 in (eg n0) return (P n0 e0) with
| eg1 x => f x
| eg2 => f0
end.

Definition silly (p : eg1 4 = eg2) :=
  match p in _ = e return match e as e0 in (eg 5) return Prop with
                          | eg2 => False
                          | _ => True
                          end
  with
  | eq_refl => I
  end.

Lemma aslkjasdg : forall ct ct' gamma e c d f lpt H0 e0 i t pfe ine,
    Rel_Lib_Field ct ct' gamma e c d f lpt H0 e0 i t = Rel_Lpt ct ct' gamma (E_Field e f) E_Lib lpt pfe ine -> False.
Proof. intros. 

Lemma lemma6 : forall ct ct' gamma e e' lpt,
    ave_rel ct ct' -> alpha ct ct' gamma e e' lpt -> calP ct' gamma e' lpt ->
    exists y', calP ct' gamma e' lpt /\
          (exists pf : alpha ct ct' gamma e y' lpt, not_derived_by_Rel_Lpt pf) /\
          AVE_reduce' ct' e' lpt y' lpt.
Proof.
  intros.
  remember H0 as H0'.
  remember e' as e'rem.
  destruct H0.
  
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. rewrite <- simpl. rewrite HeqH0'. simpl.
    unfold not. intros exst. destruct exst as [pfe [ine abasdg]]. 
    rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists e'. split; eauto. split. rewrite <- Heqe'rem. exists H0'. apply I. rewrite <- Heqe'rem. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl.
  - exists (E_Field e' f). split; trivial. split. exists H0'. apply I. apply RA'_refl. *)
Lemma lemma7addextra : forall A (ns lpt' lpt : set A),
    ns U lpt' U lpt = (ns U lpt') U ns U lpt.
Proof.
  intros.
  rewrite (union_comm ns lpt'). rewrite union_assoc.
  rewrite <- (union_assoc ns ns lpt). rewrite union_same.
  rewrite <- union_assoc. rewrite (union_comm ns lpt').
  rewrite union_assoc. reflexivity.
Qed.

Lemma lemma7 : forall ct' e e' lpt lpt' ns,
    AVE_reduce ct' e lpt e' lpt' -> AVE_reduce ct' e (union ns lpt) e' (union ns lpt').
Proof.
  intros ct' e e' lpt lpt' ns reduce.
  induction reduce; try solve [constructor; trivial; try apply union_intror; try apply H]; try rewrite union_addr; try rewrite lemma7addextra;
    try constructor; try apply RA_Field with c d; try apply RA_Invk with c;
      try apply RAC_Invk_Arg with e0 e0' n; try apply RAC_New_Arg with e0 e0' n; trivial.
  - rewrite <- lemma7addextra. rewrite <- union_assoc.
    rewrite (union_comm ns (set_from_list largs)). rewrite union_assoc.
    apply RA_Lib_Invk with d; trivial.
  - rewrite <- lemma7addextra. rewrite <- union_assoc. rewrite (union_comm ns lpt'). rewrite union_assoc.
    assert (lpt' U ns U lpt = (ns U lpt') U ns U lpt).
    { rewrite <- (union_assoc (ns U lpt') ns lpt).
      rewrite (union_comm ns lpt'). rewrite (union_assoc lpt' ns ns).
      rewrite union_same. rewrite union_assoc. reflexivity. }
    rewrite H0.
    apply RA_Sub with e; trivial. apply union_intror. apply H.
Qed.

Lemma lemma8 : forall ct' e e' lpt lpt',
    AVE_reduce ct' e lpt e' lpt' -> subset lpt lpt'.
Proof. 
  intros. unfold subset. unfold E.Included.
  induction H; intros;
    solve [ apply union_introl; solve [ apply union_introl; reflexivity || trivial
                                      | apply union_intror; reflexivity || trivial
                                      | reflexivity || trivial]
          | apply union_intror; solve [ apply union_introl; reflexivity || trivial
                                      | apply union_intror; reflexivity || trivial
                                      | reflexivity || trivial]
          | reflexivity || trivial].
Qed.


Lemma lemma9setfromlist : forall {A : Type} (l : list A) (n : nat) (a : A),
    length l = S n -> nth_error l n = Some a ->
    set_from_list (first_n l (S n)) = add a (set_from_list (first_n l n)).
Proof.
  induction l; intros; simpl; inversion H.
  destruct n; rewrite H2; inversion H0.
  - simpl. destruct l; simpl; reflexivity.
  - simpl. rewrite IHl with n a0; trivial.
    unfold add. unfold E.Add. rewrite union_assoc. rewrite (union_comm (E.Singleton A a0) (E.Singleton A a)).
    rewrite <- union_assoc. reflexivity.
Qed.

Lemma lemma9 : forall ct' n le e0 llpt lpt0,
    length le = S n -> length llpt = S n ->
    hd_error le = Some e0 -> hd_error llpt = Some lpt0 ->
    e0 <> E_Lib -> set_In e0 lpt0 ->
    (forall m e lpt e0 lpt0,
        m < n -> nth_error le m = Some e -> nth_error llpt m = Some lpt ->
        nth_error le (S m) = Some e0 -> nth_error llpt (S m) = Some lpt0 ->
        AVE_reduce ct' e lpt e0 lpt0) ->
    (forall m lpt lpt0,
        m < n -> nth_error llpt m = Some lpt -> nth_error llpt (S m) = Some lpt0 ->
        AVE_reduce ct' E_Lib (set_from_list (first_n le (S m)) U lpt)
                   E_Lib (set_from_list (first_n le (S (S m))) U lpt0)).
Proof.
  induction n.
  - intros le e0 llpt lpt0 len_le len_llpt hde0 hdlpt0 neq_lib_e0 in_e_lpt0
           n_reduce m lpt_m lpt_sm le_m_n index_lpt_m index_lpt_sm.
    inversion le_m_n.
  - intros le e0 llpt lpt0 len_le len_llpt hde0 hdlpt0 neq_lib_e0 in_e_lpt0
           n_reduce m lpt_m lpt_sm le_m_n index_lpt_m index_lpt_sm.
    destruct le; inversion len_le.
    destruct llpt; inversion len_llpt.
    inversion hde0. inversion hdlpt0.
    assert ({ m = n } + { m <> n }) by apply PeanoNat.Nat.eq_dec. destruct H.
    + subst m. subst e0.
      assert (exists e', nth_error (e :: le) n = Some e').
      { apply get_nth with (n0 := S (S n)); trivial.
        apply le_S. apply le_m_n. }
      destruct H as [e_m index_e_m].
      assert (exists e', nth_error (e :: le) (S n) = Some e').
      { apply get_nth with (n0 := S (S n)); trivial.
        apply Lt.lt_n_S. apply le_m_n. }
      destruct H as [e_Sm index_e_Sm].
      assert (AVE_reduce ct' e_m lpt_m e_Sm lpt_sm).
      { apply n_reduce with n; trivial. }
      assert (AVE_reduce ct' e_m (set_from_list (first_n (e :: le) (S n)) U lpt_m)
                             e_Sm (set_from_list (first_n (e :: le) (S n)) U lpt_sm)).
      { apply lemma7; trivial. }
      assert (set_from_list (first_n (e :: le) (S (S n))) = add e_Sm (set_from_list (first_n (e :: le) (S n)))).
      { apply lemma9setfromlist; trivial. }
      rewrite H4. rewrite union_addl.
      assert (lpt_sm = lpt_sm U lpt_m).
      { apply union_include. apply lemma8 with ct' e_m e_Sm; trivial. }
      rewrite H5. rewrite (union_comm lpt_sm lpt_m). rewrite <- union_assoc.
      remember (set_from_list (first_n (e :: le) (S n)) U lpt_m) as lpt_m'.
      rewrite <- (union_same lpt_m').
      rewrite (union_comm (lpt_m' U lpt_m')).
      rewrite <- union_assoc.
      rewrite union_same.
      apply RA_Sub with e_m; trivial.
      * rewrite Heqlpt_m'. apply union_introl. apply In_list_set_In_list. apply nth_error_In with n.
        apply nth_error_first_n. apply index_e_m.
      * rewrite union_comm. rewrite Heqlpt_m'. rewrite union_assoc. rewrite (union_comm lpt_m).
        rewrite <- (union_include lpt_m lpt_sm). rewrite <- Heqlpt_m'. apply H2.
        apply lemma8 with ct' e_m e_Sm. trivial.
    + subst e. subst s.
      rewrite remove_last_first_n.
      rewrite (remove_last_first_n (e0 :: le) (S (S m))).
      apply IHn with e0 (remove_last (lpt0 :: llpt)) lpt0; trivial.
      * rewrite <- (remove_last_length (e0 :: le)). reflexivity. trivial.
      * rewrite <- (remove_last_length (lpt0 :: llpt)). reflexivity. trivial.
      * destruct le. inversion len_le. reflexivity.
      * destruct llpt. inversion len_llpt. reflexivity.
      * intros. apply n_reduce with m0; eauto;
                  rewrite remove_last_nth_error; eauto; rewrite len_le || rewrite len_llpt; apply Lt.lt_n_S;
                    solve [apply Lt.lt_S; trivial | apply Lt.lt_n_S; trivial].
      * inversion le_m_n. contradiction. apply H2.
      * rewrite <- remove_last_nth_error. trivial. rewrite len_llpt. apply Lt.lt_n_S. trivial.
      * rewrite <- remove_last_nth_error. trivial. rewrite len_llpt.
        apply Lt.lt_n_S. apply Lt.lt_n_S. inversion le_m_n. contradiction. apply H2.
      * rewrite len_le. apply Lt.lt_n_S. apply Lt.lt_n_S. inversion le_m_n. contradiction. apply H2.
      * rewrite len_le. apply Lt.lt_n_S. apply le_m_n.
Qed.

Lemma E_Lib_dec : forall e, e = E_Lib \/ e <> E_Lib.
Proof.
  intros. destruct e; solve [left; trivial | right; discriminate].
Qed.

Lemma use_lemma_9_1 : forall ct' e lpt e' lpt',
    AVE_reduce' ct' e lpt e' lpt' -> exists le llpt n,
        length le = S n /\ length llpt = S n /\
        hd_error le = Some e /\ hd_error llpt = Some lpt /\
        last_error le = Some e' /\ last_error llpt = Some lpt' /\
        (forall m e lpt e0 lpt0,
            m < n -> nth_error le m = Some e -> nth_error llpt m = Some lpt ->
            nth_error le (S m) = Some e0 -> nth_error llpt (S m) = Some lpt0 ->
            AVE_reduce ct' e lpt e0 lpt0).
Proof.
  intros. induction H.
  - exists (e :: nil). exists (lpt :: nil). exists 0.
    split; split; split; split; split; split; trivial || intros. inversion H.
  - destruct IHAVE_reduce' as [le [llpt [n [len_le [len_llpt [hd_le [hd_llpt [last_le [last_llpt AVE_each]]]]]]]]].
    exists (e :: le). exists (lpt :: llpt). exists (S n).
    split; try split; try split; try split; try split; try split.
    + simpl. rewrite len_le. reflexivity.
    + simpl. rewrite len_llpt. reflexivity.
    + simpl. destruct le; inversion len_le. rewrite last_le. reflexivity.
    + simpl. destruct llpt; inversion len_llpt. rewrite last_llpt. reflexivity.
    + intros. destruct m.
      * inversion H2. inversion H3. inversion H4. inversion H5.
        destruct le; inversion len_le. destruct llpt; inversion len_llpt.
        subst e0. subst lpt0. inversion hd_le. inversion hd_llpt. subst e2. subst s.
        inversion H9. inversion H10. subst e1. subst lpt1. trivial.
      * apply AVE_each with m; try assumption.
        apply Lt.lt_S_n. apply H1.
Qed.

Lemma unuse_lemma_9_1 : forall n ct' e lpt e' lpt' le llpt,
    length le = S n -> length llpt = S n ->
    hd_error le = Some e -> hd_error llpt = Some lpt ->
    last_error le = Some e' -> last_error llpt = Some lpt' ->
    (forall m e lpt e0 lpt0,
        m < n -> nth_error le m = Some e -> nth_error llpt m = Some lpt ->
        nth_error le (S m) = Some e0 -> nth_error llpt (S m) = Some lpt0 ->
        AVE_reduce ct' e lpt e0 lpt0) ->
    AVE_reduce' ct' e lpt e' lpt'.
Proof.
  induction n.
  - intros.
    destruct le; inversion H1. destruct le; inversion H.
    destruct llpt; inversion H4. destruct llpt; inversion H0.
    subst e0. inversion H8. subst s. inversion H2. inversion H3.
    subst e'. subst lpt'. apply RA'_refl.
  - intros ct' e lpt e' lpt' le llpt len_le len_llpt hd_le hd_llpt last_le last_llpt AVE_each.
    destruct le as [| e0 le']; inversion len_le as [len_le'].
    destruct le' as [| e1 le'']; inversion len_le' as [len_le''].
    destruct llpt as [| lpt0 llpt']; inversion len_llpt as [len_llpt'].
    destruct llpt' as [| lpt1 llpt'']; inversion len_llpt' as [len_llpt''].
    apply RA'_step with e1 lpt1.
    + apply AVE_each with 0; trivial. unfold lt. apply le_n_S. apply le_0_n.
    + apply IHn with (e1 :: le'') (lpt1 :: llpt''); trivial.
      intros. apply AVE_each with (S m); try assumption.
      apply Lt.lt_n_S. assumption.
Qed.

Lemma lemma10 : forall ct ct' gamma e0 e0' e' lpt lpt',
    alpha ct ct' gamma e0 E_Lib lpt -> alpha ct ct' gamma e0' e' lpt' ->
    FJ_reduce e0 e0' -> AVE_reduce' ct' E_Lib lpt e' lpt' -> exists lpt'',
        alpha ct ct' gamma e0' E_Lib lpt'' /\ AVE_reduce' ct' E_Lib lpt E_Lib lpt''.
Proof.
  intros. destruct (E_Lib_dec e').
  - exists lpt'. subst e'. split; trivial.
  - dependent induction H2; try (destruct H3; reflexivity).
    destruct (E_Lib_dec e').
    + assert (exists lpt'' : set expr,
                 alpha ct ct' gamma e0' E_Lib lpt'' /\ AVE_reduce' ct' E_Lib lpt' E_Lib lpt'').
      { apply IHAVE_reduce'; trivial.
        - rewrite (union_include lpt lpt').
          + rewrite union_comm. apply lemma5. trivial.
          + apply lemma8 with ct' E_Lib e'; trivial. }
      destruct H6 as [lpt''0 [alph AVE_red]].
      exists lpt''0. split; trivial.
      subst e'. apply RA'_step with E_Lib lpt'; trivial.
    + inversion H2.
      * inversion H6.
      * symmetry in H10. contradiction.
      * symmetry in H9. contradiction.
      * symmetry in H10. contradiction.
      * subst lpt. subst lpt'. subst e'. rename e'' into e'. rename lpt'' into lpt'.
        assert (exists lpt''', AVE_reduce' ct' E_Lib lpt0 E_Lib lpt''' /\
                          subset lpt' lpt''' /\
                          set_In e' lpt''').
        { apply use_lemma_9_1 in H3 as H7.
          destruct H7 as [le [llpt [n [len_le [len_llpt [hd_le [hd_llpt [last_le [last_llpt AVE_each]]]]]]]]].
          assert (forall m lpt lpt0,
                     m < n -> nth_error llpt m = Some lpt -> nth_error llpt (S m) = Some lpt0 ->
                     AVE_reduce ct' E_Lib (set_from_list (first_n le (S m)) U lpt)
                                E_Lib (set_from_list (first_n le (S (S m))) U lpt0)).
          apply lemma9 with e lpt0; assumption.
          exists (set_from_list (first_n le (S n)) U lpt'). split; try split.
          - apply unuse_lemma_9_1 with n (repeat E_Lib (S n))
                                             (map (fun p => set_from_list (first_n le (S (fst p))) U (snd p))
                                                  (zip_with_ind llpt)); trivial.
            + apply repeat_length.
            + rewrite map_length. rewrite zip_with_ind_length. trivial.
            + destruct llpt; inversion hd_llpt. subst s.
              simpl. f_equal. destruct le; inversion hd_le. subst e1. 
              replace (first_n (e :: le) 1) with (e :: nil) by (destruct le; reflexivity). 
              symmetry. rewrite union_comm. apply union_include.
              unfold subset. unfold E.Included. intros. simpl in H8. destruct H8; inversion H8.
              subst x. apply H6.
            + apply last_repeat.
            + remember (n, lpt') as p.
              replace n with (fst p) by (rewrite Heqp; reflexivity).
              replace lpt' with (snd p) by (rewrite Heqp; reflexivity).
              apply last_error_map with (a := p).
              rewrite Heqp. apply last_error_zip_with_ind; trivial.
            + intros. destruct n. inversion H8.
              assert (exists lpt_m, nth_error llpt m = Some lpt_m).
              { apply nth_error_better_Some. rewrite len_llpt. apply le_S. apply H8. }
              assert (exists lpt_Sm, nth_error llpt (S m) = Some lpt_Sm).
              { apply nth_error_better_Some. rewrite len_llpt. apply le_n_S. apply H8. }
              destruct H13 as [lpt_m Hlpt_m]. destruct H14 as [lpt_Sm Hlpt_Sm].
              replace lpt with (set_from_list (first_n le (S m)) U lpt_m).
              replace lpt1 with (set_from_list (first_n le (S (S m))) U lpt_Sm).
              replace e1 with E_Lib. replace e2 with E_Lib.
              * apply H7; trivial. 
              * symmetry. apply repeat_spec with (S (S n)). apply nth_error_In with (S m). trivial.
              * symmetry. apply repeat_spec with (S (S n)). apply nth_error_In with m. trivial.
              * apply nth_error_zip_with_ind in Hlpt_Sm.
                apply nth_error_map with (f := (fun p => set_from_list (first_n le (S (fst p))) U snd p)) in Hlpt_Sm.
                assert (Some (set_from_list (first_n le (S (S m))) U lpt_Sm) = Some lpt1).
                { rewrite <- H12. symmetry. apply Hlpt_Sm. }
                inversion H13. trivial.
              * apply nth_error_zip_with_ind in Hlpt_m.
                apply nth_error_map with (f := (fun p => set_from_list (first_n le (S (fst p))) U snd p)) in Hlpt_m.
                assert (Some (set_from_list (first_n le (S m)) U lpt_m) = Some lpt).
                { rewrite <- H10. symmetry. apply Hlpt_m. }
                inversion H13. trivial.
          - unfold subset. unfold E.Included. intros. apply union_intror. assumption.
          - rewrite <- len_le. rewrite first_n_length. apply union_introl. apply In_list_set_In_list.
            apply last_error_In. apply last_le. }
        destruct H7 as [lpt''' [AVE_red''' [sub_lpt'_lpt''' in_e_lpt''']]].
        exists lpt'''. split; trivial.
        apply Rel_Lpt with e'; trivial.
        rewrite (union_include lpt'); trivial.
        rewrite union_comm. apply lemma5. trivial.
      * symmetry in H10. contradiction.
Qed.