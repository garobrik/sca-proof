(* Test *)

Require Import Lists.List.
Require Import Arith.EqNat.
Require Import Maps.

Definition method := id.

(*
Inductive lib : Type := .
Inductive app : Type := .

Inductive class (T : Type) : Type :=
| Obj : class lib
| Lib_Clazz : class lib -> list method ->  class lib
| Ext_Lib : class lib -> list method -> class app
| Ext_App : class app -> list method -> class app.

Inductive app_class : Type :=
| Ext_Lib : lib_class -> list method -> app_class
| Ext_App : app_class -> list method -> app_class.
 *)

(** Definition of class objects which contain their parent class,
    and class table which just says whether class is in app.
 *)
Module Rec.

  Inductive class : Type :=
  | Obj : class
  | C : class -> list method -> class.

  Inductive class_table : Type :=
  | CT : (class -> Prop) -> class_table.

  Definition in_app (ct : class_table) (c : class) : Prop :=
    match ct with
    | CT f => f c
    end.

End Rec.

Module ParId.

  Inductive class : Type :=
  | Obj : class
  | C : id -> list method -> class.

  Definition class_table : Type := partial_map class * partial_map class.

  Definition extends_id (ct : class_table) (i : id) (d : class) : Prop :=
    match ct with (app, lib) => app i = Some d \/ lib i = Some d end.

  Definition extends (ct : class_table) (c d : class) : Prop :=
    match c with
    | Obj => False
    | C i _ => extends_id ct i d
    end.


  Definition in_lib_id (ct : class_table) (i : id) : Prop :=
    match ct with (_, lib) => lib i <> None end.

  Definition in_app_id (ct : class_table) (i : id) : Prop :=
    match ct with (app, _) => app i <> None end.

  Definition in_table_id (ct : class_table) (i : id) : Prop :=
    in_lib_id ct i \/ in_app_id ct i.

  Definition in_lib (ct : class_table) (c : class) : Prop :=
    match c with
    | Obj => True
    | C i _ => in_lib_id ct i
    end.
  Definition in_app (ct : class_table) (c : class) : Prop :=
    match c with
    | Obj => False
    | C i _ => in_app_id ct i
    end.
  Definition in_table (ct : class_table) (c : class) : Prop :=
    match c with
    | Obj => True
    | C i _ => in_table_id ct i
    end.
  Lemma in_table_app_or_lib : forall (ct : class_table) (c : class),
      in_table ct c <-> in_lib ct c \/ in_app ct c.
  Proof.
    intros. destruct c.
    - simpl. split. auto. auto. 
    - unfold in_table, in_lib, in_app. unfold in_table_id. reflexivity.
  Qed.
  Lemma in_app_in_table : forall (ct : class_table) (c : class),
      in_app ct c -> in_table ct c.
  Proof. intros. rewrite in_table_app_or_lib. right. apply H. Qed.
  Lemma in_lib_in_table : forall (ct : class_table) (c : class),
      in_lib ct c -> in_table ct c.
  Proof. intros. rewrite in_table_app_or_lib. left. apply H. Qed.
  
  Inductive valid_class (ct : class_table) : class -> Type :=
  | ValidObj : valid_class ct Obj
  | ValidParent : forall i ms d,
      valid_class ct d -> extends ct (C i ms) d ->
      ~ (in_lib ct (C i ms) /\ in_app ct (C i ms)) ->
      (in_lib ct d /\ in_table ct (C i ms)) \/ (in_app ct d /\ in_app ct (C i ms))  ->
      valid_class ct (C i ms).
        

  Definition valid_table (ct : class_table) : Type :=
    forall c, in_table ct c -> valid_class ct c.

  Lemma extends_injective : forall ct c d d',
      valid_class ct c -> extends ct c d -> extends ct c d' -> d = d'.
  Proof.
    intros ct c d d' pfc c_ext_d c_ext_d'.
    unfold extends in c_ext_d, c_ext_d'. destruct c as [| i ms].
    - inversion c_ext_d.
    - unfold extends_id in c_ext_d, c_ext_d'. remember ct as ct'. destruct ct' as [app lib]. inversion pfc.
      destruct c_ext_d as [d_in_app | d_in_lib], c_ext_d' as [d'_in_app | d'_in_lib].
      + rewrite d_in_app in d'_in_app. inversion d'_in_app. reflexivity.
      + assert (in_lib (app, lib) (C i ms)) as c_in_lib.
        { unfold in_lib, in_lib_id, not. intros. rewrite d'_in_lib in H5. inversion H5. }
        assert (in_app (app, lib) (C i ms)) as c_in_app.
        { unfold in_app, in_app_id, not. intros. rewrite d_in_app in H5. inversion H5. }
        unfold not in H3. assert False. apply H3. split. apply c_in_lib. apply c_in_app. inversion H5.
      + assert (in_lib (app, lib) (C i ms)) as c_in_lib.
        { unfold in_lib, in_lib_id, not. intros. rewrite d_in_lib in H5. inversion H5. }
        assert (in_app (app, lib) (C i ms)) as c_in_app.
        { unfold in_app, in_app_id, not. intros. rewrite d'_in_app in H5. inversion H5. }
        unfold not in H3. assert False. apply H3. split. apply c_in_lib. apply c_in_app. inversion H5.
      + rewrite d_in_lib in d'_in_lib. inversion d'_in_lib. reflexivity.
  Qed.
        

  Fixpoint mresolve (ct : class_table) (m : method) (c : class) (pfc : valid_class ct c) : option class :=
    match pfc with
    | ValidObj _ => None
    | ValidParent _ _ ms d pfd _ _ _  => if (existsb (fun m' => beq_id m m') ms)
                                        then Some c
                                        else mresolve ct m d pfd
    end.

  Lemma mres_lib_in_lib : forall (ct : class_table) (m : method) (c e : class) (pfc : valid_class ct c),
      in_lib ct c -> mresolve ct m c pfc = Some e -> in_lib ct e.
    admit.
  Admitted.
  Lemma lemma1 : forall (ct : class_table) (c e : class) (m : method) (pfc : valid_class ct c),
      mresolve ct m c pfc = Some e -> in_app ct e -> in_app ct c.
  Proof.
    intros. induction pfc.
    - unfold mresolve in H. inversion H.
    - unfold mresolve in H. destruct (existsb (fun m' : id => beq_id m m') ms) in H.
      + inversion H. rewrite H2. apply H0.
      + fold mresolve in H. apply IHpfc in H. destruct o.
        * inversion pfc.
          -- rewrite <- H2 in H. unfold in_app in H. inversion H.
          -- rewrite H6 in H4. destruct H4. split. destruct H1. apply H1. apply H.
        * destruct H1. apply H2.
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
    intros. inversion H. rewrite in_table_app_or_lib in H0. destruct H0.
    - apply H0.
    - apply H2 in H0. unfold valid_table in X.
      assert (in_table ct c). { apply in_app_in_table. apply H0. }
      apply X in H5. inversion H5.
      + rewrite <- H6 in H0. inversion H0.
      + rewrite H10 in H8. destruct H8. split. apply H1. apply H0.
  Qed.

  (*Lemma ext_in_ct_ext_in_ct' : forall (ct ct' : class_table) (c d : class),
      ave_rel ct ct' -> in_table ct c -> in_table ct' c -> extends ct c d -> extends ct' c d.
  Proof.
    intros ct ct' c d ave cin cin' ext.*)
    
    

  Lemma lemma2 : forall (ct ct' : class_table) (c e e' : class) (m : method) (pfc : valid_class ct c) (pfc' : valid_class ct' c),
      in_app ct c -> mresolve ct m c pfc = Some e -> mresolve ct' m c pfc' = Some e'  -> ave_rel ct ct' ->
      in_app ct e \/ in_lib ct' e'.
Proof.
  intros ct ct' c e e' m pfc pfc' c_in_app c_res_e c_res_e' rel.
  induction pfc as [| i ms d pfd IHd c_ext_d not_lib_app app_ext_app].
  (* c is Obj *)
  - unfold mresolve in c_res_e. inversion c_res_e.
  (* c extends d *)
  - unfold mresolve in c_res_e. fold mresolve in c_res_e.
    destruct (existsb (fun m' : id => beq_id m m') ms) eqn:m_res.
    (* m-res *)
    + inversion c_res_e. left. apply c_in_app.
    (* m-res-inh *)
    + inversion rel as [ct_val ct'_val keep_app keep_ext keep_lib].
      remember (C i ms) as c. unfold mresolve in c_res_e'.
      (* can't induct on pfc and pfc' simultaneously, so manually destruct pfc' and show that it's the same d *)
      destruct pfc' as [_ | i0 ms0 d0 pfd' c_ext_d'] eqn:pfc''.
      * inversion c_res_e'.
      * fold mresolve in c_res_e'. inversion Heqc.
        rewrite H1 in c_res_e'. rewrite m_res in c_res_e'.
        assert (d = d0) as deq.
        { apply extends_injective with (ct := ct') (c := (C i0 ms0)).
          -- apply pfc'.
          -- apply keep_ext.
             ++ apply c_ext_d.
             ++ apply in_app_in_table. apply keep_app. apply c_in_app.
          -- apply c_ext_d'. }
        destruct app_ext_app as [[d_in_lib _] | [d_in_app _]].
        (* d in lib - use averroes transformation properties *)
        -- right. apply mres_lib_in_lib with (m := m) (c := d0) (pfc := pfd').
           ++ apply keep_lib with (c := (C i0 ms0)).
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
         
       
End ParId.

Module ParC.

  Inductive class : Type :=
  | Obj : class
  | C : class -> list method -> class.

  (** application classes * library classes  *)
  Definition class_table : Type := list class * list class.

  Definition in_table (ct : class_table) (c : class) : Prop :=
    match ct with (app, lib) => In c app \/ In c lib end.

  Definition in_app (ct : class_table) (c : class) : Prop :=
    match ct with (app, _) => In c app end.

  Definition in_lib (ct : class_table) (c : class) : Prop :=
    match ct with (_, lib) => In c lib end.

  Inductive valid_class (ct : class_table) : class -> Type :=
  | ValidObj : valid_class ct Obj
  | ValidParent : forall c ms,
      valid_class ct c ->
      ~ (in_lib ct (C c ms) /\ in_app ct (C c ms)) ->
      (in_lib ct c /\ in_table ct (C c ms)) \/ (in_app ct c /\ in_app ct (C c ms))  ->
      valid_class ct (C c ms).

  Definition extends (c d : class) : Prop :=
    match c with
    | Obj => False
    | C c' _ => c' = d
    end.

  Definition valid_table (ct : class_table) : Type :=
    match ct with
    | (app, lib) => forall c, in_table ct c -> valid_class ct c
    end.

  Fixpoint mresolve (m : method) (c : class) : option class :=
    match c with
    | Obj => None
    | C d ms => if (existsb (fun m' => beq_id m m') ms) then Some c else mresolve m d
    end.
  
  Lemma lemma1 : forall (ct : class_table) (pft : valid_table ct) (c e : class) (pfc : valid_class ct c) (pfe : valid_class ct e) (m : method),
      mresolve m c = Some e -> in_app ct e -> in_app ct c.
  Proof.
    intros. induction pfc.
    - unfold mresolve in H. inversion H.
    - unfold mresolve in H. destruct (existsb (fun m' : id => beq_id m m') ms) in H.
      + inversion H. rewrite H2. apply H0.
      + fold mresolve in H. apply IHpfc in H. destruct o.
        * destruct n. destruct H1. split. apply H1. apply H.
        * destruct H1. apply H2.
  Qed.
  
End ParC.
(*
Definition extends (c d : class) : Prop :=
  match c with
  | Obj => False
  | C d' ms => d' = d
  end.

Definition parent (c : class) : class :=
  match c with
  | Obj => Obj
  | C d _ => d
  end.
*)
Axiom obj_in_lib : forall (ct : class_table), ~ (in_app ct Obj).

Axiom no_lib_ext_app : forall (ct : class_table) (c : class) (ms : list method),
    in_app ct c -> in_app ct (C c ms).

Module NonInductive.
  Fixpoint mresolve (ct : class_table) (m : method) (c : class) : class :=
    match c with
    | Obj => Obj
    | C d ms => if (existsb (fun m' => beq_id m m') ms) then c else mresolve ct m d
    end.
  
  Lemma lemma1 : forall (ct : class_table) (c : class) (m : method),
      in_app ct (mresolve ct m c) -> in_app ct c.
  Proof.
    intros. induction c as [| d ms].
    - simpl in H. apply obj_in_lib in H. inversion H.
    - simpl in H. destruct (existsb (fun m' : id => beq_id m m') l) in H.
      + apply H.
      + apply ms in H. apply no_lib_ext_app. apply H.
  Qed.
  
End NonInductive.

Module Induct.
  Inductive mresolve (ct : class_table) : method -> class -> class -> Prop :=
  | Mres : forall (m : method) (c : class) (ms : list method),
      In m ms -> mresolve ct m (C c ms) (C c ms)
  | Mres_Inh : forall (m : method) (c d : class) (ms : list method),
      ~ In m ms -> mresolve ct m c d -> mresolve ct m (C c ms) d.

  Lemma lemma1 : forall (ct : class_table) (c d : class) (m : method),
      mresolve ct m c d -> in_app ct d -> in_app ct c.
  Proof.
    intros. induction H.
    - (* Mres *) apply H0.
    - (* Mres-Inh *) apply no_lib_ext_app. auto. 
  Qed.
End Induct.

Module InductOpt.
  Inductive mresolve (ct : class_table) : method -> class -> option class -> Prop :=
  | M_Res_None : forall (m : method), mresolve ct m Obj None
  | M_Res : forall (m : method) (c : class) (ms : list method),
    In m ms -> mresolve ct m (C c ms) (Some (C c ms))
  | M_Res_Inh : forall (m : method) (c : class) (d : option class) (ms : list method),
    ~ In m ms -> mresolve ct m c d -> mresolve ct m (C c ms) d.

Lemma lemma1 : forall (ct : class_table) (c d : class) (m : method),
    mresolve ct m c (Some d) -> in_app ct d -> in_app ct c.
Proof.
  intros. remember (Some d) as sd. induction H.
  - (* Obj *) inversion Heqsd.
  - (* Mres *) inversion Heqsd. rewrite <- H2 in H0. apply H0.
  - (* Mres-Inh *) apply IHmresolve in Heqsd. apply no_lib_ext_app. apply Heqsd.
Qed.
End InductOpt.