Require Export Coq.Init.Datatypes.
Require Export Coq.Lists.List.
Require Export Arith.EqNat.
Require Export Program.Equality.
Require Export Coq.Logic.ProofIrrelevance.

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

  Set Implicit Arguments.
  Inductive Forallt (A : Type) (P : A -> Type) : list A -> Type :=
    Forallt_nil : Forallt P nil
  | Forallt_cons : forall (x : A) (l : list A), P x -> Forallt P l -> Forallt P (x :: l).
  Unset Implicit Arguments.

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
  Proof. induction l; intros; inversion H0; inversion H; subst; eauto. Qed.

  Theorem Forall_repeat : forall (A : Type) (P : A -> Prop) (n : nat) (a : A),
      P a -> Forall P (repeat a n).
  Proof.
    intros. induction n.
    - apply Forall_nil.
    - apply Forall_cons; assumption.
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
      n < length l <-> exists a, nth_error l n = Some a.
  Proof.
    split.
    - intros. assert (nth_error l n <> None) by (apply nth_error_Some; trivial).
      destruct (nth_error l n) eqn:ntherr.
      + exists a. reflexivity.
      + destruct H0; reflexivity.
    - intros. apply (nth_error_Some). intro. destruct H. rewrite H in H0. inversion H0.
  Qed.

  Lemma index_of_existsb : forall {A : Type} (f : A -> bool) (l : list A),
      (exists n, index_of f l = Some n) <-> existsb f l = true.
  Proof.
    intros. induction l.
    - simpl. split; intros; inversion H. inversion H0.
    - simpl. destruct (f a) eqn:fa; simpl.
      + split; intros; try (exists 0); reflexivity.
      + rewrite <- IHl. split; intros; destruct H as [n Hn].
        * exists (pred n). destruct (index_of f l); inversion Hn. reflexivity.
        * exists (S n). rewrite Hn. reflexivity.
  Qed.

  Lemma index_of_In : forall {A : Type} (l : list A) (f : A -> bool) (a : A),
      (forall b, f b = true <-> a = b) -> ((exists n, index_of f l = Some n) <-> In a l).
  Proof.
    induction l; split; intros; simpl; try solve [inversion H0].
    - inversion H0. inversion H1.
    - destruct H0 as [n Hn]. inversion Hn. destruct (f a) eqn:fa.
      + apply H in fa. subst. left. reflexivity.
      + right. specialize (IHl f a0 H). apply IHl. exists (pred n).
        destruct (index_of f l).
        * simpl in H1. injection H1 as H2. rewrite <- H2. reflexivity.
        * inversion H1.
    - destruct (f a) eqn:fa.
      + exists 0. reflexivity.
      + inversion H0.
        * symmetry in H1. apply H in H1. rewrite H1 in fa. inversion fa.
        * specialize (IHl f a0 H). apply IHl in H1. destruct H1 as [n Hn].
          rewrite Hn. simpl. exists (S n). reflexivity.
  Qed.

  Lemma nth_error_combine : forall {A} l l' n (a a' : A),
      nth_error l n = Some a -> nth_error l' n = Some a' ->
      nth_error (combine l l') n = Some (a, a').
  Proof.
    induction l; intros; try solve [destruct n; inversion H].
    destruct n.
    + destruct l'; inversion H0. inversion H. reflexivity.
    + destruct l'; try solve [inversion H0]. simpl in H. simpl in H0. simpl.
      apply IHl; assumption.
  Qed.

  Lemma index_of_length : forall A (f : A -> bool) l n,
      index_of f l = Some n -> n < length l.
  Proof.
    induction l; intros; try inversion H.
    destruct (f a) eqn:fa.
    - inversion H1. simpl. apply le_n_S. apply le_0_n.
    - destruct (index_of f l) as [m|]; try solve [inversion H1].
      simpl in H1. inversion H1. simpl. apply Lt.lt_n_S. apply IHl. reflexivity.
  Qed.

  Lemma nth_error_repeat : forall A n m (a : A),
      n < m -> nth_error (repeat a m) n = Some a.
  Proof.
    intros. generalize dependent n. induction m; intros.
    - inversion H.
    - destruct n; try reflexivity.
      apply Lt.lt_S_n in H. simpl. apply IHm. assumption.
  Qed.

  Lemma subset_trans : forall {A} (s : set A) s' s'',
      subset s s' -> subset s' s'' -> subset s s''.
  Proof. intros A s s' s'' H H0 a a_in_s. apply H0, H, a_in_s. Qed.

  Lemma existsb_find : forall {A} (P : A -> bool) (l : list A),
      existsb P l = true <-> (exists a, find P l = Some a).
  Proof.
    induction l; (split; intros; [| destruct H]; inversion H).
    - destruct (P a) eqn:Pa; simpl; rewrite Pa.
      + eexists. reflexivity.
      + apply IHl. assumption.
    - destruct (P a) eqn:Pa; simpl; rewrite Pa.
      + reflexivity.
      + apply IHl. eexists. eassumption.
  Qed.

End generic_thms.
