Require Import proof.

Lemma RA'_trans : forall ct' e lpt e' lpt' e'' lpt'',
    AVE_reduce' ct' e lpt e' lpt' ->
    AVE_reduce' ct' e' lpt' e'' lpt'' ->
    AVE_reduce' ct' e lpt e'' lpt''.
Proof.
  intros. induction H; eauto.
Qed.
Hint Resolve RA'_trans.

Lemma lemma8' : forall (ct' : class_table) (e e' : expr) (lpt lpt' : set expr),
    AVE_reduce' ct' e lpt e' lpt' -> subset lpt lpt'.
Proof.
  intros. induction H.
  - intros x H. assumption.
  - apply lemma8 in H. eapply subset_trans; eassumption.
Qed.
Hint Resolve lemma8'.

Lemma RAC'_Field : forall ct' e e' lpt lpt' fi,
    AVE_reduce' ct' e lpt e' lpt' -> AVE_reduce' ct' (E_Field e fi) lpt (E_Field e' fi) (lpt' U lpt).
Proof.
  intros.
  induction H.
  - rewrite union_same. apply RA'_refl.
  - eapply RA'_step; eauto.
    repeat erewrite <- union_include; eauto.
    erewrite <- union_include in IHAVE_reduce'; eauto.
    Unshelve. assumption. assumption. assumption. assumption. assumption. assumption. 
Qed.
Hint Resolve RAC'_Field.

Lemma RAC'_Invk_Recv : forall {ct e e'} mi le {lpt lpt'},
    AVE_reduce' ct e lpt e' lpt' -> AVE_reduce' ct (E_Invk e mi le) lpt (E_Invk e' mi le) (lpt' U lpt).
Proof.
  intros. induction H; try (rewrite union_same; constructor).
  eapply RA'_step. eapply RAC_Invk_Recv. eassumption.
  repeat erewrite <- union_include; eauto.
  erewrite <- union_include in IHAVE_reduce'; eauto.
    Unshelve. assumption. assumption. assumption. assumption. assumption. assumption. 
Qed.
Hint Resolve RAC'_Invk_Recv.

Inductive not_derived_by_rel_lpt {ct ct' gamma} : forall {e e' lpt}, alpha ct ct' gamma e e' lpt -> Prop :=
  N_Rel_Field : forall {e e' : expr} {f : field_id} {lpt : set expr} pf,
    not_derived_by_rel_lpt (Rel_Field ct ct' gamma e e' f lpt pf)
| N_Rel_Lib_Field : forall {e : expr} {c : class} {pfc : valid_class ct c} {di : class_id} 
                    {f : field_id} {lpt : set expr} pf1 pf2 pf3 pf4,
    not_derived_by_rel_lpt (Rel_Lib_Field ct ct' gamma e c pfc di f lpt pf1 pf2 pf3 pf4)
| N_Rel_New : forall {ci : class_id} {le le' : list expr} {lpt : set expr} pf1 pf2 pf3,
    not_derived_by_rel_lpt (Rel_New ct ct' gamma ci le le' lpt pf1 pf2 pf3)
| N_Rel_Lib_New : forall {ci : class_id} {le : list expr} {lpt : set expr} pf1 pf2,
    not_derived_by_rel_lpt (Rel_Lib_New ct ct' gamma ci le lpt pf1 pf2)
| N_Rel_Invk : forall {e e' : expr} {le le' : list expr} {mi : method_id} {lpt : set expr} pf1 pf2 pf3,
    not_derived_by_rel_lpt (Rel_Invk ct ct' gamma e e' le le' mi lpt pf1 pf2 pf3)
| N_Rel_Lib_Invk : forall {e : expr} {le : list expr} {mi : method_id} {lpt : set expr} pf1 pf2 pf3,
    not_derived_by_rel_lpt (Rel_Lib_Invk ct ct' gamma e le mi lpt pf1 pf2 pf3)
| N_Rel_Cast : forall {e e' : expr} {c : class_id} {lpt : set expr} pf1,
    not_derived_by_rel_lpt (Rel_Cast ct ct' gamma e e' c lpt pf1)
| N_Rel_Lib_Cast : forall {e : expr} {ci : class_id} {lpt : set expr} pf1,
    not_derived_by_rel_lpt (Rel_Lib_Cast ct ct' gamma e ci lpt pf1).

Lemma lemma6 : forall {ct ct' gamma e eh lpt},
    alpha ct ct' gamma e eh lpt -> calP ct' gamma eh lpt -> exists yh,
        (exists rel : alpha ct ct' gamma e yh lpt, not_derived_by_rel_lpt rel) /\
        AVE_reduce' ct' eh lpt yh lpt.
Proof.
  intros ct ct' gamma e eh lpt H H0.
  induction H.
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Field H).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Lib_Field H H1 H2 H3).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_New H H1 H2).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Lib_New H H1).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Invk H H1 H2).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Lib_Invk H H1 H2).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Cast H).
  - eexists. split; try apply RA'_refl. eexists. apply (N_Rel_Lib_Cast H).
  - destruct H0 as [_ calPlpt]. apply calPlpt in H1 as calPe'.
    destruct (IHalpha (conj calPe' calPlpt)) as [dh [[rel not_lpt] red]].
    eexists. split. eexists. eassumption.
    eapply RA'_step; try eassumption.
    apply RA_Return. assumption.
Qed.

Lemma decl_in_lib_ct_decl_in_lib_ct'_h : forall {ct ct'} (rel : ave_rel ct ct') {c} pfc (pfc' : valid_class ct' c) fi di,
    declaring_class ct c pfc fi = Some di -> in_lib_id ct di -> pfc' = pfc' ->
    in_lib_id ct' di.
Proof.
  intros ct ct' rel c pfc pfc'.
  apply simul_induct with (ct := ct) (ct' := ct') (c := c) (pfc := pfc) (pfc' := pfc');
    try assumption; clear c pfc pfc'; intros; try solve [inversion H].
  inversion H0.
  destruct (@existsb field_id (beq_nat fi) (dfields c)) eqn:exstb;
    try (eapply H; try eassumption; reflexivity).
  inversion H4. subst. destruct ct' as (app', lib'). exists c.
  inversion rel as [val_ct _ keep_app _ _]. apply in_lib_id_in_lib in H1 as c_in_lib; try assumption.
  Focus 2. inversion sca as [[_ sol]|[_ sol]]; [ | apply in_app_in_table]; assumption.
  assert (pfc' := ValidParent (app', lib') c d pfd' ext' nla' sca').
  assert (in_table (app', lib') c) by (apply valid_in_table; assumption).
  destruct H3; try assumption.
  apply keep_app in H3. destruct nla; split; assumption.
Qed.

Lemma decl_in_lib_ct_decl_in_lib_ct' : forall {ct ct'} (rel : ave_rel ct ct') {c} pfc (pfc' : valid_class ct' c) fi di,
    declaring_class ct c pfc fi = Some di -> in_lib_id ct di -> 
    in_lib_id ct' di.
Proof.
  intros. eapply decl_in_lib_ct_decl_in_lib_ct'_h with (pfc'0 := pfc'); try reflexivity; eassumption.
Qed.
Hint Resolve decl_in_lib_ct_decl_in_lib_ct'.

Lemma calPadd : forall ct' gamma e ea lpt,
    calP ct' gamma e lpt -> calPexpr ct' gamma ea -> calP ct' gamma e (add ea lpt).
Proof.
  intros. inversion H as [calPe calPlpt].
  split; try assumption.
  intros. destruct H1; auto.
  inversion H1. subst. assumption.
Qed.
Hint Resolve calPadd.

Lemma find_method_mresolve_h : forall l mi,
    existsb (fun a => beq_nat mi match a with Method _ id _ _ => id end) l =
    existsb (fun a => match a with Method _ id _ _ => beq_nat mi id end) l.
Proof.
  induction l; try reflexivity.
  intros. simpl. destruct a. rewrite IHl. reflexivity.
Qed.

Lemma find_method_mresolve : forall {ct c} pfc mi,
    (exists m, find_method mi pfc = Some m) <-> (exists p, mresolve ct mi c pfc = Some p).
Proof.
  induction pfc; (split; intros; [destruct H as [m Hm]; inversion Hm | destruct H as [p Hp]; inversion Hp]).
  - destruct (lookup_method c mi) eqn:find_method.
    + inversion H0; subst.
      exists c. simpl. unfold lookup_method in find_method. destruct c; try solve [inversion e].
      unfold dmethods_id. rewrite existsb_map.
      assert (existsb (fun a => PeanoNat.Nat.eqb mi (mid a)) (dmethods (C c c0 l c1 l0)) = true).
      { rewrite find_method_mresolve_h. apply existsb_find. eexists; eassumption. }
      rewrite H. reflexivity.
    + simpl. unfold lookup_method in find_method. destruct c; try solve [inversion e].
      assert (~ exists m, find (fun m : method => match m with
                                        | Method _ mi' _ _ => PeanoNat.Nat.eqb mi mi'
                                          end) l0 = Some m).
      { intro. destruct H. rewrite find_method in H. inversion H. }
      eapply not_iff in H. Focus 2. apply existsb_find.
      apply Bool.not_true_is_false in H.
      unfold dmethods_id. rewrite existsb_map. simpl. rewrite find_method_mresolve_h. rewrite H.
      apply IHpfc. simpl in Hm. rewrite find_method in Hm. eexists. eassumption.
  - destruct c; try solve [inversion e].
    destruct (existsb (beq_nat mi) (dmethods_id (C c c0 l c1 l0))) eqn:exstb; simpl in exstb; 
      unfold dmethods_id in exstb; simpl; rewrite existsb_map, find_method_mresolve_h in exstb.
    + apply existsb_find in exstb. destruct exstb as [m Hm]. simpl in Hm. rewrite Hm. eexists. reflexivity.
    + rewrite <- Bool.not_true_iff_false in exstb. eapply not_iff in exstb. Focus 2. symmetry. apply existsb_find.
      apply not_exists_some_iff_none in exstb. simpl in exstb. rewrite exstb. apply IHpfc. eexists. eassumption.
Qed.
Hint Resolve find_method_mresolve.

Ltac try_invert :=
  try match goal with
      | [ H : _ |- _ ] => try solve [inversion H]
      end.

Lemma mresolve_valid : forall {ct c} pfc mi e,
    mresolve ct mi c pfc = Some e -> valid_class ct e.
Proof.
  induction pfc; intros; try_invert.
  simpl in H. destruct (existsb (beq_nat mi) (dmethods_id c)); inversion H; subst; eauto.
Qed.
Hint Resolve mresolve_valid.

Lemma find_method_ct_ct' : forall {ct ct'} (rel : ave_rel ct ct') {c}
                             (pfc : valid_class ct c) (pfc' : valid_class ct' c) mi,
    find_method mi pfc = find_method mi pfc'.
Proof.
  intros ct ct' rel c pfc pfc'.
  apply simul_induct with (ct := ct) (ct' := ct') (c := c) (pfc := pfc) (pfc' := pfc'); trivial.
  clear c pfc pfc'.
  intros. simpl. destruct (lookup_method c mi); auto.
Qed.
Hint Resolve find_method_ct_ct'.

Lemma combine_step : forall {A B} la lb (a : A) (b : B),
    (a, b) :: combine la lb = combine (a :: la) (b :: lb).
Proof. reflexivity. Qed.
Hint Resolve combine_step.

Lemma subtype_in_table : forall ct c d,
    subtype ct c d -> in_table ct c.
Proof. intros. induction H; eauto. Qed.
Hint Resolve subtype_in_table.

Lemma supertype_in_table : forall ct c d,
    valid_table ct -> subtype ct c d -> in_table ct d.
Proof. intros ct c d val_ct sub_c_d. inversion val_ct. induction sub_c_d; eauto. Qed.
Hint Resolve supertype_in_table.

Lemma subtype_ct_ct' : forall {ct ct'} c d,
    ave_rel ct ct' -> in_table ct' c -> subtype ct c d -> subtype ct' c d.
Proof with eauto.
  intros ct ct' c d rel_ct c_in_ct' c_sub_d. inversion rel_ct as [_ val_ct' _ keep_ext _].
  induction c_sub_d; eauto.
  - specialize (IHc_sub_d1 c_in_ct').
    assert (in_table ct' d)...
  - constructor; eauto. apply keep_ext; split; eauto.
Qed.
Hint Resolve subtype_ct_ct'.

Axiom preservation : forall ct gamma e e' ci,
    type_of ct gamma e ci -> FJ_reduce' ct e e' -> type_of ct gamma e' ci.
Hint Resolve preservation.


Lemma in_dmethods_mresolve : forall ct c pfc m,
    In m (dmethods c) -> mresolve ct (mid m) c pfc = Some c.
Proof with eauto.
  intros. destruct pfc; [inversion H|].
  simpl. unfold dmethods_id. rewrite existsb_map.
  replace (existsb (fun a : method => PeanoNat.Nat.eqb (mid m) (mid a)) (dmethods c)) with true...
  symmetry. eapply existsb_exists. split_rec 2; eauto. symmetry. apply beq_nat_refl.
Qed.
Hint Resolve in_dmethods_mresolve.

Lemma valid_calP : forall ct' gamma e,
    valid_expr ct' gamma e -> calPexpr ct' gamma e.
Proof.
  intros. induction H using valid_expr_ind_list; decomp; try inversion H; eauto.
Qed.
Hint Resolve valid_calP.

Lemma FJ_reduce_valid : forall ct gamma e e',
    valid_expr ct gamma e ->
    FJ_reduce ct e e' ->
    valid_expr ct gamma e'.
Proof.
  intros ct gamma e e' val_e H.
  induction H; inversion val_e; subst; eauto.
  - inversion H7; subst. eapply Forall_In; try eassumption; eauto.
  - inversion val_e; subst. inversion H9; subst. eauto.


Lemma calPrel : forall ct' gamma e e' lpt lpt',
    valid_table ct' ->
    AVE_reduce ct' e lpt e' lpt' ->
    valid_expr ct' gamma e ->
    calP ct' gamma e lpt ->
    calP ct' gamma e' lpt'.
Proof.
  intros ct' gamma e e' lpt lpt' val_ct' H val_e.
  induction H; eauto; intros; try solve [inverts 2; eauto].
  - split; eauto. inversion H2; inversion H3; inversion val_e; inversion H11; eauto. subst.
    apply In_set_from_list_In_list in H5. apply valid_calP. eapply Forall_In; swap 1 2; eassumption.
  - admit. (*inversion val_e. inversion H8. eauto. *)
  - eapply IHAVE_reduce; eauto.

Lemma lemma11 : forall ct ct' gamma e0 e e' eh lpt,
    ave_rel ct ct' -> FJ_reduce' ct e0 e -> FJ_reduce ct e e' ->
    alpha ct ct' gamma e eh lpt -> calP ct' gamma eh lpt ->
    type_checks ct gamma e0 -> fj_expr e0 -> valid_expr ct gamma e -> fj_expr e ->
    exists eh' lpt', AVE_reduce' ct' eh lpt eh' lpt' /\ alpha ct ct' gamma e' eh' lpt' /\ calP ct' gamma eh' lpt'.
Proof with eauto.
  intros ct ct' gamma e0 e e' eh lpt rel_ct red_e0_e red_e_e' rel_e_eh calPehlpt
         typ_chk_e0 fj_expr_e0 val_e fj_expr_e.
  generalize dependent eh. generalize dependent e0.
  inversion rel_ct as [val_ct val_ct' keep_app _ _].
  inversion val_ct as [ct0 in_table_valid _ one_cid id_in_one one_fid _]; subst ct0.
  inversion val_ct' as [ct0 in_table_valid' _ _ _ _ _]; subst ct0.
  induction red_e_e'; intros; dependent induction rel_e_eh;
    try solve [destruct calPehlpt; eapply IHrel_e_eh in rel_ct; try reflexivity; eauto;
               decomp; split_rec 4; try eassumption; eauto]; try clear IHrel_e_eh.


  (* Case R_Field *)

    (* Subcase Rel_Field *)
    - assert (In fi (field_ids ct c pfc)) as In_fields.
      { assert (forall fi', (beq_nat fi) fi' = true <-> fi = fi').
        { split; try apply beq_nat_true. intro. subst. symmetry. apply beq_nat_refl. }
        eapply index_of_In. eassumption. eexists; eassumption. }
      apply In_fields_decl_exists in In_fields. destruct In_fields as [chi declchi].
      apply valid_in_table in pfc as c_in_table. destruct c_in_table as [c_in_app | c_in_lib].

      (* if c is in CT_A *)
      + dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_New *)
        * assert (exists ehi, nth_error le' n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H0. apply nth_error_better_Some. eexists; eauto. }
           destruct exeh as [ehi Hehi].
           exists ehi. exists lpt. split.
           -- eapply RA'_step with ehi lpt; try eapply RA'_refl. apply RA_FJ.
              assert (valid_class ct' c) as pfc'...
              eapply R_Field with (pfc := pfc'); eauto. rewrite <- (field_ids_same pfc); trivial.
           -- inversion calPehlpt as [calPeh calPlpt]. inversion calPeh. inversion H6.
              split; try split; try apply Forall_In with le'; try apply nth_error_In with n; try assumption.
              subst. apply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt)
                                            (l := combine le le')
                                            (a := (ei, ehi)); try assumption.
              apply nth_error_In with n. apply nth_error_combine; assumption.

        (* SubSubCase Rel_Lib_New, CONTRADICTION  *)
        * destruct (not_lib_app ct c); trivial; split; trivial.
           apply in_lib_id_in_lib; trivial. apply in_app_in_table; trivial.

        (* SubSubCase Rel_Lpt, Induction  *)
        * eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption.
           destruct IHspec as [eh' [lpt' [red_eh' [rel_eh' calP_eh']]]].
           exists eh'. exists lpt'. split; try split; try assumption.
           -- eapply RA'_trans; try eassumption.
              eapply RA'_step; try solve [econstructor].
              rewrite <- union_same. eapply RAC_Field.
              apply RA_Return. assumption.
           -- destruct calPehlpt as [_ calP_lpt].
              assert (valid_class ct' c) as pfc'.
              { apply in_table_valid', in_app_in_table, keep_app, c_in_app. }
              split; try assumption. eapply P_Field with (pfc' := pfc'); eauto.
              erewrite decl_ct'_decl_ct; eassumption.

      (* if c is in CT_L *)
      + dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_New *)
        * assert (exists ehi, nth_error le' n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H0. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           exists ehi. exists lpt. split; try split.
           -- apply RA'_step with ehi lpt; try apply RA'_refl. apply RA_FJ.
              assert (valid_class ct' c) as pfc'.
              { apply in_table_valid', in_lib_in_table, keep_id_keep_class with ct; assumption. }
              apply R_Field with pfc' n; trivial. rewrite <- (field_ids_same pfc); trivial.
           -- remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           -- eapply calPsub; try eassumption.
              eapply SUB_Trans.
              ++ apply SUB_New. eapply nth_error_In. eassumption.
              ++ eapply SUB_Field.

        (* SubSubCase Rel_Lib_New *)
        * apply decl_of_in_lib_in_lib in declchi as chi_in_lib; try assumption.
           assert (ch_in_lib := chi_in_lib).
           unfold in_lib_id in ch_in_lib. destruct ct as [app lib].
           destruct ch_in_lib as [ch Hch].
           assert (chi = id_of ch).
           { apply one_cid. simpl. destruct (app chi) eqn:appchi; try assumption.
             destruct (id_in_one chi). split; try assumption. simpl. exists c0. assumption. }
           subst. assert (valid_class (app, lib) ch) as pfch.
           { apply in_table_valid. apply in_lib_in_table. assumption. }
           inversion calPehlpt as [calPeh calPlpt]. inversion calPeh. subst.
           rename pfc' into pfc0'.
           assert (valid_class (app, lib) c0) as pfc0 by (apply valid_ct'_valid_ct with ct'; assumption).
           assert (declaring_class (app, lib) c0 pfc0 fi = Some di) by
               (rewrite <- decl_ct'_decl_ct with (ct' := ct') (pfc' := pfc0'); assumption).
           assert (di = (id_of ch)) by (apply one_fid with c0 pfc0 c pfc fi; assumption). subst.
           assert (valid_class ct' ch) as pfch'. 
           { apply in_table_valid'. apply in_table_in_table' with (app, lib); try assumption.
             - right. assumption.
             - apply decl_in_table with c0 pfc0' fi. assumption. }
           remember (E_New (id_of ch) (repeat E_Lib (length (fields ct' ch pfch')))) as ch_new.
           assert (in_lib ct' ch).
           { destruct (valid_in_table ct' ch pfch'); try assumption. 
             destruct (not_lib_app (app, lib) ch pfch). split... apply keep_app; assumption. }
           exists E_Lib. exists (add ch_new lpt).
           split; try split.
           ++ apply RA'_step with (E_Field E_Lib fi) (add ch_new lpt).
              { rewrite Heqch_new. apply RA_New. assumption. }
              apply RA'_step with (E_Field ch_new fi) (add ch_new lpt).
              { rewrite <- union_same. apply RAC_Field. apply RA_Return. right. reflexivity. }
              apply RA'_step with E_Lib (add ch_new lpt); try apply RA'_refl.
              apply RA_FJ. rewrite Heqch_new.
              apply decld_class_same_decl with (pfe := pfch') in H6 as decl_ch'; try assumption.
              apply decl_index_of in decl_ch' as fi_in_ch; try assumption.
              destruct fi_in_ch as [m Hm].
              apply R_Field with pfch' m; try assumption.
              apply nth_error_repeat. rewrite fields_field_ids_length.
              apply index_of_length with (beq_nat fi). assumption.
           ++ apply lemma5. eapply Forall_In with (P := fun e  => alpha (app, lib) ct' gamma e E_Lib lpt);
                              try eapply nth_error_In; eassumption.
           ++ split. apply P_Lib. intros. destruct H7.
              apply calPlpt. apply H7. inversion H7. subst x. rewrite Heqch_new.
              apply P_New. apply Forall_repeat. apply P_Lib.
              apply decl_in_table with c0 pfc0' fi. assumption.

        (* SubSubCase Rel_Lpt, CONTRADICTION  *)
        * eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption.
           destruct IHspec as [eh' [lpt' [red_eh' [rel_eh' calP_eh']]]].
           exists eh'. exists lpt'. split; try split; try assumption.
           -- eapply RA'_trans; try eassumption.
              eapply RA'_step; try solve [econstructor].
              rewrite <- union_same. eapply RAC_Field.
              apply RA_Return. assumption.
           -- destruct calPehlpt as [calPeh calP_lpt].
              split; try assumption. inversion calPeh. eapply P_Field; try eassumption; apply calP_lpt, H.

    (* Subcase Rel_Lib_Field *)
    - assert (In fi (field_ids ct c pfc)) as In_fields.
      { assert (forall fi', (beq_nat fi) fi' = true <-> fi = fi').
        { split; try apply beq_nat_true. intro. subst. symmetry. apply beq_nat_refl. }
        eapply index_of_In. eassumption. eexists; eassumption. }
      apply In_fields_decl_exists in In_fields. destruct In_fields as [chi declchi].
      assert (di = chi) by (eapply one_fid; eassumption). subst di.
      apply valid_in_table in pfc as c_in_table. destruct c_in_table as [c_in_app | c_in_lib].

      (* if c is in CT_A *)
      + dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_Lib_New, CONTRADICTION *)
        * destruct (not_lib_app ct c pfc). split; try assumption.
           apply in_lib_id_in_lib; try apply rel_ct; try apply in_app_in_table; assumption.

        (* SubSubCase Rel_Lpt, INDUCTION  *)
        * destruct e'; inversion rel_e_eh; subst;
             try solve [eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption].
           clear IHrel_e_eh.
           assert (exists ehi, nth_error l n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H11. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           assert (valid_class ct' c) as pfc'.
           { apply in_table_valid', in_app_in_table, keep_app. assumption. }
           eexists. eexists. split; try split.
           -- eapply RA'_step.
              { eapply RA_Field with (pfc := pfc'). erewrite decl_ct'_decl_ct. eapply declchi. assumption.
                eapply decl_in_lib_ct_decl_in_lib_ct' with (c1 := c); eassumption. }
              eapply RA'_step.
              { eapply RA_Return. right. reflexivity. }
              eapply RA'_step.
              { eapply RAC_Field. eapply RA_Return. left. eapply H. }
              rewrite union_same. eapply RA'_step.
              { eapply RA_FJ. eapply R_Field with (pfc := pfc'); try eassumption.
                erewrite <- field_ids_same; eassumption. }
              apply RA'_refl.
           -- remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              apply lemma5. eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           -- inversion calPehlpt as [_ calPlpt].
              eapply calPsub.
              ++ apply calPadd. split. apply calPlpt. eassumption. assumption.
                 eapply P_Field with (pfc' := pfc'). constructor.
                 erewrite decl_ct'_decl_ct; eassumption.
              ++ eapply SUB_New, nth_error_In, Hehi.

      (* if c is in CT_L *)
      + dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_Lib_New *)
        * eexists. eexists. split; try split; try eassumption. apply RA'_refl.
           eapply Forall_In with (P := fun e => alpha ct ct' gamma e E_Lib lpt); try eassumption.
           eapply nth_error_In; eassumption.

        (* SubSubCase Rel_Lpt, CONTRADICTION  *)
        * destruct e'; inversion rel_e_eh; subst;
             try solve [eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption].
           clear IHrel_e_eh.
           assert (exists ehi, nth_error l n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H11. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           assert (valid_class ct' c) as pfc'.
           { apply in_table_valid'. apply in_lib_in_table. apply keep_id_keep_class with ct; assumption. }
           eexists. eexists. split; try split.
           -- eapply RA'_step.
              { eapply RA_Field with (pfc := pfc'). erewrite decl_ct'_decl_ct. eapply declchi. assumption.
                eapply decl_in_lib_ct_decl_in_lib_ct' with (c1 := c); eassumption. }
              eapply RA'_step.
              { eapply RA_Return. right. reflexivity. }
              eapply RA'_step.
              { eapply RAC_Field. eapply RA_Return. left. eapply H. }
              rewrite union_same. eapply RA'_step.
              { eapply RA_FJ. eapply R_Field with (pfc := pfc'); try eassumption.
                erewrite <- field_ids_same; eassumption. }
              apply RA'_refl.
           -- remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              apply lemma5.
              eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           -- inversion calPehlpt as [_ calPlpt].
              eapply calPsub.
              ++ apply calPadd. split. apply calPlpt. eassumption. assumption.
                 eapply P_Field with (pfc' := pfc'). constructor.
                 erewrite decl_ct'_decl_ct; eassumption.
              ++ eapply SUB_New, nth_error_In, Hehi.
           


  (* Case R_Invk *)

    - assert (exists ch, mresolve ct mi c pfc = Some ch) as exst_ch.
      { apply find_method_mresolve. eexists; eassumption. }
      destruct exst_ch as [ch mres_ch].
      assert (valid_class ct ch) as pfch...
      destruct (valid_in_table ct ch pfch).

      (* Subcase Rel_Invk and mresolve(m, C) in CT_A *)
      + assert (in_app ct c) by (eapply lemma1; eassumption).
        assert (valid_class ct' c) as pfc'.
        { apply in_table_valid', in_app_in_table, keep_app. auto. }
        dependent induction rel_e_eh.
        
        * split_rec 4.
           -- eapply RA'_step; try solve [constructor].
              eapply RA_FJ. eapply R_Invk with (pfc := pfc'); try eassumption.
              erewrite <- find_method_ct_ct'; eassumption.
           -- repeat rewrite combine_step. admit. (* apply lemma3; eauto. *)
           -- inversion calPehlpt as [calPinvk calPlpt].
              split; eauto. admit.
              

        * destruct (not_lib_app ct c pfc). split; auto.

        * inversion calPehlpt as [calPeh calPlpt].
           inversion calPeh; subst.
           eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; eauto.
           destruct IHspec as [eh' [lpt' [red_eh' [rel_eh' calP_eh']]]].
           split_rec 4; try eassumption; eauto.
           -- eapply RA'_step.
              { eapply RAC_Invk_Recv. eapply RA_Return. eassumption. }
              rewrite union_same. eauto.

      (* Subcase Rel_Invk and mresolve(m, C) in CT_L *)
      + admit.

    - assert (exists ch, mresolve ct mi c pfc = Some ch) as exst_ch.
      { apply find_method_mresolve. eexists; eassumption. }
      destruct exst_ch as [ch mres_ch].
      assert (valid_class ct ch) as pfch...
      destruct (valid_in_table ct ch pfch).

      (* Subcase Rel_Lib_Invk and mresolve(m, C) in CT_A *)
      + admit.

      (* Subcase Rel_Lib_Invk and mresolve(m, C) in CT_L *)
      + admit.


  (* Case R_Cast *)

    (* Subcase Rel_Cast *)
    - assert (in_table ct c) as c_in_table by eauto.
      dependent induction rel_e_eh.

      (* SubSubCase Rel_New, direct proof *)
      + split_rec 4; try (eapply RA'_step; try apply RA'_refl; apply RA_FJ; apply R_Cast); eauto.

      (* SubSubCase Rel_Lib_New, case analysis *)
      + destruct c_in_table as [c_in_app | c_in_lib].

      (* SubSubSubCase C in CT_A, CONTRADICTION *)
        * assert (valid_class ct c) as pfc... destruct (not_lib_app ct c pfc). split; eauto.

      (* SubSubSubCase C in CT_L, direct proof *)
        * split_rec 4; try (eapply RA'_step; try apply RA'_refl; apply RA_Cast); eauto.

      (* SubSubCase Rel_Lpt, induction *) 
      + inversion calPehlpt as [calPeh calPlpt]; inversion calPeh;
          eapply IHrel_e_eh in rel_ct; eauto; decomp; subst;
            split_rec 4; try (eapply RA'_step; try eassumption; rewrite <- union_same; eauto); eauto.

    (* Subcase Rel_Lib_Cast *)
    - split_rec 4; eauto.


  (* Case RC_Field *)

    (* Subcase Rel_Field *)
    - inversion val_e; inversion fj_expr_e; subst. eapply IHred_e_e' in rel_e_eh as IHspec; eauto.
      destruct IHspec as [eh'0 [lpt'' IHspec]]. decomp.
      exists (E_Field eh'0 f), lpt''. split_rec 2; try solve [erewrite union_include; eauto]; eauto.
      inversion calPehlpt as [calPeh calPlpt]. inversion calPeh; subst.
      inversion H3.
      split; eauto.

    (* Subcase Rel_Lib_Field *)
    - inversion val_e; inversion fj_expr_e; subst. eapply IHred_e_e' in rel_e_eh as IHspec; eauto.
      destruct IHspec as [eh'0 [lpt'' IHspec]]. decomp.
      destruct (E_Lib_dec eh'0); subst; try solve [split_rec 4; eauto].
      eapply lemma10 with (e0' := e') in rel_e_eh as lemma10spec; eauto.
      destruct lemma10spec as [lpt''' [rel_e'_lib red_lpt_lpt'']].
      exists E_Lib, lpt'''. split_rec 2; eauto.
      exists
      exists (E_Field eh'0 f), lpt''. split_rec 2; try solve [erewrite union_include; eauto]; eauto.
      inversion calPehlpt as [calPeh calPlpt]. inversion calPeh; subst.
      inversion H3.
      split; eauto.


  (* Case RC_Invk_Recv *)

    (* Subcase Rel_Invk *)
    - admit.

    (* Subcase Rel_Lib_Invk *)

    - admit.

  (* Case RC_Invk_Arg *)

    (* Subcase Rel_Invk *)
    - admit.

    (* Subcase Rel_Lib_Invk *)
    - admit.

  (* Case RC_New_Arg *)

    (* Subcase Rel_New *)
    - admit.

    (* Subcase Rel_Lib_New *)
    - admit.

  (* Case RC_Cast *)

    (* Subcase Rel_Cast *)
    - admit.

    (* Subcase Rel_Lib_Cast *)
    - admit.

Admitted.