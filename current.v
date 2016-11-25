Require Import proof.

Lemma RA'_trans : forall ct' e lpt e' lpt' e'' lpt'',
    AVE_reduce' ct' e lpt e' lpt' ->
    AVE_reduce' ct' e' lpt' e'' lpt'' ->
    AVE_reduce' ct' e lpt e'' lpt''.
Proof.
  intros ct' e lpt e' lpt' e'' lpt'' red_first. generalize dependent e''. generalize dependent lpt''.
  dependent induction red_first; intros; try assumption.
  eapply RA'_step; try eapply IHred_first; eassumption.
Qed.

Lemma lemma8' : forall (ct' : class_table) (e e' : expr) (lpt lpt' : set expr),
    AVE_reduce' ct' e lpt e' lpt' -> subset lpt lpt'.
Proof.
  intros. induction H.
  - unfold subset. intros x H. assumption.
  - apply lemma8 in H. eapply subset_trans; eassumption.
Qed.

Lemma RAC'_Field : forall ct' e e' lpt lpt' fi,
    AVE_reduce' ct' e lpt e' lpt' -> AVE_reduce' ct' (E_Field e fi) lpt (E_Field e' fi) (lpt' U lpt).
Proof.
  intros.
  induction H.
  - rewrite union_same. apply RA'_refl.
  - eapply RA'_step. apply RAC_Field. apply H.
    assert (subset lpt lpt') by (eapply lemma8; eassumption).
    assert (subset lpt' lpt'') by (eapply lemma8'; eassumption).
    assert (subset lpt lpt'') by (eapply subset_trans; eassumption).
    repeat (rewrite <- union_include; try assumption).
    rewrite <- union_include in IHAVE_reduce'; assumption.
Qed.

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

Lemma calPadd : forall ct' gamma e ea lpt,
    calP ct' gamma e lpt -> calPexpr ct' gamma ea -> calP ct' gamma e (add ea lpt).
Proof.
  intros. inversion H as [calPe calPlpt].
  split; try assumption.
  intros. destruct H1; auto.
  inversion H1. subst. assumption.
Qed.

Lemma find_method_mresolve_h : forall l mi,
    existsb (fun a => beq_nat mi match a with Method _ id _ _ => id end) l =
    existsb (fun a => match a with Method _ id _ _ => beq_nat mi id end) l.
Proof.
  induction l; try reflexivity.
  intros. simpl. destruct a. rewrite IHl. reflexivity.
Qed.

Lemma check : forall {A B}, A <-> B -> ~ A -> ~ B.
Proof. intros. intro. apply H in H1. contradiction. Qed.

Lemma find_method_mresolve : forall {ct c} pfc mi,
    (exists m, find_method mi pfc = Some m) <-> (exists p, mresolve ct mi c pfc = Some p).
Proof.
  induction pfc; (split; intros; [destruct H as [m Hm]; inversion Hm | destruct H as [p Hp]; inversion Hp]).
  - destruct (lookup_method c mi) eqn:find_method.
    + inversion H0; subst.
      exists c. simpl. unfold lookup_method in find_method. destruct c; try solve [inversion e].
      simpl. rewrite existsb_map.
      assert (existsb (fun a : method => PeanoNat.Nat.eqb mi match a return method_id with
                                                     | Method _ id _ _ => id
                                                          end) l0 = true).
      { rewrite find_method_mresolve_h. apply existsb_find. eexists; eassumption. }
      rewrite H. reflexivity.
    + simpl. unfold lookup_method in find_method. destruct c; try solve [inversion e].
      assert (~ exists m, find (fun m : method => match m with
                                        | Method _ mi' _ _ => PeanoNat.Nat.eqb mi mi'
                                          end) l0 = Some m).
      { intro. destruct H. rewrite find_method in H. inversion H. }
      eapply check in H. Focus 2. symmetry. apply existsb_find. apply Bool.not_true_is_false in H.
      simpl. rewrite existsb_map. rewrite find_method_mresolve_h. rewrite H.
      apply IHpfc. simpl in Hm. rewrite find_method in Hm. eexists. eassumption.
  - destruct c; try solve [inversion e].
    destruct (existsb (beq_nat mi) (dmethods_id (C c c0 l c1 l0))) eqn:exstb; simpl in exstb; simpl;
      rewrite existsb_map, find_method_mresolve_h in exstb.
    + apply existsb_find in exstb. destruct exstb as [m Hm]. rewrite Hm. eexists. reflexivity.
    + rewrite <- Bool.not_true_iff_false in exstb. eapply check in exstb. Focus 2. apply existsb_find.
      apply not_exists_some_iff_none in exstb. rewrite exstb. apply IHpfc. eexists. eassumption.
Qed.

Ltac try_invert :=
  try match goal with
      | [ H : _ |- _ ] => try solve [inversion H]
      end.

Hint Constructors AVE_reduce. Hint Constructors AVE_reduce'. Hint Resolve RA'_trans.
Hint Constructors valid_class.

Lemma mresolve_valid : forall {ct c} pfc mi e,
    mresolve ct mi c pfc = Some e -> valid_class ct e.
Proof.
  induction pfc; intros; try_invert.
  simpl in H. destruct (existsb (beq_nat mi) (dmethods_id c)); inversion H; subst; eauto.
Qed.
Hint Resolve mresolve_valid.

Ltac decomp :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : exists _, _ |- _ ] => destruct H
         end.

Ltac split_rec n :=
  match n with
  | S ?n' => match goal with
            |[ |- exists _, _ ] => eexists; split_rec n'
            |[ |- _ /\ _] => split; split_rec n'
            | _ => idtac
            end
  | 0 => idtac
  end.

Lemma lemma11 : forall ct ct' gamma e0 e e' eh lpt,
    ave_rel ct ct' -> FJ_reduce' ct e0 e -> FJ_reduce ct e e' ->
    alpha ct ct' gamma e eh lpt -> calP ct' gamma eh lpt ->
    type_checks ct gamma e0 -> fj_expr e0 ->
    exists eh' lpt', AVE_reduce' ct' eh lpt eh' lpt' /\ alpha ct ct' gamma e' eh' lpt' /\ calP ct' gamma eh' lpt'.
Proof.
  intros ct ct' gamma e0 e e' eh lpt rel_ct red_e0_e red_e_e' rel_e_eh calPehlpt typ_chk_e0 fj_expr_e0.
  induction red_e_e'.


  (* Case R_Field *)
  - dependent induction rel_e_eh.


    (* Subcase Rel_Field *)
    + assert (In fi (field_ids ct c pfc)) as In_fields.
      { assert (forall fi', (beq_nat fi) fi' = true <-> fi = fi').
        { split; try apply beq_nat_true. intro. subst. symmetry. apply beq_nat_refl. }
        eapply index_of_In. eassumption. eexists; eassumption. }
      apply In_fields_decl_exists in In_fields. destruct In_fields as [chi declchi].
      apply valid_in_table in pfc as c_in_table. destruct c_in_table as [c_in_app | c_in_lib].

      (* if c is in CT_A *)
      * clear IHrel_e_eh. dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_New *)
        -- assert (exists ehi, nth_error le' n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H0. apply nth_error_better_Some. eexists; eauto. }
           destruct exeh as [ehi Hehi].
           exists ehi. exists lpt. split.
           ++ eapply RA'_step with ehi lpt; try eapply RA'_refl. apply RA_FJ.
              inversion rel_ct as [_ val_ct' keep_app _ _].
              destruct val_ct' as [ct' in_table_valid _ _ _ _ _ _]. assert (valid_class ct' c) as pfc'.
              { apply in_table_valid. apply in_app_in_table. apply keep_app; assumption. }
              eapply R_Field with (pfc := pfc'); eauto. rewrite <- (field_ids_same pfc); trivial.
           ++ inversion calPehlpt as [calPeh calPlpt]. inversion calPeh. inversion H6.
              split; try split; try apply Forall_In with le'; try apply nth_error_In with n; try assumption.
              subst. apply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt)
                                            (l := combine le le')
                                            (a := (ei, ehi)); try assumption.
              apply nth_error_In with n. apply nth_error_combine; assumption.

        (* SubSubCase Rel_Lib_New, CONTRADICTION  *)
        -- destruct (not_lib_app ct c); trivial; split; trivial. inversion rel_ct.
           apply in_lib_id_in_lib; trivial. apply in_app_in_table; trivial.

        (* SubSubCase Rel_Lpt, Induction  *)
        -- eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption.
           destruct IHspec as [eh' [lpt' [red_eh' [rel_eh' calP_eh']]]].
           exists eh'. exists lpt'. split; try split; try assumption.
           ++ eapply RA'_trans; try eassumption.
              eapply RA'_step; try solve [econstructor].
              rewrite <- union_same. eapply RAC_Field.
              apply RA_Return. assumption.
           ++ destruct calPehlpt as [_ calP_lpt].
              inversion rel_ct as [_ val_ct' keep_app _ _].
              inversion val_ct' as [ct0 in_table_valid _ _ _ _ _]. clear ct0 H2.
              assert (valid_class ct' c) as pfc'.
              { apply in_table_valid, in_app_in_table, keep_app, c_in_app. }
              split; try assumption. eapply P_Field with (pfc' := pfc'); eauto.
              erewrite decl_ct'_decl_ct; eassumption.

      (* if c is in CT_L *)
      * clear IHrel_e_eh. dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_New *)
        -- assert (exists ehi, nth_error le' n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H0. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           exists ehi. exists lpt. split; try split.
           ++ apply RA'_step with ehi lpt; try apply RA'_refl. apply RA_FJ.
              inversion rel_ct as [_ val_ct' _ _ _]. destruct val_ct' as [ct' valid_in_table _ _ _ _ _ _].
              assert (valid_class ct' c) as pfc'.
              { apply valid_in_table. apply in_lib_in_table. apply keep_id_keep_class with ct; assumption. }
              apply R_Field with pfc' n; trivial. rewrite <- (field_ids_same pfc); trivial.
           ++ remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           ++ eapply calPsub; try eassumption.
              eapply SUB_Trans.
              ** apply SUB_New. eapply nth_error_In. eassumption.
              ** eapply SUB_Field.

        (* SubSubCase Rel_Lib_New *)
        -- apply decl_of_in_lib_in_lib in declchi as chi_in_lib; try assumption.
           assert (ch_in_lib := chi_in_lib).
           unfold in_lib_id in ch_in_lib. destruct ct as [app lib].
           destruct ch_in_lib as [ch Hch].
           inversion rel_ct as [valid_ct valid_ct' _ _ _].
           inversion valid_ct as [ct in_table_valid _ one_cid id_in_one one_fid _]. subst.
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
           inversion valid_ct' as [ct in_table_valid' _ _ _ _ _]. subst.
           assert (valid_class ct' ch) as pfch'. 
           { apply in_table_valid'. apply in_table_in_table' with (app, lib); try assumption.
             - right. assumption.
             - apply decl_in_table with c0 pfc0' fi. assumption. }
           remember (E_New (id_of ch) (repeat E_Lib (length (fields ct' ch pfch')))) as ch_new.
           assert (in_lib ct' ch).
           { destruct (valid_in_table ct' ch pfch'); try assumption. inversion rel_ct.
             destruct (not_lib_app (app, lib) ch pfch). split; try apply H9; assumption. }
           exists E_Lib. exists (add ch_new lpt).
           split; try split.
           ** apply RA'_step with (E_Field E_Lib fi) (add ch_new lpt).
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
           ** apply lemma5. eapply Forall_In with (P := fun e  => alpha (app, lib) ct' gamma e E_Lib lpt);
                              try eapply nth_error_In; eassumption.
           ** split. apply P_Lib. intros. destruct H7.
              apply calPlpt. apply H7. inversion H7. subst x. rewrite Heqch_new.
              apply P_New. apply Forall_repeat. apply P_Lib.
              apply decl_in_table with c0 pfc0' fi. assumption.

        (* SubSubCase Rel_Lpt, CONTRADICTION  *)
        -- eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption.
           destruct IHspec as [eh' [lpt' [red_eh' [rel_eh' calP_eh']]]].
           exists eh'. exists lpt'. split; try split; try assumption.
           ++ eapply RA'_trans; try eassumption.
              eapply RA'_step; try solve [econstructor].
              rewrite <- union_same. eapply RAC_Field.
              apply RA_Return. assumption.
           ++ destruct calPehlpt as [calPeh calP_lpt].
              split; try assumption. inversion calPeh. eapply P_Field; try eassumption; apply calP_lpt, H.

    (* Subcase Rel_Lib_Field *)
    + assert (In fi (field_ids ct c pfc)) as In_fields.
      { assert (forall fi', (beq_nat fi) fi' = true <-> fi = fi').
        { split; try apply beq_nat_true. intro. subst. symmetry. apply beq_nat_refl. }
        eapply index_of_In. eassumption. eexists; eassumption. }
      apply In_fields_decl_exists in In_fields. destruct In_fields as [chi declchi].
      inversion rel_ct as [val_ct val_ct' keep_app _ _ ].
      inversion val_ct as [ct0 _ _ _ _ same_fi _]. clear ct0 H4.
      inversion val_ct' as [ct0 in_table_valid' _ _ _ _ _]. clear ct0 H4.
      assert (di = chi) by (eapply same_fi; eassumption). subst di.
      apply valid_in_table in pfc as c_in_table. destruct c_in_table as [c_in_app | c_in_lib].

      (* if c is in CT_A *)
      * clear IHrel_e_eh. dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_Lib_New, CONTRADICTION *)
        -- destruct (not_lib_app ct c pfc). split; try assumption.
           apply in_lib_id_in_lib; try apply rel_ct; try apply in_app_in_table; assumption.

        (* SubSubCase Rel_Lpt, INDUCTION  *)
        -- destruct e'; inversion rel_e_eh; subst;
             try solve [eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption].
           clear IHrel_e_eh.
           assert (exists ehi, nth_error l n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H11. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           assert (valid_class ct' c) as pfc'.
           { apply in_table_valid', in_app_in_table, keep_app. assumption. }
           eexists. eexists. split; try split.
           ++ eapply RA'_step.
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
           ++ remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              apply lemma5. eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           ++ inversion calPehlpt as [_ calPlpt].
              eapply calPsub.
              ** apply calPadd. split. apply calPlpt. eassumption. assumption.
                 eapply P_Field with (pfc' := pfc'). constructor.
                 erewrite decl_ct'_decl_ct; eassumption.
              ** eapply SUB_New, nth_error_In, Hehi.

      (* if c is in CT_L *)
      * clear IHrel_e_eh. dependent induction rel_e_eh; intros.

        (* SubSubCase Rel_Lib_New *)
        -- eexists. eexists. split; try split; try eassumption. apply RA'_refl.
           eapply Forall_In with (P := fun e => alpha ct ct' gamma e E_Lib lpt); try eassumption.
           eapply nth_error_In; eassumption.

        (* SubSubCase Rel_Lpt, CONTRADICTION  *)
        -- destruct e'; inversion rel_e_eh; subst;
             try solve [eapply IHrel_e_eh in rel_ct as IHspec; try reflexivity; try eassumption].
           clear IHrel_e_eh.
           assert (exists ehi, nth_error l n = Some ehi) as exeh.
           { apply nth_error_better_Some. rewrite <- H11. apply nth_error_better_Some. exists ei. trivial. }
           destruct exeh as [ehi Hehi].
           assert (valid_class ct' c) as pfc'.
           { apply in_table_valid'. apply in_lib_in_table. apply keep_id_keep_class with ct; assumption. }
           eexists. eexists. split; try split.
           ++ eapply RA'_step.
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
           ++ remember (ei, ehi) as p.
              replace ei with (fst p); try replace ehi with (snd p); try (rewrite Heqp; reflexivity).
              apply lemma5.
              eapply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt).
              eassumption. eapply nth_error_In. erewrite nth_error_combine; eauto.
              rewrite Heqp. reflexivity.
           ++ inversion calPehlpt as [_ calPlpt].
              eapply calPsub.
              ** apply calPadd. split. apply calPlpt. eassumption. assumption.
                 eapply P_Field with (pfc' := pfc'). constructor.
                 erewrite decl_ct'_decl_ct; eassumption.
              ** eapply SUB_New, nth_error_In, Hehi.
           

    (* Subcase Rel_Lpt *) 
    + destruct calPehlpt; eapply IHrel_e_eh in rel_ct; try reflexivity; try split; eauto;
        decomp; split_rec 4; try eassumption; eauto.


  (* Case R_Invk *)
  - assert (exists ch, mresolve ct mi c pfc = Some ch).
    { apply find_method_mresolve. eexists; eassumption. }
    destruct H1 as [ch mres_ch].
    assert (valid_class ct ch) as pfch by eauto.
    dependent induction rel_e_eh; destruct (valid_in_table ct ch pfch);
      try solve [destruct calPehlpt; eapply IHrel_e_eh in rel_ct; try reflexivity; try split; eauto;
                 decomp; split_rec 4; try eassumption; eauto]; clear IHrel_e_eh.


    (* Subcase Rel_Invk and mresolve(m, C) in CT_A *)
    + assert (in_app ct c) by (eapply lemma1; eassumption).
      split_rec 4.
      * 


    (* Subcase Rel_Lib_Invk *)
    + admit.

  (* Case R_Cast *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Cast *)
    + admit.
    (* Subcase Rel_Lib_Cast *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
  (* Case RC_Field *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Field *)
    + admit.
    (* Subcase Rel_Lib_Field *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
  (* Case RC_Invk_Recv *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Invk *)
    + admit.
    (* Subcase Rel_Lib_Invk *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
  (* Case RC_Invk_Arg *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Invk *)
    + admit.
    (* Subcase Rel_Lib_Invk *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
  (* Case RC_New_Arg *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_New *)
    + admit.
    (* Subcase Rel_Lib_New *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
  (* Case RC_Cast *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Cast *)
    + admit.
    (* Subcase Rel_Lib_Cast *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
Admitted.