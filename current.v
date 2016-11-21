Require Import proof.

Lemma lemma11 : forall ct ct' gamma e0 e e' eh lpt,
    ave_rel ct ct' -> FJ_reduce' ct e0 e -> FJ_reduce ct e e' ->
    alpha ct ct' gamma e eh lpt -> calP ct' gamma eh lpt ->
    type_checks ct gamma e0 -> fj_expr e0 ->
    exists eh' lpt', AVE_reduce' ct' eh lpt eh' lpt' /\ alpha ct ct' gamma e' eh' lpt' /\ calP ct' gamma eh' lpt'.
Proof.
  intros ct ct' gamma e0 e e' eh lpt rel_ct red_e0_e red_e_e' rel_e_eh calPehlpt typ_chk_e0 fj_expr_e0.
  induction red_e_e'.


  (* Case R_Field *)
  - inversion rel_e_eh.


    (* Subcase Rel_Field *)
    + subst lpt0. subst f. subst e.
      apply valid_in_table in pfc as c_in_table. destruct c_in_table as [c_in_app | c_in_lib].

      (* if c is in CT_A *)
      * inversion H5.
        -- subst lpt0. subst le0. subst ci.
           assert (exists ehi, nth_error le' n = Some ehi).
           { apply nth_error_better_Some. rewrite <- H6. apply nth_error_better_Some. exists ei. trivial. }
           destruct H1 as [ehi Hehi].
           exists ehi. exists lpt. split.
           ++ apply RA'_step with ehi lpt; try apply RA'_refl. apply RA_FJ.
              inversion rel_ct. inversion H3. assert (valid_class ct' c) as pfc'.
              { apply H12. apply in_app_in_table. apply H8; trivial. }
              apply R_Field with pfc' n; trivial. rewrite <- (field_ids_same pfc); trivial.
           ++ subst eh. subst e'. inversion calPehlpt. inversion H1. inversion H8.
              split; try split; try apply Forall_In with le'; try apply nth_error_In with n; try assumption.
              subst. apply Forall_In with (P := fun p => alpha ct ct' gamma (fst p) (snd p) lpt)
                                            (l := combine le le')
                                            (a := (ei, ehi)); try assumption.
              apply nth_error_In with n. apply nth_error_combine; assumption.
        -- destruct (not_lib_app ct c); trivial; split; trivial. inversion rel_ct.
           apply in_lib_id_in_lib; trivial. apply in_app_in_table; trivial.
        -- subst e'. subst lpt0. subst eh.
           inversion rel_ct as [_ _ keep_app _ _].
           exists E_Lib. eexists. split; try split. eapply RA'_step.
           eapply RAC_Field. eapply RA_New. eapply RA_Return.
           eapply RA_FJ. apply R_Field.


      (* if c is in CT_L *)
      * inversion H5.

        (* SubSubCase Rel_New *)
        -- subst le0. subst lpt0. subst ci.
           assert (exists ehi, nth_error le' n = Some ehi).
           { apply nth_error_better_Some. rewrite <- H6. apply nth_error_better_Some. exists ei. trivial. }
           destruct H1 as [ehi Hehi].
           exists ehi. exists lpt. split.
           ++ apply RA'_step with ehi lpt; try apply RA'_refl. apply RA_FJ.
              inversion rel_ct. inversion H3.
              assert (valid_class ct' c) as pfc'.
              { apply H12. apply in_lib_in_table. apply keep_id_keep_class with ct; assumption. }
              apply R_Field with pfc' n; trivial. rewrite <- (field_ids_same pfc); trivial.
           ++ 
           ++ apply calPsub with eh; trivial.
              apply SUB_Trans with e'.
              ** subst e'. apply SUB_New. apply nth_error_In with n; trivial.
              ** subst eh. apply SUB_Field.

        (* SubSubCase Rel_Lib_New *)
        -- subst e'. subst le0. subst lpt0. subst ci.
           assert (In fi (field_ids ct c pfc)).
           { assert (forall fi', (beq_nat fi) fi' = true <-> fi = fi').
             { split; try apply beq_nat_true. intro. subst. symmetry. apply beq_nat_refl. }
             apply (index_of_In (field_ids ct c pfc) (beq_nat fi) fi H1). exists n; assumption. }
           apply In_fields_decl_exists in H1. destruct H1 as [chi declchi].
           apply decl_of_in_lib_in_lib in declchi as chi_in_lib; try assumption.
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
             apply H10 in H2. destruct (not_lib_app (app, lib) ch pfch). split; assumption. }
           exists E_Lib. exists (add ch_new lpt).
           split.
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
           ** split. apply P_Lib. intros. destruct H7.
              apply calPlpt. apply H7. inversion H7. subst x. rewrite Heqch_new.
              apply P_New. apply Forall_repeat. apply P_Lib.
              apply decl_in_table with c0 pfc0' fi. assumption.

        (* SubSubCase Rel_Lpt *) 
        -- subst. exists (E_Field E_Lib fi). exists lpt. split. apply RA'_refl. assumption.


    (* Subcase Rel_Lib_Field *)
    + 


    (* Subcase Rel_Lpt *) 
    + exists E_Lib. exists lpt. split. apply RA'_refl. subst eh. trivial.


  (* Case R_Invk *)
  - dependent induction rel_e_eh.
    (* Subcase Rel_Invk *)
    + admit.
    (* Subcase Rel_Lib_Invk *)
    + admit.
    (* Subcase Rel_Lpt *)
    + exists E_Lib. exists lpt. split. apply RA'_refl. trivial.
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