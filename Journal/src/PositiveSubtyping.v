Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export PositiveBase.

Lemma chooseS_flip : forall m X A B C,
    chooseS m X A B C = chooseS (flip m) X B A C.
Proof with auto.
  intros.
  destruct m...
Qed.



Lemma sub_amber2_eq : forall A B E,
    sub_amber2 E A B -> sub_amber2 E B A -> A = B.
Proof with auto.
  induction 1; intros; simpl in *; eauto.
  -
    dependent destruction H1; eauto.
  -
    dependent destruction H1.
    rewrite IHsub_amber2_1; eauto.
    rewrite IHsub_amber2_2; eauto.
  -
    dependent destruction H2...
    f_equal.
    pick fresh X.
    apply open_rec_eq with (X:=X) (n:=0)...
    unfold open_tt in *...
    apply H0...
    apply H2...
Qed.

Lemma subst_eq_open: forall X A B C D Y,
    subst_tt X D A = subst_tt X C B ->
    type C -> type D ->
    Y \notin  {{X}} \u fv_tt C \u fv_tt D ->
    subst_tt X D (open_tt A Y) = subst_tt X C (open_tt B Y).
Proof with auto.
  intros.
  rewrite <- subst_tt_open_tt_var...
  rewrite <- subst_tt_open_tt_var...
  rewrite H.
  f_equal...
Qed.

Lemma subst_eq_chooseS: forall B X C D m,
    type C -> type D ->
    X \in fv_tt B ->
          chooseS m X C D B = chooseS m X D C B ->
          C = D.
Proof with auto.
  intro B.
  induction B;intros;simpl in *;try solve [apply F.empty_iff in H1;destruct H1]...
  -
    apply KeySetFacts.singleton_iff in H1.
    subst.
    unfold chooseS in H2;destruct m;simpl in *;destruct (X==X)...
    destruct n...
    destruct n...
  -
    rewrite chooseS_mu in H2.
    rewrite chooseS_mu in H2.
    inversion H2.
    apply IHB with (X:=X) (m:=m)...
  -
    rewrite chooseS_arrow in H2.
    rewrite chooseS_arrow in H2.
    inversion H2.
    apply AtomSetImpl.union_1 in H1.
    destruct H1...
    eauto.
    eauto.
Qed.

Lemma notin_subst: forall X T Y D,
    X `notin` fv_tt (subst_tt Y D T) ->
    X <> Y ->
    X \notin fv_tt T.
Proof with auto.
  intros.
  induction T;simpl in *...
  destruct (a==Y)...
  apply notin_singleton_2.
  subst...
Qed.

Lemma pos_subst_rev: forall A,
    type A ->
    forall m Y C D X,
      type C -> type D ->
    posvar m Y (subst_tt X D A) (subst_tt X C A) ->
    Y \notin {{X}} \u fv_tt C \u fv_tt D ->
    posvar m Y A A.
Proof with auto.
  intros A H.
  induction H;intros;simpl in *...
  -
    destruct (X==X0);subst...
  -
    dependent destruction H3.
    constructor;eauto.
  -
    dependent destruction H3...
    +
      apply pos_rec with (L:=L \u L0 \u fv_tt C \u {{X}} \u {{X0}} \u fv_tt D \u fv_tt T);intros.
      *
        specialize_x_and_L Y L.
        specialize_x_and_L Y (L0 \u {{X0}} ).
        rewrite subst_tt_open_tt_var in H3...
        rewrite subst_tt_open_tt_var in H3...
        specialize (H0 _ _ _ _ _ H1 H2 H3 H5)...
      *
        specialize_x_and_L Y L.
        specialize_x_and_L Y (L0 \u {{X0}} ).
        rewrite subst_tt_open_tt_var in H4...
        rewrite subst_tt_open_tt_var in H4...
        specialize (H0 _ _ _ _ _ H1 H2 H4)...
    +
      apply notin_subst in H3...
      apply pos_rec_t with (L:=L)...
Qed.


Lemma sub_amber_to_posvar: forall E A B  m X C D  ,
    sub_amber2 E A B ->
    sub_amber2 E C D ->
    sub_amber2 E (chooseS m X C D A) (chooseS m X D C B) ->
    posvar m X A B \/ (C = D).
Proof with auto.
  intros.
  generalize dependent X.
  generalize dependent m.
  dependent induction H;intros...
  -
    left.
    constructor...
    apply wfa_type in H...
  -
    destruct m;simpl in *;destruct (X==X0);subst...
    right.
    apply sub_amber2_eq in H1...
  -
    rewrite chooseS_arrow in H2.
    rewrite chooseS_arrow in H2.
    dependent destruction H2.
    rewrite  chooseS_flip in H2_.
    remember (chooseS (flip m) X C D B1).
    rewrite  chooseS_flip in H2_.
    subst.
    specialize (IHsub_amber2_1   H1 (flip m) _ H2_ ).    
    specialize (IHsub_amber2_2   H1 m _ H2_0 ).    
    destruct IHsub_amber2_1;destruct IHsub_amber2_2...    
  -
    rewrite chooseS_mu in H3.
    rewrite chooseS_mu in H3.
    dependent destruction H3.
    pick fresh Y.
    specialize_x_and_L Y L.
    specialize_x_and_L Y L0.
    assert (Ht:=H3).
    apply suba2_regular in H3.
    assert (Hq:=H2).
    apply suba2_regular in H2.
    destruct_hypos.
    apply wfa_type in H7.
    apply wfa_type in H8.
    dependent destruction H1...
    +
      assert (sub_amber2 ( nil ++ [(X, bind_sub)] ++ E) C D).
      apply sub_amber2_weakening...
      rewrite <- chooseS_open in Ht...
      rewrite <- chooseS_open in Ht...
      specialize (H0 H10 _ _ Ht).
      destruct H0...
      left.
      apply pos_rec with (L:=fv_tt B \u {{X0}} \u {{X}}  \u fv_tt C \u fv_tt D \u L0).
      intros.
      rewrite subst_tt_intro with (X:=X)...
      remember (subst_tt X Y (open_tt A X)).
      rewrite subst_tt_intro with (X:=X)...
      subst.
      apply pos_rename_fix...
      intros...
    +
      assert (X0 \notin fv_tt B \/ X0 \in fv_tt B).
      apply in_dec...
      destruct H10.
      left.
      apply pos_rec_t with (L:=L0 \u {{X}})...
      dependent destruction H9...
      *
        assert (sub_amber2 ( nil ++ [(X, bind_sub)] ++ E) C D).
        apply sub_amber2_weakening...
        rewrite <- chooseS_open in Ht...
        rewrite <- chooseS_open in Ht...
        specialize (H0 H12 _ _ Ht).
        destruct H0...
        left.
        apply pos_rec with (L:=fv_tt B \u {{X0}} \u {{X}} \u L2 \u fv_tt C \u fv_tt D \u L0).
        intros.
        rewrite subst_tt_intro with (X:=X)...
        apply pos_rename_fix...
        intros.
        specialize_x_and_L Y (L2 \u {{X}}).
        rewrite <- chooseS_open in H10...
        rewrite <- chooseS_open in H10...
        destruct m;simpl in H10.
        apply pos_subst_rev with (C:=C) (D:=D) (X:=X0)...
        apply pos_subst_rev with (C:=D) (D:=C) (X:=X0)...
      *
        right.
        apply subst_eq_chooseS with (X:=X0) (m:=m) (B:=B)...
Qed.

      

Lemma sub_typePairR : forall  A B X,
    sub X A B ->
    typePairR A B.
Proof with auto.
  intros.
  induction H...
  -
    constructor...
    apply wf_type in H0...
  -
    apply tp_rec with (L:=L )...
Qed.   

Lemma wfa_replacing: forall E1 E2 T X Y,
    WFA (E1++ X ~ bind_sub ++E2) T ->
    X <> Y ->
    WFA (E1++ Y ~ bind_sub ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    constructor.
    analyze_binds H.
  -
    simpl.
    rewrite_alist (E1 ++ Y ~ bind_sub ++ E2).
    constructor...
  -
    simpl.
    apply WFA_rec with (L:=L \u {{X}}).
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
Qed.

Lemma sub_amber2_replacing: forall E1 E2 A B X Y,
    sub_amber2 (E1 ++ (X ~ bind_sub) ++ E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    sub_amber2 (E1 ++ (Y ~ bind_sub) ++ E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;try solve [simpl in *;auto]...
  -
    constructor...
    apply wfa_replacing...
  -
    simpl.
    destruct (X0==X)...
    constructor...
    analyze_binds H.
  -
    simpl.
    apply sam2_rec with (L:=L \u {{X}} \u dom E1 \u dom E2 \u {{Y}} \u fv_tt A \u fv_tt B);intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2)...
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
    assert (typ_mu (subst_tt X Y A) = subst_tt X Y (typ_mu A)) by auto.
    assert (typ_mu (subst_tt X Y B) = subst_tt X Y (typ_mu B)) by auto.
    rewrite H5.
    rewrite H6.
    apply pos_rename_fix...
Qed.
    
    
Lemma sub_to_amber2: forall E A B,
    sub E A B ->
    sub_amber2 E A B.
Proof with auto.
  intros.
  assert (Ht:=H).
  induction H...
  constructor...
  apply soundness_wf in H0...
  apply completeness_wfa...
  pick fresh X.
  specialize_x_and_L X L.
  specialize (H0 H).
  specialize (H2 H1).
  apply suba_regular in Ht.
  destruct_hypos.
  assert (Hq:=H0).
  apply sub_amber_to_posvar with (m:=Pos) (X:=X) (A:=open_tt A1 X) (B:=open_tt A2 X) in H0...
  destruct H0.
  -
    apply sam2_rec with (L:={{X}} \u fv_tt A1 \u fv_tt A2 \u dom E);intros...
    rewrite subst_tt_intro with (X:=X)...
    remember (subst_tt X X0 (open_tt A1 X)).
    rewrite subst_tt_intro with (X:=X)...
    subst.
    rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
    apply sub_amber2_replacing...
    simpl...
    constructor...
    apply pos_rec with (L:=fv_tt A1 \u fv_tt A2 \u {{X}} \u {{X0}}).
    intros.
    rewrite subst_tt_intro with (X:=X)...
    remember (subst_tt X Y (open_tt A1 X)).
    rewrite subst_tt_intro with (X:=X)...
    subst.
    apply pos_rename_fix...
    apply pos_rename_3 with (X:=X) (m:=Pos)...
    apply notin_union.
    split...
    apply notin_union.
    split;apply notin_fv_tt_open_aux...
    intros.
    rewrite subst_tt_intro with (X:=X)...
    remember (subst_tt X Y (open_tt A1 X)).
    rewrite subst_tt_intro with (X:=X)...
    subst.
    apply pos_rename_1...
    apply notin_union.
    split...
    apply notin_union.
    split;apply notin_fv_tt_open_aux...
  -
    unfold open_tt in H0.
    apply open_rec_eq in H0...
    subst.
    apply sub_amber2_refl...
  -
    simpl...
    rewrite <- subst_tt_intro...
    rewrite <- subst_tt_intro...
Qed.
