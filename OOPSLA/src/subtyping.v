Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export infra.

(** Lemma 3 *)
Lemma sub_regular : forall E A B,
    Sub E A B -> wf_env E /\ WFS E A /\ WFS E B.
Proof with auto.
  intros.
  induction H...
  destruct IHSub1.
  destruct IHSub2.
  destruct H2.
  destruct H4.
  split...
  split.
  pick fresh X.
  specialize (H0 0 X).
  assert (X \notin L) by auto.
  apply H0 in H1.
  destruct H1.
  dependent destruction H1...
  split;apply WFS_rec with (L:=L);intros;
  apply H0...
Qed.

(** Theorem 4 (Reflexivity) *)
Lemma refl : forall E A,
    wf_env E -> WFS E A -> Sub E  A A.
Proof with auto.
  intros.
  induction H0...
  apply SA_rec with (L:=L \u dom E)...
Defined.

Lemma trans_aux: forall B E,
    WFS E B -> forall A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros...
  -
    dependent destruction H0.
    dependent destruction H...
  -
    dependent destruction H.
    dependent destruction H0...
  -
    dependent destruction H0.
    dependent destruction H2...
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...    
    constructor...
    apply sub_regular in H1_...
    apply H1_.
    apply sub_regular in H1_0...
    apply H1_0.
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...
    apply WFS_rec with (L:=L0)...
    intros...
    specialize (H1 n X H4).
    apply sub_regular in H1...
    destruct H1...
    destruct H5...
    apply SA_rec with (L:=L \u L0 \u L1).
    intros.
    apply H0 with (n:=n)...
Qed.

(** Theorem 5 (Transitivity) *)
Lemma Transitivity: forall B E A C,
    Sub E A B -> Sub E B C -> Sub E A C.
Proof with auto.
  intros.
  apply trans_aux with (B:=B)...
  apply sub_regular in H0.
  destruct H0.
  destruct H1...
Qed.

Lemma Sub_weakening: forall E E1 E2 A B,
    Sub (E1++E2) A B ->
    wf_env (E1 ++ E ++ E2) ->
    Sub (E1++E++E2) A B.
Proof with auto.
  intros.
  generalize dependent E.
  dependent induction H;intros...
  -
    constructor...
    apply wfs_weakening...
  -
    apply SA_rec with (L:=L \u dom (E1 ++ E ++ E2))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E1) ++ E ++ E2).
    apply H0...
    rewrite_alist ([(X, bind_sub)] ++ E1 ++ E ++ E2)...
Qed.

Lemma wfs_replacing: forall E1 E2 T X Y,
    WFS (E1++ X ~ bind_sub ++E2) T ->
    X <> Y ->
    WFS (E1++ Y ~ bind_sub ++E2) (subst_tt X Y T).
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
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
Qed.


Lemma Sub_replacing: forall E1 E2 A B X Y,
    Sub (E1++ X ~ bind_sub ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    Sub (E1++ Y ~ bind_sub ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    analyze_binds H0.
  -
    simpl.
    constructor...
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    apply wfs_replacing...
  -
    simpl.
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
  -
    simpl.
    apply SA_rec with (L:=L  \u {{X}} \u dom (E1 ++ [(Y, bind_sub)] ++ E2) )...
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
Qed.

Lemma subst_wfs_unfoldn: forall n T X E1 E2,
    WFS (E1 ++ X ~ bind_sub ++ E2) (unfoldT T X n) ->
    forall Y, Y \notin fv_tt T \u {{X}} -> X \notin fv_tt T ->
    WFS (E1 ++ Y ~ bind_sub ++ E2) (unfoldT T Y n).
Proof with auto.
  intros.
  rewrite <- unfoldT_subst with (X:=X)...
  apply wfs_replacing...
Qed.
  

Lemma subst_sub_unfoldn: forall n C D X E1 E2,
    Sub (E1 ++ X ~ bind_sub ++ E2) (unfoldT C X n) (unfoldT D X n) ->
    forall Y, Y \notin fv_tt C \u fv_tt D \u {{X}} ->
              X \notin fv_tt C \u fv_tt D ->
              wf_env (E1 ++ Y ~ bind_sub  ++ E2) ->
              Sub (E1 ++ Y ~ bind_sub  ++ E2) (unfoldT C Y n) (unfoldT D Y n).
Proof with auto.
  intros.
  rewrite <- unfoldT_subst with (X:=X)...
  remember (subst_tt X Y (unfoldT C X n)).
  rewrite <- unfoldT_subst with (X:=X)...
  subst.
  apply Sub_replacing...
Qed.

Lemma wfs_permutation: forall E E1 E2 E3 A,
    WFS (E ++ E1 ++ E2 ++ E3) A ->
    WFS (E ++ E2 ++ E1 ++ E3) A.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor.
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaL...
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaR.
    apply In_lemmaR...
    apply In_lemmaL...
    apply in_app_iff in H.
    destruct H.
    apply In_lemmaR...
    apply In_lemmaL...
    apply In_lemmaR...
    apply In_lemmaR...
    apply In_lemmaR...
  -
    apply WFS_rec with (L:=L)...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E) ++ E2 ++ E1 ++ E3).
    apply H0...
Qed.    
    
Lemma Sub_permutation: forall E E1 E2 E3 A B,
    Sub (E ++ E1 ++ E2 ++ E3) A B ->
    wf_env (E ++ E2 ++ E1 ++ E3) ->
    Sub (E ++ E2 ++ E1 ++ E3) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H0...
  -
    constructor...
    apply wfs_permutation...
  -
    apply SA_rec with (L:=L \u dom (E ++ E2 ++ E1 ++ E3 ))...
    intros.
    rewrite_alist (([(X, bind_sub)] ++ E) ++ E2 ++ E1 ++ E3).
    apply H0...
    rewrite_alist ([(X, bind_sub)] ++ E ++ E2 ++ E1 ++ E3)...    
Qed.

Lemma strengthening_wfs: forall E1 E2 T X m,
    WFS (E1 ++ X ~ m ++ E2) T->
    X \notin fv_tt T ->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    analyze_binds H...
    simpl.
    apply D.F.singleton_iff...
  -
    simpl in H1.
    constructor...
    apply IHWFS1 with (X0:=X) (m0:=m)...
    apply IHWFS2 with (X0:=X) (m0:=m)...
  -
    simpl in H1.
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_fv_tt_open...
Qed.    

Lemma strengthening_sub: forall E1 E2 A B X m,
    Sub (E1 ++ X ~ m ++ E2) A B ->
    X \notin (fv_tt A \u fv_tt B) ->
    wf_env  (E1 ++ E2 ) ->
    Sub (E1 ++ E2) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H0...
    apply AtomSetImpl.union_2.
    apply D.F.singleton_iff...
  -
    constructor...
    apply strengthening_wfs with (X:=X) (m:=m)...
  -
    simpl in H1.
    constructor...
    apply IHSub1 with (X0:=X) (m0:=m)...
    apply IHSub2 with (X0:=X) (m0:=m)...
  -
    simpl in H1.
    apply SA_rec with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (m0:=m)...
    apply notin_union.
    split.
    apply notin_fv_tt_open...
    apply notin_fv_tt_open...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ E2).
    constructor...
Qed.


Lemma subst_rec: forall E1 E2 X A B,
    Sub (E1 ++ X ~ bind_sub ++ E2) A B ->
    wf_env (E1 ++ E2) ->
    forall  C D ,
      WFS (E1 ++ E2) (typ_mu C) -> WFS (E1 ++ E2) (typ_mu D) ->
      X \notin fv_tt C \u fv_tt D \u dom (E1 ++ E2)  ->
    (forall n, Sub (X ~ bind_sub ++ E1 ++ E2) (subst_tt X (unfoldT C X n) A) (subst_tt X (unfoldT D X n) B)) ->
    Sub (E1 ++ E2) (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros E1 E2 X A B H.
  dependent induction H;intros...
  -
    simpl in *...
    destruct (X0==X)...
    apply SA_rec with (L:={{X}} \u fv_tt C \u fv_tt D \u dom (E1 ++ E2)).
    intros...
    rewrite_alist (nil ++ [(X1, bind_sub)] ++ (E1 ++ E2)).
    apply subst_sub_unfoldn with (X:=X)...
    simpl...
    constructor...
    constructor...
    analyze_binds H0.
  -
    constructor...
    rewrite_alist (nil ++ E1 ++ E2).
    apply subst_tt_wfs2...
    simpl.
    rewrite_alist (nil ++ (X ~ bind_sub) ++ E1 ++ E2).
    apply wfs_permutation...
  -
    simpl in *.
    constructor...
    apply IHSub1...
    intros.
    specialize (H5 n).
    dependent destruction H5...
    apply IHSub2...
    intros.
    specialize (H5 n).
    dependent destruction H5...
  -
    assert (type (typ_mu C)). apply wfs_type with (E:=E1 ++ E2)...
    assert (type (typ_mu D)). apply wfs_type with (E:=E1 ++ E2)...
    simpl in *...
    apply SA_rec with (L:=L \u {{X}} \u fv_tt C \u fv_tt D \u fv_tt A1 \u fv_tt A2 \u dom (E1 ++ E2)).
    intros.
    rewrite <- subst_open_unfoldn...
    rewrite <- subst_open_unfoldn...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0...
    +
      constructor...
    +
      rewrite_alist  (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
      apply wfs_weakening...
    +
      rewrite_alist  (nil ++ [(X0, bind_sub)] ++ (E1 ++ E2)).
      apply wfs_weakening...
    +
      intros.
      specialize (H5 n0).
      dependent destruction H5.
      remember (unfoldT C X n0).
      remember (unfoldT D X n0).
      assert (type t).
      {
        dependent destruction H6.
        subst.
        pick fresh Y.
        rewrite <- unfoldT_subst with (X:=Y)...
        apply subst_tt_type...
        apply type_unfoldT...
      }
      assert (type t0).
      {
        dependent destruction H7.
        subst.
        pick fresh Y.
        rewrite <- unfoldT_subst with (X:=Y)...
        apply subst_tt_type...
        apply type_unfoldT...
      }
      rewrite subst_open_unfoldn...
      rewrite subst_open_unfoldn...
      pick fresh X1.
      remember (subst_tt X t A1).
      remember (subst_tt X t0 A2).
      rewrite_alist (X ~ bind_sub ++ [(X0, bind_sub)] ++ (E1 ++ E2)) .
      apply subst_sub_unfoldn with (X:=X1)...
      rewrite_alist (nil ++ [(X, bind_sub)] ++ [(X1, bind_sub)] ++ (E1 ++ E2)).
      apply Sub_permutation...
      simpl.
      apply H5...
      simpl.
      constructor...
      constructor...
      assert (X0 \notin fv_tt t1).
      {
        subst.
        apply notin_fv_subst...
        apply notin_fv_tt_open...
      }
      assert (X0 \notin fv_tt t2).
      {
        subst.
        apply notin_fv_subst...
        apply notin_fv_tt_open...
      }
      auto.
      assert (X1 \notin fv_tt t1).
      {
        subst.
        apply notin_fv_subst...
      }
      assert (X1 \notin fv_tt t2).
      {
        subst.
        apply notin_fv_subst...
      }
      auto.
Qed.

(** Lemma 7 

Note: Here _unfoldT_ is a syntax sugar representing finite unfolding.
We show the formulation after desugaring them in the paper.
*)
Lemma subst_rec_col: forall E X A B,
    Sub (X ~ bind_sub ++ E) A B ->
    wf_env E ->
    forall  C D ,
      WFS E (typ_mu C) -> WFS E (typ_mu D) ->
      X \notin fv_tt C \u fv_tt D \u dom E  ->
    (forall n, Sub (X ~ bind_sub ++E) (subst_tt X (unfoldT C X n) A) (subst_tt X (unfoldT D X n) B)) ->
    Sub E (subst_tt X (typ_mu C) A) (subst_tt X (typ_mu D) B).
Proof with auto.
  intros.
  assert (E = nil ++ E) by auto.
  rewrite H5 in *.
  rewrite_alist (nil ++ [(X, bind_sub)] ++ empty ++ E) in H.
  apply Sub_permutation in H...
  rewrite_alist (nil ++ [(X, bind_sub)] ++ E) in H.
  apply subst_rec...
  simpl...
  constructor...
Qed.  
  
(** Lemma 8 (Unfolding Lemma) *)
Lemma unfolding_lemma :
  forall E A B,
    Sub E (typ_mu A) (typ_mu B) ->
    Sub E (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof with auto.
  intros.
  dependent destruction H.
  pick fresh X.
  assert (X \notin L) by auto.
  assert (WF := H).
  specialize (H 0 X H0).
  simpl in H.
  assert (wf_env ((X, bind_sub) :: E)).
  apply sub_regular in H.
  destruct H...
  remember (open_tt A X) as S.
  remember (open_tt B X) as T.
  apply subst_rec_col with (X:=X) (C:=A) (D:=B) in H...
  -
    subst.
    rewrite <- subst_tt_intro in H...
    rewrite <- subst_tt_intro in H...
  -
    simpl...
    inversion H1...
  -
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    assert (X0 \notin L) by auto.
    specialize (WF n X0 H3).
    apply sub_regular in WF.
    destruct WF.
    destruct H5.
    rewrite_alist ([(X0, bind_sub)] ++ E)...
  -
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    assert (X0 \notin L) by auto.
    specialize (WF n X0 H3).
    apply sub_regular in WF.
    destruct WF.
    destruct H5.
    rewrite_alist ([(X0, bind_sub)] ++ E)...
  -
    intros.
    subst.
    rewrite unfoldSn...
    rewrite unfoldSn...
Qed.


(** Lemma 17 

Note: Lemma 17, 19 and 20 have syntax sugar _chooseS_ and _chooseD_. 
We show the formulation after desugaring them in the paper.
*)
Lemma gnegative_lemma : forall A B X m E2,
    NTyp E2 m X A B -> forall C D , type C -> type D ->
    Sub E2 (chooseS m X C D A) (chooseS m X D C B) -> 
    Sub E2 D C.
Proof with auto.  
  induction 1; intros; simpl in *...
  -
    destruct (X == X); try contradiction; eauto.
  -
    rewrite chooseS_arrow in H2.
    rewrite chooseS_arrow in H2.
    dependent destruction H2...
  -
    rewrite chooseS_arrow in H2.
    rewrite chooseS_arrow in H2.
    dependent destruction H2...
    eapply IHNTyp; eauto.
    destruct m; simpl in *; eauto.
  -
    rewrite chooseS_mu in H3.
    rewrite chooseS_mu in H3.
    dependent destruction H3...
    pick fresh Y.
    rewrite_alist (nil ++ E).
    apply strengthening_sub with (X:=Y) (m:=bind_sub)...
    simpl.
    apply H0...
    rewrite <- chooseD_unfold...
    rewrite <- chooseD_unfold...
    apply H3...
    specialize (H3 0 Y).
    assert (Y \notin L0) by auto.
    apply H3 in H4.
    apply sub_regular in H4.
    destruct H4.
    inversion H4...
Qed.

(** Lemma 19 *)
Lemma negative_lemma :
  forall C E1 E2 X D m A B,
    Der m E1 A B E2 C D ->
    NTyp (E1++E2) m X A B ->
    X `in` fv_tt C \/ X `in` fv_tt D -> forall n,
        Sub E2 (subst_tt X (UnfoldS n X C) C) (subst_tt X (UnfoldS n X D) D) ->
        Sub E2 (subst_tt X C C) (subst_tt X D D) ->                                                
        Sub E2 (subst_tt X (UnfoldS n X D) D) (subst_tt X (UnfoldS n X C) C).
Proof with auto.
  intros.
  dependent induction H; eauto.
  -
    simpl in *.
    assert (Sub E A B) by auto.
    apply sub_regular in H4.
    destruct H4.
    destruct H5.
    apply wfs_type in H5.
    apply wfs_type in H6.
    apply gnegative_lemma with (C := A) (D := B) in H0...
    apply Sub_eq in H...
    subst...
  -
    apply IHDer...
    apply NMu with (n:=n) (L:={{X0}}\u fv_tt A \u fv_tt B).
    intros.
    rewrite_alist (nil ++ [(X1, bind_sub)] ++ E2 ++ E1).
    apply ntyp_rename with (X:=X0)...
    destruct H2.
    apply in_notin with (T:= fv_tt C)...
    apply in_notin with (T:= fv_tt D)...
Defined.

(** Lemma 16 part 1 *)
Lemma der_sub_whole : forall m E1 A B E2 C D, Der m E1 A B E2 C D -> Sub E2 C D.
  intros.
  induction H; eauto.
Defined.

(** Lemma 16 part 2 *)
Lemma der_sub_sub : forall m E1 A B E2 C D,
    Der m E1 A B E2 C D ->
    Sub (E1 ++ E2) A B (* SubSub m E1 E2 A B*).
Proof with auto.
  intros.
  induction H; try (destruct m); simpl in *; try solve [dependent destruction IHDer;auto]...
  -
    dependent destruction IHDer...
    pick fresh Y.
    rewrite_alist (nil ++ X ~ bind_sub ++ (E2 ++ E1)).
    apply subst_sub_unfoldn with (X:=Y)...
    simpl...
    apply H1...
    assert (Y \notin L) by auto.
    specialize (H1 0 Y H2).
    apply sub_regular in H1.
    destruct H1.
    inversion H1...
    simpl.
    constructor...
  -
    dependent destruction IHDer...
    pick fresh Y.
    rewrite_alist (nil ++ X ~ bind_sub ++ (E2 ++ E1)).
    apply subst_sub_unfoldn with (X:=Y)...
    simpl...
    apply H1...
    simpl.
    assert (Y \notin L) by auto.
    specialize (H1 0 Y H2).
    apply sub_regular in H1.
    destruct H1.
    inversion H1...
    constructor...
Qed.

(** Lemma 20 *)
Lemma sub_generalize_intensive : forall E1 E2 A B,
    Sub (E1 ++ E2) A B ->
    forall C D X m, Der m E1 A B E2 C D -> X `in` fv_tt C \/ X `in` fv_tt D -> forall n,
          Sub E2 (subst_tt X (UnfoldS n X C) C) (subst_tt X (UnfoldS n X D) D) ->
           Sub E2 (subst_tt X C C) (subst_tt X D D) ->
    Sub (E1 ++ E2) (chooseD n m X C D A) (chooseD n m X D C B).
Proof with auto.
  intros.
  dependent induction H; simpl in *; eauto.
  -
    destruct m; unfold chooseD; eauto.
  -
    destruct m; simpl in *; subst; eauto; destruct (X == X0); simpl in *; eauto.
    subst.
    eapply negative_lemma with (E1 := E1) in H1; eauto.
    rewrite_alist (nil ++ E1 ++ E2).
    apply Sub_weakening...
    rewrite_alist (nil ++ E1 ++ E2).
    apply Sub_weakening...    
  -
    destruct m; unfold chooseD; simpl in *; eauto.
    constructor...
    apply subst_tt_wfs...
    apply der_sub_whole in H1.
    apply sub_regular in H1.
    destruct H1.
    destruct H5.
    rewrite_alist (nil ++ E1 ++ E2).
    apply wfs_weakening...
    simpl.
    apply subst_tt_wfs...
    apply wfs_unfoldS...
    constructor...
    apply subst_tt_wfs...
    apply der_sub_whole in H1.
    apply sub_regular in H1.
    destruct H1.
    destruct H5.
    rewrite_alist (nil ++ E1 ++ E2).
    apply wfs_weakening...
    simpl.
    apply subst_tt_wfs...
    apply wfs_unfoldS...
  -
    rewrite chooseD_arrow.
    rewrite chooseD_arrow.
    constructor.
    apply DFun2 in H1; eauto.
    eapply IHSub1 in H3; eauto.
    destruct m; simpl in *; eauto.
    apply DFun1 in H1; eauto.
  -
    rewrite chooseD_mu.
    rewrite chooseD_mu.
    apply SA_rec with (L := L \u fv_tt A1 \u fv_tt A2 \u fv_tt C \u fv_tt D \u {{X}} \u dom E1 \u dom E2).
    intros.
    assert (X0 \notin L) by eauto.
    apply (H0 n0 X0 H6 (X0 ~ bind_sub ++ E1)) with (m:=m) in H3; eauto.
    simpl in H3.
    apply der_sub_whole in H1.
    apply sub_regular in H1.
    destruct H1.
    destruct H7.
    apply wfs_type in H8.
    apply wfs_type in H7.
    rewrite chooseS_unfold...
    rewrite chooseS_unfold...
Qed.    

(** Lemma 21 *)
Lemma sub_subst : forall E A B,
    Sub E A B -> forall X, 
    Sub E (subst_tt X A A) (subst_tt X B B) -> forall n, 
        Sub E (subst_tt X (UnfoldS n X A) A) (subst_tt X (UnfoldS n X B) B).
Proof with auto.
  intros.
  assert (E = nil ++ E) by eauto.
  rewrite H1.
  assert ((X \notin fv_tt(A) \u  fv_tt(B)) \/ (X \in fv_tt(A) \u fv_tt(B))).
  apply in_dec.
  destruct H2.
  - 
    apply notin_union in H2.
    destruct H2.
    assert (FX := H2).
    assert (FY := H3).
    apply subst_tt_fresh with (U := UnfoldS n X A) in H2.
    apply subst_tt_fresh with (U := UnfoldS n X B) in H3.
    apply subst_tt_fresh with (U := A) in FX.
    apply subst_tt_fresh with (U := B) in FY.
    rewrite <- FX in  *.
    rewrite <- FY in  *.
    rewrite <- H2.
    rewrite <- H3.
    simpl...
  -
    induction n; simpl in *; eauto.
    eapply sub_generalize_intensive with (m := Pos) (E1 := nil) in IHn; eauto.
    apply AtomSetImpl.union_1 in H2.
    destruct H2...
Qed.

Lemma completeness_wf : forall E A, WFS E A -> WF E A.
  intros.
  induction H; eauto.
  apply WF_rec with (L := L); intros; eauto.
  specialize (H0 0 X H1); simpl in *. eauto.
Defined.

(** Theorem 15 (Completeness of algorithmic subtyping) *)
Lemma completeness : forall E A B,
    Sub E A B -> sub E A B.
Proof with auto.
  intros.
  induction H; eauto.
  - constructor...
    apply completeness_wf; eauto.
  - apply sa_rec with (L := L); intros.
    specialize (H0 0 X H1); eauto.
    specialize (H0 1 X H1); eauto.
Defined.

Lemma wfs_generalize : forall n E X A,
    X \notin fv_tt A ->
    WFS E (open_tt A (typ_fvar X)) ->
    WFS E (unfoldT A X n).
Proof with auto.  
  induction n;intros...
  simpl.
  rewrite subst_tt_intro with (X:=X)...
  apply subst_tt_wfs...
Qed.


Lemma soundness_wf : forall E A,
    WF E A -> WFS E A.
Proof with auto.  
  intros.
  induction H...  
  apply WFS_rec with (L := L \u fv_tt A).
  intros...
  assert (X \notin L) by auto.
  specialize (H0 X H2).
  apply wfs_generalize...
Defined.

(** Theorem 22 (Soundness of algorithmic subtyping) *)
Lemma soundness : forall E A B,
    sub E A B -> Sub E A B.
Proof with auto.
  intros.
  induction H; eauto.
  -
    constructor...
    apply soundness_wf; eauto.
  -
    apply SA_rec with (L := L \u fv_tt A1 \u fv_tt A2); intros.
    assert (X \notin L) by auto.
    specialize (H0 X H4).
    specialize (H2 X H4).
    clear H H1.
    rewrite subst_tt_intro with (X:=X) in H2...
    remember (subst_tt X (open_tt A1 X) (open_tt A1 X)).
    rewrite subst_tt_intro with (X:=X) in H2...
    subst.
    assert (Sub (X ~ bind_sub ++ E) (open_tt A1 X) (open_tt A2 X)) by auto.
    remember (open_tt A1 X).
    remember (open_tt A2 X).
    destruct n.
    simpl...
    subst...
    apply sub_subst with (X:=X) (n:=n) in H0...
    rewrite <- unfoldS_unfoldT...
    rewrite <- unfoldS_unfoldT...
    simpl...
    subst...
Qed.

(** Theorem 13 (Reflexivity) *)
Lemma refl_algo : forall E A,
    wf_env E -> WFS E A -> sub E  A A.
Proof with auto.
  intros.
  induction H0...
  apply sa_rec with (L:=L \u dom E)...
  intros.
  assert (X \notin L) by auto.
  assert (wf_env ([(X, bind_sub)] ++ E)).
  constructor...
  specialize (H1 0 X H3 H4).
  simpl in H1...
  intros.
  assert (X \notin L) by auto.
  assert (wf_env ([(X, bind_sub)] ++ E)).
  constructor...
  specialize (H1 1 X H3 H4).
  simpl in H1...
Defined.

(** Lemma 12  *)
Lemma suba_regular : forall E A B,
    sub E A B -> wf_env E /\ WF E A /\ WF E B.
Proof with auto.
  intros.
  induction H...
  destruct IHsub1.
  destruct IHsub2.
  destruct H2.
  destruct H4.
  split...
  split.
  pick fresh X.
  specialize (H2 X).
  assert (X \notin L) by auto.
  apply H2 in H3.
  destruct H3.
  dependent destruction H3...
  split;apply WF_rec with (L:=L);intros;
  apply H0...
Qed.

Lemma trans_aux_algo: forall B E,
    WFS E B -> forall A C,
    sub E A B -> sub E B C -> sub E A C.
Proof with auto.
  intros B E H.
  dependent induction H;intros...
  -
    dependent destruction H0.
    dependent destruction H...
  -
    dependent destruction H.
    dependent destruction H0...
  -
    dependent destruction H0.
    dependent destruction H2...
  -
    dependent destruction H1.
    dependent destruction H2...
    constructor...    
    constructor...
    apply suba_regular in H1_...
    apply H1_.
    apply suba_regular in H1_0...
    apply H1_0.
  -
    dependent destruction H1.
    dependent destruction H3...
    constructor...
    apply WF_rec with (L:=L0)...
    intros...
    specialize (H1  X H5).
    apply suba_regular in H1...
    destruct H1...
    destruct H6...
    apply sa_rec with (L:=L \u L0 \u L1).
    intros.
    apply H0 with (n:=0);simpl...
    apply H1...
    apply H3...
    intros.
    apply H0 with (n:=1);simpl...
    apply H2...
    apply H4...
Qed.

(** Theorem 14 (Transitivity) *)
Lemma trans_algo: forall B E A C,
    sub E A B -> sub E B C -> sub E A C.
Proof with auto.
  intros.
  apply trans_aux_algo with (B:=B)...
  apply suba_regular in H0.
  destruct H0.
  destruct H1...
  apply soundness_wf...
Qed.

Lemma sub_replacing: forall E1 E2 A B X Y,
    sub (E1++ X ~ bind_sub ++E2) A B ->
    X <> Y ->
    wf_env (E1 ++ Y ~ bind_sub ++ E2) ->
    sub (E1++ Y ~ bind_sub ++E2) (subst_tt X Y A) (subst_tt X Y B).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros...
  -
    simpl.
    destruct (X0==X)...
    analyze_binds H0.
  -
    simpl.
    constructor...
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    apply completeness_wf.
    apply wfs_replacing...
    apply soundness_wf...
  -
    simpl.
    rewrite_alist (E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
  -
    simpl.
    apply sa_rec with (L:=L  \u {{X}} \u dom (E1 ++ [(Y, bind_sub)] ++ E2) )...
    intros.
    rewrite  subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
    intros.
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite <- subst_tt_open_tt...
    rewrite <- subst_tt_open_tt...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H2...
    rewrite_alist ([(X0, bind_sub)] ++ E1 ++ [(Y, bind_sub)] ++ E2).
    constructor...
Qed.

Lemma open_subst_twice : forall A (X Y:atom),
    X \notin fv_tt A ->
    subst_tt X Y (open_tt A (open_tt A X)) = (open_tt A (open_tt A Y)).
Proof with auto.
  intros.
  remember (open_tt A X).
  rewrite subst_tt_open_tt...
  rewrite <- subst_tt_fresh...
  f_equal...
  subst.
  rewrite <- subst_tt_intro...
Qed.  
