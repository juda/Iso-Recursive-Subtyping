Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export subtyping.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  WFS E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  WFS E U.
Proof with auto.
  induction 1; intros J; analyze_binds J...
  apply IHwf_env in BindsTac.
  rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
  apply wfs_weakening...
  injection BindsTacVal; intros; subst...
  rewrite_alist (nil ++ [(x0, bind_typ T)] ++ E).
  apply wfs_weakening...
  rewrite_alist (nil ++ [(x0, bind_typ T)] ++ E).
  apply wfs_weakening...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 WFS (F ++ x ~ bind_typ U ++ E) T ->
 WFS (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  analyze_binds H...
  apply WFS_rec with (L:=L).
  intros.
  rewrite_alist (([(X, bind_sub)] ++ F) ++ E).
  apply H0...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.







Lemma wfs_open_type2: forall A G,
    WFS G (typ_mu A) -> WFS G (open_tt A (typ_mu A)).
Proof with auto.
  intros.
  dependent destruction H.
  pick fresh X.
  rewrite subst_tt_intro with (X:=X)...
  rewrite_alist (nil ++ E).
  apply subst_tt_wfs2...
  simpl.
  apply WFS_rec with (L:=L)...
  simpl...
  specialize (H 0 X).
  unfold unfoldT in H.
  rewrite_alist ([(X, bind_sub)] ++ E)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ WFS E T.
Proof with auto.
  intros.
  induction H...
  -
    repeat split...
    apply wf_typ_from_binds_typ with (x:=x)...
  -
    pick fresh Y.
    assert (Y \notin L) by auto.
    apply H0 in H1.
    destruct H1.
    split.
    dependent destruction H1...
    destruct H2.
    split...
    apply lc_abs with (L:=L)...
    intros.
    apply H0...
    dependent destruction H1...
    apply wfs_type in H2...
    constructor...
    dependent destruction H1...
    rewrite_alist (nil ++ G).
    apply wf_typ_strengthening with (x:=Y) (U:=T1)...
  -
    destruct IHtyping1...
    destruct H2.
    dependent destruction H3.
    destruct IHtyping2.
    destruct H4.
    repeat split...
  -
    destruct IHtyping.
    destruct H2.
    split...
    split...
    apply lc_fold...
    apply wfs_type with (E:=G)...
  -
    destruct IHtyping.
    destruct H1.
    split...
    split...
    apply lc_unfold...
    apply wfs_type with (E:=G)...
    apply wfs_open_type2...
  -
    destruct IHtyping.
    destruct H2.
    apply sub_regular in H0.
    repeat split...
    apply H0...
Qed.    
    
Lemma typing_weakening: forall E1 E2 E3 e T,
    typing (E1 ++ E3) e T ->
    wf_env (E1 ++ E2 ++ E3) ->
    typing (E1 ++ E2 ++ E3) e T.
Proof with simpl_env; eauto using wf_typ_from_wf_env_typ.
  intros.

  remember (E1 ++ E3) as Ht.
  generalize dependent E1.
  induction H;intros;subst...
  -
    apply typing_abs with (L:=L \u dom E1 \u dom E2 \u dom E3).
    intros.
    rewrite_alist (([(x, bind_typ T1)] ++ E1) ++ E2 ++ E3).
    apply H0...
    rewrite_alist ([(x, bind_typ T1)] ++ E1 ++ E2 ++ E3).
    constructor...
    assert (x \notin L) by auto.
    apply H in H3.
    apply typing_regular  in H3.
    destruct H3.
    dependent destruction H3.
    apply wfs_weakening...
  -
    apply typing_fold...
    apply wfs_weakening...
  -
    apply typing_sub with (S:=S).
    apply IHtyping...
    apply Sub_weakening...
Qed.

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma strengthening_wfs_typ: forall E1 E2 S X T,
    WFS (E1 ++ X ~ bind_typ S ++ E2) T->
    WFS (E1 ++ E2) T.
Proof with auto.
  intros.
  dependent induction H...
  -
    analyze_binds H...
  -
    constructor...
    apply IHWFS1 with (X0:=X) (S0:=S)...
    apply IHWFS2 with (X0:=X) (S0:=S)...
  -
    apply WFS_rec with (L:=L \u {{X}}).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (S0:=S)...
Qed.    

Lemma strengthening_sub_typ: forall E1 E2 A B X T,
    Sub (E1 ++ X ~ bind_typ T ++ E2) A B ->
    wf_env  (E1 ++ E2 ) ->
    Sub (E1 ++ E2) A B.
Proof with auto.
  intros.
  dependent induction H...
  -
    constructor...
    analyze_binds H0...
  -
    constructor...
    apply strengthening_wfs_typ with (X:=X) (S:=T) ...
  -
    constructor...
    apply IHSub1 with (X0:=X) (T0:=T)...
    apply IHSub2 with (X0:=X) (T0:=T)...
  -
    apply SA_rec with (L:=L \u {{X}} \u dom (E1 ++ E2)).
    intros.
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ E2).
    apply H0 with (X1:=X) (T0:=T)...
    constructor...
Qed.

(** Lemma 9 *)
Lemma typing_through_subst_ee : forall F U E x T e u,
  typing (F ++ x ~ bind_typ U ++ E) e T ->
  typing E u U ->
  typing (F ++ E) (subst_ee x u e) T.
Proof with eauto.
  intros.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction H;intros;subst;simpl in *...
  -
    constructor...
    apply wf_env_strengthening in H...
  -
    destruct (x0==x)...
    subst...
    analyze_binds_uniq H1...
    apply uniq_from_wf_env...
    injection BindsTacVal; intros; subst.
    rewrite_alist (nil ++ F ++ E).
    apply typing_weakening...
    simpl.
    apply wf_env_strengthening in H...
    analyze_binds H1...
    constructor...
    apply wf_env_strengthening in H...
    constructor...
    apply wf_env_strengthening in H...
  -
    apply typing_abs with (L:=L \u {{x}})...
    intros.
    rewrite subst_ee_open_ee_var...
    rewrite_alist (([(x0, bind_typ T1)] ++ F) ++ E).
    apply H1...
    apply typing_regular in H0...
    apply H0.
  -
    apply typing_fold...
    rewrite_alist (WFS (F ++ (x ~ bind_typ U) ++ E) (typ_mu A)) in H1.
    apply wf_typ_strengthening in H1...
  -
    apply typing_sub with (S:=S)...
    rewrite_alist (F ++ (x ~ bind_typ U) ++ E) in H1.
    apply typing_regular in H.
    destruct H.    
    apply strengthening_sub_typ in H1...
    apply wf_env_strengthening with (x:=x) (T:=U)...
Qed.


                                  
Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, Sub E T (typ_arrow U1 U2) ->
     Sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing (x ~ bind_typ S1 ++ E) (open_ee e1 x) S2 /\ Sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  -
    inversion Sub; subst.
    split...
    exists T2. exists L...
  -
    assert (definition.Sub G S (typ_arrow U1 U2)).
    apply Transitivity with (B:=T)...
    assert (typing G (exp_abs S1 b1) (typ_arrow U1 U2)).
    apply typing_sub with (S:=S)...
    dependent destruction H2...
Qed.


Lemma typing_inv_fold: forall S G T v,
    typing G (exp_fold T v) S ->
    forall U, Sub G S (typ_mu U) ->
    (exists T', typing G v (open_tt T' (typ_mu T')) /\ Sub G (open_tt T' (typ_mu T')) (open_tt U (typ_mu U))).
Proof with auto.
  intros.
  generalize dependent U.
  dependent induction H;intros...
  -
    exists A...
    split...
    apply unfolding_lemma...
  -
    specialize (IHtyping T v).
    assert (exp_fold T v = exp_fold T v) by auto.
    apply IHtyping with (U:=U) in H2...
    apply Transitivity with (B:=T0)...
Qed.
    
(** Theorem 10 (Preservation) *)
Lemma preservation : forall E e e' T,
    typing E e T ->
    step e e' ->
    typing E e' T.
Proof with auto.
  intros.
  generalize dependent e'.
  dependent induction H;intros;try solve [dependent destruction H1;auto|inversion H0]...
  -
    dependent destruction H1...
    +
      dependent destruction H.
      pick fresh Y.
      rewrite subst_ee_intro with (x:=Y)...
      rewrite_alist (nil ++ G).
      apply typing_through_subst_ee with (U:=T1)...
      apply H...
      apply typing_inv_abs with (U1:=T1) (U2:=T2) in H...
      destruct H.
      destruct H4.
      destruct H4.
      pick fresh Y.
      rewrite subst_ee_intro with (x:=Y)...
      rewrite_alist (nil ++ G).
      apply typing_through_subst_ee with (U:=T)...
      specialize (H4 Y).
      assert (Y \notin x0) by auto.
      apply H4 in H5.
      destruct H5.
      apply typing_sub with (S:=x)...
      apply Sub_weakening...
      apply typing_regular in H5.
      destruct H5...
      apply typing_sub with (S:=T1)...
    +
      apply typing_app with (T1:=T1)...
    +
      apply typing_app with (T1:=T1)...
  -
    dependent destruction H0...
    dependent destruction H...
    apply typing_inv_fold with (U:=T) in H...
    destruct H...
    destruct H.
    apply typing_sub with (S:=open_tt x (typ_mu x))...
  -
    apply typing_sub with (S:=S)...
Qed.

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].

    inversion H; subst; eauto.
Qed.

    
    
Lemma canonical_form_fold : forall e U,
  value e ->
  typing empty e (typ_mu U) ->
  exists V, exists e1, (Sub empty (typ_mu V) (typ_mu U) /\ value e1 /\ e = exp_fold (typ_mu V) e1).
Proof with auto.
  intros e U Val Typ.
  remember empty as E.
  remember (typ_mu U) as T.
  assert (WFS E T).
  apply typing_regular in Typ.
  destruct Typ.
  destruct H0...
  revert U HeqT HeqE.
  induction Typ; intros U EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  -
    dependent destruction Val.
    exists A...
    exists e...
    repeat split...
    apply refl...
  -
    inversion H; subst; eauto.
    dependent destruction H0.
    apply IHTyp with (U:=A1) in Val...
    destruct Val.
    destruct H1.
    exists x.
    exists x0.
    destruct H1.
    destruct H2.
    repeat split...
    apply Transitivity with (B:=typ_mu A1)...
    apply SA_rec with (L:=L)...
    apply typing_regular in Typ.
    apply Typ.
Qed.

(** Theorem 11 (Progress) *)
Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof with eauto.
  intros.
  dependent induction H...
  -
    inversion H0...
  -
    left.
    constructor.
    pick fresh Y.
    assert (Y \notin L) by auto.
    apply H in H1...
    apply typing_regular in H1.
    destruct H1.
    destruct H2.
    apply lc_abs with (L:=L).
    intros.
    apply H in H4.
    apply typing_regular in H4.
    apply H4.
    apply wf_typ_from_wf_env_typ in H1.
    apply wfs_type with (E:=empty)...
  -
    right.
    assert (empty ~= empty) by auto.
    apply IHtyping1 in H1.
    destruct H1...
    assert (empty ~= empty) by auto.
    apply IHtyping2 in H2...
    destruct H2...
    apply canonical_form_abs with (U1:=T1) (U2:=T2) in H1...
    destruct H1.
    destruct H1.
    exists (open_ee x0 e2).
    subst.
    apply step_beta...
    apply typing_regular in H.
    apply H.
    destruct H2.
    exists (exp_app e1 x).
    apply step_app2...
    destruct H1.
    exists (exp_app x e2).
    apply step_app1...
    apply typing_regular in H0.
    apply H0.
  -
    assert (empty ~= empty) by auto.
    apply IHtyping in H1.
    destruct H1.
    left.
    constructor...
    apply wfs_type in H0...
    right.
    destruct H1.
    exists (exp_fold (typ_mu A) x).
    constructor...
    apply typing_regular in H.
    destruct H.
    destruct H2.
    apply wfs_type in H0...
  -
    assert (empty ~= empty) by auto.
    apply IHtyping in H0.
    right.
    destruct H0...
    +
      apply canonical_form_fold with (U:=T) in H0...
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      exists x0...
      rewrite H2.
      apply step_fld...
      apply sub_regular in H0.
      apply wfs_type with (E:=empty)...
      apply H0.
      apply typing_regular in H.
      apply wfs_type with (E:=empty)...
      apply H.
    +
      destruct H0.
      exists (exp_unfold (typ_mu T) x).
      apply step_unfold...
      apply typing_regular in H...
      apply wfs_type with (E:=empty)...
      apply H.
Qed.
