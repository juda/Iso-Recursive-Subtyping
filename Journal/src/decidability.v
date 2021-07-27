Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Export subtyping2.


  

Lemma decidability_aux : forall E A B,
    WFS E A ->
    WFS E B ->
    wf_env E ->
    (Sub E A B \/ ~ Sub E A B) /\
    (Sub E B A \/ ~ Sub E B A).
Proof with auto.
  intros.
  generalize dependent B.
  induction H;intros...
  -
    induction H0;auto;try solve [split;auto;right;auto;intros v;inversion v]...
    split...
    right...
    intros v.
    inversion v...
    left...
    constructor...
    apply WFS_rec with (L:=L)...
  -
    induction H0;auto;try solve [split;auto;right;auto;intros v;inversion v]...
  -
    induction H0;auto;try solve [split;auto;right;auto;intros v;inversion v]...
    destruct (X==X0)...
    subst...
    split...
    right...
    intros v...
    inversion v...
    right...
    intros v...
    inversion v...
  -
    induction H2;auto;try solve [split;auto;right;auto;intros v;inversion v]...
    specialize (IHWFS1 H1 _ H2_).
    destruct IHWFS1.
    specialize (IHWFS2 H1 _ H2_0).
    destruct IHWFS2.
    split...
    +
      clear H2 H5.
      destruct H3;destruct H4;try solve [right;intros v;inversion v;auto]...
    +
      clear H3 H4.
      destruct H2;destruct H5;try solve [right;intros v;inversion v;auto]...
  -
    induction H2;auto;try solve [split;auto;right;auto;intros v;inversion v]...
    +
      split...
      left...
      constructor...
      apply WFS_rec with (L:=L)...
      right.
      intros v.
      inversion v...
    +
      clear H3.
      pick fresh X.
      assert (X \notin L) by auto.
      assert (wf_env ([(X, bind_sub)] ++ E)) by auto.
      assert (X \notin L0) by auto.
      assert ((forall n, (Sub ([(X, bind_sub)] ++ E) (unfoldT A X n) (unfoldT A0 X n) \/
                         ~ Sub ([(X, bind_sub)] ++ E) (unfoldT A X n) (unfoldT A0 X n))) /\
              (forall n, (Sub ([(X, bind_sub)] ++ E) (unfoldT A0 X n) (unfoldT A X n) \/
        ~ Sub ([(X, bind_sub)] ++ E) (unfoldT A0 X n) (unfoldT A X n)))).
      split.
      intros.
      specialize (H2 n _ H5).
      specialize (H0 n X H3 H4 _ H2)...
      destruct H0...
      intros.
      specialize (H2 n _ H5).
      specialize (H0 n X H3 H4 _ H2)...
      destruct H0...
      destruct H6.
      split.
      *
        clear H7.
        assert (H7:= H6).
        specialize (H6 0).
        specialize (H7 1).
        destruct H6;destruct H7;simpl in *.
        --
          left.
          apply soundness.
          apply sa_rec with (L:=L \u {{X}} \u dom E).
          intros.
          rewrite subst_tt_intro with (X:=X)...
          remember (subst_tt X X0 (open_tt A X)).
          rewrite subst_tt_intro with (X:=X)...
          subst.
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
          apply sub_replacing...
          apply completeness...
          simpl...
          constructor...
          intros.
          rewrite <- open_subst_twice with (X:=X)...
          remember (subst_tt X X0 (open_tt A (open_tt A X))).
          rewrite <- open_subst_twice with (X:=X)...
          subst.
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
          apply sub_replacing...
          apply completeness...
          simpl...
          constructor...
        --
          right.
          intros v.
          dependent destruction v.
          apply H7.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 1 Y H9).
          simpl in H8.
          rewrite <- open_subst_twice with (X:=Y)...
          remember (subst_tt Y X (open_tt A (open_tt A Y))).
          rewrite <- open_subst_twice with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
        --
          right.
          intros v.
          dependent destruction v.
          apply H6.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 0 Y H9).
          simpl in H8.
          rewrite subst_tt_intro with (X:=Y)...
          remember (subst_tt Y X (open_tt A Y)).
          rewrite subst_tt_intro with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
        --
          right.
          intros v.
          dependent destruction v.
          apply H6.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 0 Y H9).
          simpl in H8.
          rewrite subst_tt_intro with (X:=Y)...
          remember (subst_tt Y X (open_tt A Y)).
          rewrite subst_tt_intro with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
      *
        clear H6.
        assert (H6:= H7).
        specialize (H6 0).
        specialize (H7 1).
        destruct H6;destruct H7;simpl in *.
        --
          left.
          apply soundness.
          apply sa_rec with (L:=L \u {{X}} \u dom E).
          intros.
          rewrite subst_tt_intro with (X:=X)...
          remember (subst_tt X X0 (open_tt A0 X)).
          rewrite subst_tt_intro with (X:=X)...
          subst.
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
          apply sub_replacing...
          apply completeness...
          simpl...
          constructor...
          intros.
          rewrite <- open_subst_twice with (X:=X)...
          remember (subst_tt X X0 (open_tt A0 (open_tt A0 X))).
          rewrite <- open_subst_twice with (X:=X)...
          subst.
          rewrite_alist (nil ++ [(X0, bind_sub)] ++ E).
          apply sub_replacing...
          apply completeness...
          simpl...
          constructor...
        --
          right.
          intros v.
          dependent destruction v.
          apply H7.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 1 Y H9).
          simpl in H8.
          rewrite <- open_subst_twice with (X:=Y)...
          remember (subst_tt Y X (open_tt A0 (open_tt A0 Y))).
          rewrite <- open_subst_twice with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
        --
          right.
          intros v.
          dependent destruction v.
          apply H6.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 0 Y H9).
          simpl in H8.
          rewrite subst_tt_intro with (X:=Y)...
          remember (subst_tt Y X (open_tt A0 Y)).
          rewrite subst_tt_intro with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
        --
          right.
          intros v.
          dependent destruction v.
          apply H6.
          pick fresh Y.
          assert (Y \notin L1) by auto.
          specialize (H8 0 Y H9).
          simpl in H8.
          rewrite subst_tt_intro with (X:=Y)...
          remember (subst_tt Y X (open_tt A0 Y)).
          rewrite subst_tt_intro with (X:=Y)...
          rewrite_alist (nil ++ [(X, bind_sub)] ++ E).
          subst.
          apply Sub_replacing...
Qed.

Theorem decidability: forall E A B,
    WF E A ->
    WF E B ->
    wf_env E ->
    (Sub E A B \/ ~ Sub E A B).
Proof with auto.
  intros.
  eapply decidability_aux...
  apply soundness_wf...
  apply soundness_wf...
Qed.
