Require Import Metalib.Metatheory.
Require Import Program.Equality.
Require Import NominalUnfolding.
Require Export Coq.micromega.Lia.
Import Nominal.
Import String.
Import List.


(* constants must be in the left *)
Fixpoint weight (T:typ) : nat :=
  match T with
  | typ_nat => 0
  | typ_top => 0
  | typ_fvar _ => 0
  | typ_bvar _ => 0
  | typ_arrow A B => 1 + weight A + weight B
  | typ_rcd _ A => 1 + weight A
  | typ_mu A => 1 + weight A
  end.

Lemma in_fv_tt_dec: forall X A,
    {X \in fv_tt A} + {X \notin fv_tt A}.
Proof with auto.
  intros.
  induction A...
  -
    destruct (X==a)...
    left;simpl.
    subst...
  -
    destruct IHA1;destruct IHA2;simpl...
Qed.


Lemma binds_dec: forall E X,
    {binds X bind_sub E} + {~ binds X bind_sub E}.
Proof with auto.
  induction E...
  intros.
  destruct a.
  destruct b.
  destruct (X==a)...
  destruct IHE with (X:=X)...
  right.
  intros v.
  apply n0.
  analyze_binds v.
Qed.

Lemma weight_open_tt_equal: forall A (X:atom),
    weight (open_tt A X) = weight A.
Proof with auto.
  intros.
  unfold open_tt.
  generalize 0.
  induction A;intros;simpl in *...
  destruct (n0==n)...
Qed.

Lemma WF_replacing: forall E1 E2 T X Y,
    WF (E1++ X ~ bind_sub ++E2) T ->
    X <> Y ->
    WF (E1++ Y ~ bind_sub ++E2) (subst_tt X Y T).
Proof with auto.
  intros.
  generalize dependent Y.
  dependent induction H;intros;simpl;try solve [rewrite_alist (E1 ++ Y ~ bind_sub ++ E2);constructor;auto]...
  -
    destruct (X0==X)...
    constructor.
    analyze_binds H.
  -
    apply WF_rec with (L:=L \u {{X}});intros.
    rewrite  subst_tt_open_tt_var...
    rewrite_alist (([(X0, bind_sub)] ++ E1) ++ Y ~ bind_sub ++ E2).
    apply H0...
Qed.

Lemma WF_replacing_var: forall E T X Y,
    WF (X ~ bind_sub ++E) (open_tt T X) ->
    X \notin fv_tt T \u {{Y}} ->
    WF (Y ~ bind_sub ++E) (open_tt T Y).
Proof with auto.
  intros.
  rewrite_alist (nil ++ [(Y, bind_sub)] ++ E).
  rewrite subst_tt_intro with (X:=X)...
  apply WF_replacing...
Qed.

Lemma WF_dec_aux: forall k E A,
    weight A <= k ->
    {WF E A } + {~WF E A}.
Proof with auto.
  induction k;intros...
  -
    induction A;simpl in *...
    +
      right...
      intros v.
      inversion v.
    +
      pose binds_dec as Q.
      destruct Q with (E:=E) (X:=a)...
      right.
      intros v.
      apply n.
      dependent destruction v...
    +
      lia.
    +
      lia.
    +
      lia.
  -
    induction A;simpl in *...
    +
      right...
      intros v.
      inversion v.
    +
      pose binds_dec as Q.
      destruct Q with (E:=E) (X:=a)...
      right.
      intros v.
      apply n.
      dependent destruction v...
    +
      pick fresh X.
      destruct IHk with (E:=(X,bind_sub) ::E) (A:=open_tt A X).
      *
        rewrite weight_open_tt_equal...
        apply le_S_n...
      *
        left.
        apply WF_rec with (L:=fv_tt A \u dom E \u {{X}});intros...
        apply WF_replacing_var with (X:=X)...
      *
        right.
        intros v.
        apply n.
        dependent destruction v.
        pick fresh Y.
        apply WF_replacing_var with (X:=Y)...
    +
      apply le_S_n in H...
      destruct IHA1;destruct IHA2;simpl;try lia...
      right.
      intros v.
      dependent destruction v.
      apply n...
      right.
      intros v.
      dependent destruction v.
      apply n...
      right.
      intros v.
      dependent destruction v.
      apply n...
    +
      destruct IHA...
      lia.
      right.
      intros v.
      dependent destruction v.
      apply n...
Qed.    
  
Lemma WF_dec: forall E A,
    {WF E A } + {~WF E A}.
Proof with auto.
  intros.
  apply WF_dec_aux with (k:=weight A)...
Qed.

Lemma WFS_dec: forall E A,
    {WFS E A } + {~WFS E A}.
Proof with auto.
  intros.
  pose WF_dec as Q.
  destruct Q with (E:=E) (A:=A).
  left.
  apply wf_to_wfs...
  right.
  intros v.
  apply n.
  apply wfs_to_wf...
Qed.

Lemma in_dom_dec: forall (E:env) X,
    {X \in dom E} + {X \notin dom E}.
Proof with auto.
  induction E;intros;simpl...
  destruct a...
  destruct IHE with (X:=X)...
  destruct (X==a);subst...
Qed.

  
Lemma wf_env_dec: forall E,
    {wf_env E} + {~wf_env E}.
Proof with auto.
  intros.
  induction E...
  destruct IHE.
  -
    destruct a.
    destruct b.
    rewrite_env ([(a, bind_sub)] ++ E).
    pose in_dom_dec as Q.
    destruct Q with (E:=E) (X:=a)...
    right.
    intros v.
    dependent destruction v.
    apply H...
  -
    destruct a.
    destruct b.
    right.
    intros v.
    dependent destruction v.
    apply n...
Qed.


Ltac solve_right_dec := right;intro v;inversion v;auto.
Ltac solve_top_dec E := pose wf_env_dec as Q;destruct Q with (E:=E);try solve [left;auto|solve_right_dec].
Ltac solve_top_wfs_dec E A1 := pose WFS_dec as Qt;destruct Qt with (E:=E) (A:=A1);try solve [solve_top_dec E|right;intros v;dependent destruction v;auto].

Definition menv := list (nat * nat).
Notation empty_menv := (@nil (nat * nat)).

Fixpoint find {A:Type} (n:nat) (E: list (nat * A)) :=
  match E with
  | (k, v) :: E' =>
        if (n == k) then Some v else find n E'
  | nil => None
  end.

Fixpoint bindings_rec (E: menv) (n: nat) (T:typ) : nat :=
  match T with
  | typ_nat => 0
  | typ_top => 0
  | typ_fvar _ => 0
  | typ_bvar m => 
      match find (n - m) E with
      | Some k => k
      | None => 0 
      end 
  | typ_arrow A B => S (max (bindings_rec E n A) (bindings_rec E n B))
  | typ_rcd _ A => S (bindings_rec E n A)
  | typ_mu A => 
       let i := bindings_rec ((S n , 0) :: E) (S n) A in
       S (bindings_rec ((S n, S i) :: E) (S n) A)
  end.

Definition bindings T := bindings_rec nil 0 T.

Definition zero := 0.

Lemma bindings_find_in: forall (E1 E2:menv) k,
    find 0 (E1 ++ E2) = None ->
    find 0 (E1 ++ (0, k) :: E2) = Some k.
Proof with auto.
  induction E1...
  intros.
  destruct a.
  simpl in *.
  destruct n;simpl in *...
  inversion H.
Qed.

Lemma bindings_find_notin: forall (E1 E2:menv) k (n:nat),
    find (S n) (E1 ++ (0, k) :: E2) = find (S n) (E1++E2).
Proof with auto.
  induction E1;intros...
  -
    destruct a...
    simpl...
    destruct (S n == n0)...
Qed.

Inductive WFC :  typ -> nat -> Prop :=
| WC_nat: forall k,
    WFC typ_nat k
| WF_top: forall k,
    WFC typ_top k
| WF_fvar: forall X k,
    WFC (typ_fvar X) k
| WF_bvar: forall b k,
    b <= k ->
    WFC (typ_bvar b) k
| WF_arrow: forall A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_arrow A B) k
| WF_rec: forall A n,
    WFC A (S n) ->
    WFC (typ_mu A) n
| WF_rcd: forall l A k,
    WFC A k ->
    WFC (typ_rcd l A) k
.
Inductive WFD :  typ -> nat -> Prop :=
| WD_nat: forall k,
    WFD typ_nat k
| WD_top: forall k,
    WFD typ_top k
| WD_fvar: forall X k,
    WFD (typ_fvar X) k
| WD_bvar: forall b k,
    b < k ->
    WFD (typ_bvar b) k
| WD_arrow: forall A B k,
    WFD A k ->
    WFD B k ->
    WFD (typ_arrow A B) k
| WD_rec: forall A n,
    WFD A (S n) ->
    WFD (typ_mu A) n
| WD_rcd: forall l A k,
    WFD A k ->
    WFD (typ_rcd l A) k
.


Inductive WFE : menv -> nat -> Prop :=
| WFE_empty:
    WFE nil 0
| WFE_cons: forall  b E k,
    WFE E k ->
    find (S k) E = None ->
    WFE ((S k,b)::E) (S k).

Hint Constructors WFC WFD WFE: core.

Lemma neq_minus: forall k n,
    n <= k ->
    n <> k ->
    exists q, k - n = S q.
Proof with auto.
  induction k;intros...
  inversion H...
  destruct H0...
  induction n...
  exists k...
  destruct IHk with (n:=n)...
  lia.
  exists x...
Qed.

Lemma neq_minus_v2: forall k n,
    n < k ->
    exists q, k - n = S q.
Proof with auto.
  induction k;intros...
  inversion H...
  induction n...
  exists k...
  destruct IHk with (n:=n)...
  lia.
  exists x...
Qed.

Fixpoint addone (E:menv) : menv :=
  match E with
  | nil => nil
  | (a,b)::E' => (S a,b)::(addone E')
  end.

Lemma find_add_eq: forall E k,
    find k E = find (S k) (addone E).
Proof with auto.
  induction E;intros...
  destruct a...
  simpl...
  destruct (k == n) ...
  destruct (S k == S n)...
  destruct n1...
  destruct (S k == S n)...
  destruct n1...
Qed.

Lemma find_add: forall E k b,
    k >= b ->
    find (k - b) E = find (S k - b) (addone E).
Proof with auto using find_add_eq.
  induction E;intros...
  -
    destruct a...
    assert (addone ((n, n0) :: E) = (S n, n0) :: addone E) by auto.
    rewrite H0.
    assert (S k - b = S (k-b)) by lia.
    rewrite H1.
    destruct (k-b);simpl...
    destruct (0==n)...
    destruct (1== S n)...
    destruct n1...
    destruct (1== S n)...
    destruct n1...
    destruct (S n1 == n)...
    destruct (S (S n1) == S n)...
    destruct n2...
    destruct (S (S n1) == S n)...
    destruct n2...
Qed.

    
Lemma bindings_add : forall E n A,
    WFC A n ->
    bindings_rec E n A = bindings_rec (addone E) (S n) A.
Proof with auto.
  intros.
  generalize dependent E.
  induction H;intros;try solve [simpl;auto]...
  -
    simpl.
    rewrite find_add...
  -
    simpl...
    f_equal...
    assert (bindings_rec ((S (S n), 0) :: addone E) (S (S n)) A =
            bindings_rec (addone ((S n, 0)::E)) (S (S n)) A) by auto.
    rewrite H0...
    rewrite <- IHWFC ...
    remember (S (bindings_rec ((S n, 0) :: E) (S n) A)).
    assert ((S (S n), n0) :: addone E = addone ((S n,n0)::E)) by auto.
    rewrite H1.
    rewrite <- IHWFC...
Qed.

Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat      
  | typ_top         => typ_top              
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X 
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T        => typ_mu (close_tt_rec (S K) Z T)
  | typ_rcd l T => typ_rcd l (close_tt_rec K Z T)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

Lemma close_wfc : forall A X,
    WFC A 0 ->
    WFC (close_tt A X) 0.
Proof with auto.  
  intros A.
  unfold close_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (a==X)...
Qed.

Lemma WFC_add_one : forall A k,
    WFC A k -> WFC A (S k).
Proof with auto.
  intros.
  induction H...
Qed.

Lemma close_wfd : forall A X,
    WFD A 0 ->
    WFD (close_tt A X) 1.
Proof with auto.  
  intros A.
  unfold close_tt.
  generalize 0.
  induction A;intros;try solve [dependent destruction H;simpl in *;auto]...
  -
    simpl...
    destruct (a==X)...
Qed.

Lemma close_open_reverse_rec: forall T X,
    (X \notin fv_tt T) -> forall k, T = close_tt_rec k X (open_tt_rec k (typ_fvar X) T).
Proof with auto.
  intros T.
  induction T;intros;simpl in *;try solve [f_equal;auto]...
  -   
    destruct (k==n)...
    simpl...
    destruct (X==X)...
    destruct n0...
  -
    destruct (a==X)...
    apply notin_singleton_1 in H...
    destruct H...
Qed.

Lemma close_open_reverse: forall T X,
    (X \notin fv_tt T) ->  T = close_tt (open_tt T (typ_fvar X)) X.
Proof with auto.
  intros.
  apply close_open_reverse_rec...
Qed.

Lemma close_type_wfc: forall A,
    type A -> WFC A 0.
Proof with auto.
  intros.
  induction H;intros...
  constructor...
  apply WFC_add_one.
  pick fresh X.
  specialize_x_and_L X L.
  apply close_wfc with (X:=X) in H0.
  rewrite <- close_open_reverse in H0...
Qed.

Lemma close_type_wfd: forall A,
    type A -> WFD A 0.
Proof with auto.
  intros.
  induction H;intros...
  pick fresh X.
  specialize_x_and_L X L.
  constructor...
  apply close_wfd with (X:=X) in H0.
  rewrite <-close_open_reverse in H0...
Qed.


Lemma type_open_tt_WFC :forall T X,
    X \notin fv_tt T ->
    type (open_tt T X) ->
    WFC T 0.
Proof with auto.
  intros.
  apply close_type_wfc in H0.
  apply close_wfc with (X:=X) in H0...
  rewrite <- close_open_reverse in H0... 
Qed.


Lemma find_former: forall (E2 E1:list (nat * nat)) (k:nat),
    (exists p, In (k,p) E1) ->
    find k E1 = find k (E1++E2).
Proof with auto.
  induction E1;intros...
  -
    inversion H...
    inversion H0.
  -
    destruct a.
    destruct H.
    destruct (k==n);subst...
    +
      simpl...
      destruct (n==n)...
      destruct n1...
    +
      simpl.
      destruct (k == n)...
      apply in_inv in H.
      destruct H...
      dependent destruction H...
      destruct n1...
      apply IHE1...
      exists x...
Qed.


Lemma minus_in_for_bindings: forall E ( n k:nat),
    (forall q, exists p, q < n -> In (n - q, p) E) ->
    (forall q, exists p, q < S n -> In (S n - q, p) ((S n, k) :: E)).
Proof with auto.
  intros.
  destruct n.
  -
    destruct q.
    exists k...
    intros.
    simpl...
    exists 0...
    intros.
    lia.
  -
    destruct q...
    exists k.
    intros.
    simpl...
    destruct H with (q:=q)...
    exists x.
    intros.
    assert (S (S n) - S q = S n - q).
    lia.
    rewrite H2.
    apply in_cons...
    apply H0...
    lia.
Qed.    

Lemma bindings_close_env_aux: forall A k,
    WFD A k->    forall E1 E2 ,
    (forall q, exists p, q < k -> In (k-q,p) E1) -> 
    bindings_rec (E1++E2) k A = bindings_rec E1 k A.
Proof with eauto.
  intros A k H.
  induction H;intros;try solve [simpl in *;auto]...
  -
    simpl...
    assert (find (k - b) E1 = find (k - b) (E1++E2)).
    {
      rewrite find_former with (E2:=E2)...
      destruct H0 with (q:=b)...
    }
    rewrite H1...
  -
    simpl.
    f_equal.
    remember (bindings_rec ((S n, 0) :: E1 ++ E2) (S n) A).
    rewrite_env (((S n, S n0) :: E1) ++ E2).
    rewrite IHWFD...
    subst.
    rewrite_env (((S n, 0) :: E1) ++ E2).
    rewrite IHWFD...
    intros.
    apply minus_in_for_bindings...
    intros.
    apply minus_in_for_bindings...
Qed.

Lemma bindings_close_env: forall A E,
    type A-> 
    bindings_rec E 0 A = bindings_rec nil 0 A.
Proof with eauto.
  intros.
  rewrite_env (nil++E).
  rewrite_env (nil ++ empty_menv).
  apply bindings_close_env_aux...
  apply close_type_wfd...
  intros.
  exists 0.
  intros.
  lia.
Qed.

Fixpoint minusk (E:menv) (k:nat): menv :=
  match E with
  | nil => nil
  | (a,b)::E' => (a - k,b)::(minusk E' k)
  end.

Fixpoint maxfst (E:menv) : nat :=
  match E with
  | nil => 0
  | (a,_)::E' => max a (maxfst E')
  end.

Lemma WFE_maxfst : forall E k,
    WFE E k ->
    maxfst E <= k.
Proof with auto.
  induction 1...
  simpl...
  destruct (maxfst E)...
  lia.
Qed.

Lemma maxfst_find_none: forall E k,
    maxfst E <= k ->
    find (S k) E = None.
Proof with auto.
  induction E;intros...
  destruct a.
  simpl in *...
  destruct (S k == n)...
  lia.
  apply IHE...
  lia.
Qed.

Lemma WFE_find_none: forall k E,
    WFE E k ->
    find (S k) E = None.
Proof with auto.
  intros.
  apply maxfst_find_none...
  apply WFE_maxfst...
Qed.
    
    
Lemma WFE_S_n:forall E n k,
  WFE E n ->
  WFE ((S n, k)::E) (S n).
Proof with auto.
  induction E;intros...
  constructor...
  apply WFE_find_none...
Qed.

Lemma WFE_find_in: forall E k,
    WFE E k ->
    forall q n, 0 < n -> 
    q < n ->
    find n E = find (n - q) (minusk E q).
Proof with auto.
  intros E k H.
  induction H;intros...
  remember (n-q).
  assert (minusk ((S k, b) :: E) q = (S k - q, b) :: (minusk E q)) as W by (simpl;auto).
  rewrite W.
  remember (S k - q).
  simpl...
  destruct (n==S k);destruct (n0==n1)...
  lia.
  lia.
  subst.
  apply IHWFE...
Qed.  

Lemma bindings_WFD_drop: forall E n b q,
    WFE E n -> q < n - b ->
    bindings_rec E n b = bindings_rec (minusk E q) (n - q) b.
Proof with auto.
  induction E;intros...
  dependent destruction H.
  assert (minusk ((S k, b0) :: E) q = (S k - q, b0) :: (minusk E q)) as W1 by (simpl;auto).
  rewrite W1...
  remember (S k - q).
  remember (S k).
  simpl...
  destruct (n-b == n);destruct (n0-b==n0)...
  lia.
  lia.
  subst.
  assert (S k - q - b = (S k - b) - q) as W2 by lia.
  rewrite W2.
  assert (0 < S k - b) as W3 by lia.
  remember (S k - b).
  rewrite <- WFE_find_in with (k:=k)...
Qed.
 
    

Lemma bindings_WFD_WFE: forall A k n E q,
    WFD A k->  WFE E n -> k <= n - q -> q <= n ->
    bindings_rec E n A = bindings_rec (minusk E q) (n-q) A.
Proof with auto using WFE_S_n.
  intros.
  generalize dependent E.
  generalize dependent n.
  generalize dependent q.
  induction H;intros;try solve [simpl in *;auto]...
  -
    assert (q < n-b). lia.
    apply bindings_WFD_drop...
  -
    simpl...
    f_equal.
    remember (bindings_rec ((S (n0 - q), 0) :: minusk E q) (S (n0 - q)) A).
    assert (S (n0 - q) = (S n0) - q) as W by  lia.
    rewrite W.
    assert  ( ((S n0 - q, S n1) :: minusk E q) = minusk ((S n0, S n1)::E) q) as W2 by (simpl;auto).
    rewrite W2.
    rewrite <- IHWFD...
    f_equal...
    f_equal...
    f_equal...
    f_equal...
    subst.
    rewrite W.
    assert ((S n0 - q, 0) :: minusk E q = minusk ((S n0, 0)::E) q) as W3 by (simpl;auto).
    rewrite W3.
    rewrite <- IHWFD...
    lia.
    lia.
Qed.

Lemma bindings_local_close: forall B E n,
  type B -> WFE E n ->
  bindings_rec E n B = bindings_rec nil 0 B.
Proof with auto.
  intros.
  rewrite bindings_WFD_WFE with (k:=0) (q:=n)...
  assert (0=n-n ) by lia.
  rewrite <- H1.
  rewrite bindings_close_env...
  apply close_type_wfd...
  lia.
Qed.

Lemma bindings_close : forall B a E n,
    type B -> WFE E n ->
    bindings_rec E n B = bindings_rec ((S n, a) :: E) (S n) B.
Proof with auto.
  intros.
  rewrite bindings_local_close...
  remember (bindings_rec empty_menv 0 B).
  rewrite bindings_local_close...
  apply WFE_S_n...
Qed.  


Lemma bindings_find: forall A E1 E2 B,
    find zero (E1++E2) = None ->
    type B ->
    WFC A 0 ->
    WFE (E1++E2)  0 ->
    bindings_rec (E1++E2) 0 (open_tt A B) =
    bindings_rec (E1 ++ (zero, bindings_rec (E1++E2) 0 B) :: E2) 0 A.
Proof with auto.
  intro A.
  unfold open_tt.
  generalize 0.
  unfold zero.
  induction A;intros;try solve [dependent destruction H1;simpl;auto]...
  -
    destruct (n0==n);subst...
    +
      assert (open_tt_rec n B n = B) as Q.
      {
        simpl...
        destruct (n==n)...
        destruct n0...
      }
      rewrite Q.
      simpl.
      rewrite Nat.sub_diag.
      rewrite bindings_find_in...
    +
      assert (open_tt_rec n0 B n = n) as Q.
      {
        simpl...
        destruct (n0==n)...
        destruct e...
        destruct n1...
      }
      rewrite Q.
      simpl.
      dependent destruction H1.
      apply neq_minus in H1...
      destruct H1...
      rewrite H1.
      erewrite <- bindings_find_notin... 
  -
    dependent destruction H1...
    simpl.
    f_equal.
    remember (S n, S (bindings_rec ((S n, 0) :: E1 ++ (0, bindings_rec (E1 ++ E2) n B) :: E2) (S n) A)) as R1.
    assert (bindings_rec (E1++E2) n B = bindings_rec (R1 :: E1++E2) (S n) B) as Q1.
    subst.
    apply bindings_close...
    rewrite Q1.    
    rewrite_alist ((R1 :: E1) ++ (0, bindings_rec ((R1 :: E1) ++ E2) (S n) B) :: E2).
    rewrite <- IHA...
    f_equal...
    remember (bindings_rec ((S n, 0) :: E1 ++ E2) (S n) (open_tt_rec (S n) B A)) as R2.
    rewrite_alist (R1 :: E1 ++ E2).
    f_equal.
    subst.
    f_equal...
    f_equal.
    assert (bindings_rec (E1++E2) n B = bindings_rec (((S n, 0) :: E1)++E2) (S n) B) as Q2.
    apply bindings_close...
    rewrite Q2.
    rewrite_alist (((S n, 0) :: E1) ++ (0, bindings_rec (((S n, 0) :: E1) ++ E2) (S n) B) :: E2).
    rewrite <- IHA...
    rewrite_env ((S n, 0) :: E1 ++ E2).
    apply WFE_S_n...
    rewrite_alist (R1 :: E1 ++E2)...
    subst...
    rewrite_env (R1 :: E1 ++ E2).
    subst.
    apply WFE_S_n...
Qed.
 

Lemma decidability_aux: forall k A B E ,
    max (bindings A) (bindings B) <= k ->
    {Sub E A B} + {~ Sub E A B}.
Proof with auto.
  intros k.
  induction k.
  -
    intros A;induction A;intros B;induction B;intros;try solve [solve_right_dec|solve_top_dec E|simpl in *;lia]...
    +
      solve_top_wfs_dec E (n).
    +
      solve_top_wfs_dec E a.
    +
      pose wf_env_dec.
      pose WFS_dec.
      destruct (a==a0);subst...
      *
        destruct s with (E:=E)...
        destruct s0 with (E:=E) (A:=a0)...
        right...
        intros v.
        apply n...
        dependent destruction v...
        right...
        intros v.
        apply n.
        dependent destruction v...
      *
        right...
        intros v.
        dependent destruction v...        
  -
    intros A;induction A;intros B;induction B;intros;try solve [solve_right_dec|solve_top_dec E]...
    +
      solve_top_wfs_dec E (n).
    +
      solve_top_wfs_dec E a.
    +
      pose wf_env_dec.
      pose WFS_dec.
      destruct (a==a0);subst...
      *
        destruct s with (E:=E)...
        destruct s0 with (E:=E) (A:=a0)...
        right...
        intros v.
        apply n...
        dependent destruction v...
        right...
        intros v.
        apply n.
        dependent destruction v...
      *
        right...
        intros v.
        dependent destruction v...   
    +
      solve_top_wfs_dec E (typ_mu A).
    +
      pose wf_env_dec as W1.
      pose WFS_dec as W2.
      clear IHA IHB.
      simpl in *.
      pick fresh X.
      remember (open_tt A (typ_rcd X (open_tt A X))) as Q1.
      remember (open_tt B (typ_rcd X (open_tt B X))) as Q2.
      destruct W1 with (E:=X~bind_sub ++ E)...
      destruct W2 with (E:=X~bind_sub ++ E) (A:=open_tt A X)...
      destruct W2 with (E:=X~bind_sub ++ E) (A:=open_tt B X)...
      *
        destruct IHk with  (A:=Q1) (B:=Q2) (E:=X~bind_sub ++ E).
        --
          assert (WFC A 0).
          {
            apply WFS_type in w0.
            apply type_open_tt_WFC in w0...
          }
          assert (WFC B 0).
          {
            apply WFS_type in w1.
            apply type_open_tt_WFC in w1...
          }
          assert (type (open_tt A X)) by (apply WFS_type in w0;auto).
          assert (type (open_tt B X)) by (apply WFS_type in w1;auto).
          subst.
          unfold bindings in *.
          rewrite_alist (empty_menv ++ empty_menv).
          rewrite bindings_find...
          rewrite bindings_find...
          simpl...
          assert (bindings_rec (empty_menv++empty_menv) 0 (open_tt A X) = bindings_rec (empty_menv++(0,0)::empty_menv) 0 A) as R1.
          rewrite bindings_find...
          assert (bindings_rec (empty_menv++empty_menv) 0 (open_tt B X) = bindings_rec (empty_menv++(0,0)::empty_menv) 0 B) as R2.
          rewrite bindings_find...
          rewrite_alist (empty_menv ++ empty_menv).
          rewrite R1.
          rewrite R2.
          apply Peano.le_S_n in H.
          simpl in H.
          unfold zero.
          rewrite_env ((0, 0) :: empty_menv).
          assert (bindings_rec ((0, S (bindings_rec ((0, 0) :: empty_menv) 0 A)) :: empty_menv ++ empty_menv) 0 A = bindings_rec ((1, S (bindings_rec ((1, 0) :: empty_menv) 1 A)) :: empty_menv) 1 A)as P1.
          {
            rewrite bindings_add...
            simpl...
            f_equal...
            rewrite bindings_add...
          }
          assert (bindings_rec ((0, S (bindings_rec ((0, 0) :: empty_menv) 0 B)) :: empty_menv ++ empty_menv) 0 B = bindings_rec ((1, S (bindings_rec ((1, 0) :: empty_menv) 1 B)) :: empty_menv) 1 B)as P2.
          {
            rewrite bindings_add...
            simpl...
            f_equal...
            rewrite bindings_add...
          }
          rewrite P1.
          rewrite P2.
          lia.
        --
          left.
          apply S_rec with (L:={{X}} \u fv_tt A \u fv_tt B \u dom E);intros...
          rewrite_env (WFS (nil ++ X0 ~ bind_sub ++ E) (open_tt A X0)).
          apply WFS_replacing_var with (X:=X)...
          rewrite_env (WFS (nil ++ X0 ~ bind_sub ++ E) (open_tt B X0)).
          apply WFS_replacing_var with (X:=X)...
          rewrite_env ((nil ++ X0 ~ bind_sub ++ E) ).
          subst.
          apply Sub_replacing_open with (X:=X)...
          dependent destruction w...
          constructor...
        --
          right.
          intros v.
          apply n.
          dependent destruction v.
          subst...
          pick fresh Y.
          specialize_x_and_L Y L.
          rewrite_env ((nil ++ X ~ bind_sub ++ E) ).
          apply Sub_replacing_open with (X:=Y)...
      *
        right.
        intros v.
        dependent destruction v.
        apply n.
        pick fresh Y.
        specialize_x_and_L Y L.
        rewrite_env ((nil ++ X ~ bind_sub ++ E) ).
        apply WFS_replacing_var with (X:=Y)...
      *
        right.
        intros v.
        dependent destruction v.
        apply n.
        pick fresh Y.
        specialize_x_and_L Y L.
        rewrite_env ((nil ++ X ~ bind_sub ++ E) ).
        apply WFS_replacing_var with (X:=Y)...
      *
        right.
        intros v.
        dependent destruction v.
        apply n.
        pick fresh Y.
        specialize_x_and_L Y L.
        get_well_form...
        dependent destruction H4...
    +
      solve_top_wfs_dec E (typ_arrow A1 A2).
    +
      simpl in H...
      apply Peano.le_S_n in H.
      destruct IHk with (A:=B1) (B:=A1) (E:=E)...
      unfold bindings.
      lia.
      destruct IHk with (A:=A2) (B:=B2) (E:=E)...
      unfold bindings.
      lia.
      right.
      intros v.
      dependent destruction v...
      right.
      intros v.
      dependent destruction v...
    +
      solve_top_wfs_dec E (typ_rcd a A).
    +
      simpl in H...
      apply Peano.le_S_n in H.
      destruct (a==a0);subst...
      *
        destruct IHk with (A:=A) (B:=B) (E:=E)...
        right.
        intros v.
        dependent destruction v...
      *
        right.
        intros v.
        dependent destruction v...
Qed.

Lemma decidability: forall A B E ,
    {Sub E A B} + {~ Sub E A B}.
Proof with auto.
  intros.
  apply decidability_aux with (k:=max (bindings A) (bindings B))...
Qed.
