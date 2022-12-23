(*
 * qkernel.v - Proof of the small quasi-kernel conjecture under the assumption of an axiom 
 *
 * Allan van Hulst - 2022
 *
 * (C) The author. Released under the CC BY-ND license (International 4.0).
 *)

Require Import List.
Require Import Lia.

(* Assume Classical Logic (i.e. law-of-excluded middle) *)
Axiom CL : forall (P : Prop), P \/ ~ P.

(* Assume a general universe of vertices U as a parameter for this theory *)
Parameter U : Set.

(* Define a directed graph as a pair D = (V(D),A(D)) *)
Definition digraph : Type := list U * list (U * U).

(* Define V(D) and A(D), include both sides of A(D) in V(D) *)
Definition A (D : digraph) := snd D.
Definition V (D : digraph) := fst D ++ map fst (A D) ++ map snd (A D).
 
(* A digraph is simple if it does not have any self-loops *)
Definition simple (D : digraph) := forall (u : U), ~ In (u, u) (A D).

(* A digraph is source-free is every vertex has at least one ingoing arc *)
Definition src_free (D : digraph) := forall (v : U), In v (V D) -> exists (u : U), In (u, v) (A D).

(* I is and independent set in D *)
Definition indep (I : list U) (D : digraph) := incl I (V D) /\
  forall (u v : U), In u I -> In v I -> ~ In (u, v) (A D).

(* Q is a quasi-kernel in D *)
Definition qkernel (Q : list U) (D : digraph) := indep Q D /\
  forall (w : U), In w (V D) -> In w Q \/
    (exists (v : U), In v Q /\ In (v, w) (A D)) \/
    (exists (u v : U), In u Q /\ In (u, v) (A D) /\ In (v, w) (A D)).

(* A simple counting predicate for lists of vertices *)
Inductive count : list U -> nat -> Prop :=
  | count_nil : count nil 0
  | count_inc : forall (u : U) (L : list U) (n : nat), count L n -> In u L -> count (u :: L) n
  | count_exc : forall (u : U) (L : list U) (n : nat), count L n -> ~ In u L -> count (u :: L) (n + 1).

(* N contains the out-neighborhood of u in D *)
Definition nbh_out (u : U) (N : list U) (D : digraph) := forall (v : U), In v N <-> In (u, v) (A D).

(* Vertex u has out-degree d in D *)
Definition deg_out (u : U) (D : digraph) (d : nat) := forall (N : list U), nbh_out u N D -> count N d.

(* Vertex w is a relative source w.r.t. vertex u if D - N+[u] has w as a new source *)
Definition rel_src (u w : U) (D : digraph) := ~ In (u, w) (A D) /\
  (exists (v : U), In (u, v) (A D) /\ In (v, w) (A D)) /\
  (forall (v : U), In (v, w) (A D) -> In (u, v) (A D)).

(* R has all relative sources with regard to u in D *)
Definition all_rel_src (u : U) (R : list U) (D : digraph) := forall (w : U), In w R <-> rel_src u w D.

(* Count the number of relative sources with regard to u in D *)
Definition num_rel_src (u : U) (D : digraph) (n : nat) := forall (R : list U), all_rel_src u R D -> count R n.

(* We state the following as an axiom about the number of relative sources *)
Axiom rel_src_leq_deg : forall (D : digraph), simple D -> A D <> nil -> exists (u : U) (n d : nat),
  In u (V D) /\ deg_out u D d /\ num_rel_src u D n /\ d >= 1 /\ d >= n.

(* Set-theoretic equality on lists of vertices *)
Definition eql (M N : list U) := incl M N /\ incl N M.

(* Lists of vertices M and N are disjoint *)
Definition disj (M N : list U) := forall (u : U), ~ (In u M /\ In u N).

(* Sub-digraph D' emerges when the vertex-set X is removed from D *)
Definition minus_set (X : list U) (D' D : digraph) := eql (X ++ V D') (V D) /\ disj X (V D') /\
  forall (u v : U), In (u, v) (A D') <-> In (u, v) (A D) /\ ~ In u X /\ ~ In v X.

(* An inductively defined breakdown schema (BDS) for directed graphs *)
Inductive bds : digraph -> list (U * list U) -> Prop :=
  | bds_vert_nil : forall (D : digraph), V D = nil -> bds D nil
  | bds_arcs_nil : forall (D D' : digraph) (B : list (U * list U)) (u : U),
    A D = nil -> minus_set (u :: nil) D' D -> bds D' B -> bds D ((u, nil) :: B)
  | bds_step : forall (D D' : digraph) (B : list (U * list U)) (u : U) (N : list U) (d n : nat),
    minus_set (u :: N) D' D -> nbh_out u N D -> deg_out u D d -> num_rel_src u D n -> 
    d >= 1 -> d >= n -> bds D' B -> bds D ((u, N) :: B).

(* The qkernel follows the construction from the breakdown schema *)
Definition qk_constr (Q : list U) (B : list (U * list U)) (D : digraph) :=
  forall (w : U) (N : list U), In (w, N) B -> In w Q \/ (exists (v : U), In v Q /\ In (v, w) (A D)) \/
    (N = nil /\ exists (u v : U) (M : list U), In u Q /\ In (u, M) B /\ In v M /\ In (v, w) (A D)).

(* Q is the smallest qkernel derivable from a breakdown schema for a specific digraph *)
Definition qkernel_smallest (Q : list U) (D : digraph) (B : list (U * list U)) :=
  qkernel Q D /\ incl Q (map fst B) /\ qk_constr Q B D /\ forall (Q' : list U) (m n : nat),
    qkernel Q' D -> incl Q' (map fst B) -> qk_constr Q' B D -> count Q m -> count Q' n -> m <= n.

(* Vertex v is an EPON with regard to vertex u and quasi-kernel Q in D *)
Definition epon (u v : U) (Q : list U) (D : digraph) :=
  In u Q /\ ~ In v Q /\ In (u, v) (A D) /\ forall (w : U), In (w, v) (A D) -> In w Q -> w = u.

(* Vertex w occurs under a b-step in the breakdown schema B *)
Definition under_b_step (w : U) (Q : list U) (B : list (U * list U)) (D : digraph) :=
  exists (u v : U) (N : list U), In (u, N) B /\ In u Q /\ In v N /\ In (v, w) (A D).

(* Collect all vertices in a breakdown schema *)
Fixpoint coll_bds (B : list (U * list U)) :=
  match B with
  | nil => nil
  | (u, N) :: B => (u :: N) ++ coll_bds B
  end.

(* Only collect the neighborhoods from a breakdown schema *)
Fixpoint coll_bds_nbh (B : list (U * list U)) :=
  match B with
  | nil => nil
  | (u, N) :: B => N ++ coll_bds_nbh B
  end.

(* Strong induction for natural numbers *)
Lemma strong_ind : forall (P : nat -> Prop), 
  (forall (n : nat), (forall (m : nat), m < n -> P m) -> P n) -> forall (n : nat), P n.
Proof.
  intros P IH n ; apply IH ; induction n ; intros m H ; inversion H ; auto.
Qed.

(* Every list of vertices has a count *)
Lemma count_ex : forall (L : list U), exists (n : nat), count L n.
Proof.
  intro L ; induction L as [ | u L ] ; [ exists 0 ; apply count_nil | destruct IHL as [ n H ] ].
  destruct (CL (In u L)) ; [ exists n ; apply count_inc | exists (n + 1) ; apply count_exc ] ; auto.
Qed.

(* Case distinction for the count predicate *)
Lemma count_cases : forall (u : U) (L : list U) (n : nat), count (u :: L) n ->
  In u L /\ count L n \/ ~ In u L /\ exists (m : nat), count L m /\ n = m + 1.
Proof.
  intros u L n H ; inversion H ; eauto.
Qed.

(* The count predicate is univalent *)
Lemma count_univ : forall (L : list U) (m n : nat), count L m -> count L n -> m = n.
Proof.
  intro L ; induction L as [ | u L ] ; intros m n Hm Hn ; [ inversion Hm ; inversion Hn ; auto | ].
  apply count_cases in Hm ; destruct Hm as [ [ Hin Hm ] | Hm ] ;
    apply count_cases in Hn ; destruct Hn as [ [ Hin' Hn ] | Hn ] ; solve [ auto ] ||
    solve [ inversion Hm ; contradiction ] || solve [ inversion Hn ; contradiction ] || auto.
  destruct Hm as [ _ [ m' [ Hm Heq ] ] ] ; destruct Hn as [ _ [ n' [ Hn Heq' ] ] ] ; assert (m' = n' ) ; lia || auto.
Qed.

(* Removing one element from a list decreases the count *)
Lemma count_rem : forall (u : U) (L : list U) (n : nat), In u L -> count L n ->
  exists (M : list U) (m : nat), ~ In u M /\ count M m /\ eql (u :: M) L /\ n = m + 1.
Proof.
  intros u L ; revert u ; induction L as [ | v L ] ; intros u n Hin Hcount ; [ simpl in Hin ; contradiction | ].
  destruct Hin as [ Heq | Hin ] ; [ rewrite Heq in * ; clear Heq v | ].
  apply count_cases in Hcount ; destruct Hcount as [ [ Hin Hcount ] | H ].
  destruct (IHL u n Hin Hcount) as [ M [ m [ Hnot_inM [ HcountM [ Heql Heq ] ] ] ] ].
  exists M ; exists m ; split ; [ | split ; [ | split ] ] ; auto.
  split ; intros v H ; destruct H as [ H | H ] ; solve [ simpl ; auto ] || 
    solve [ right ; apply Heql ; simpl ; auto ] || apply Heql in H ; auto.
  destruct H as [ Hnot_inL [ m [ Hcount Heq ] ] ] ; exists L ; exists m ; 
    split ; [ | split ; [ | split ] ] ; solve [ auto ] || split ; intros v H ; auto.
  apply count_cases in Hcount ; destruct Hcount as [ [ Hin' Hcount ] | H ].
  destruct (IHL u n Hin Hcount) as [ M [ m [ Hnot_inM [ HcountM [ Heql Heq ] ] ] ] ].
  exists M ; exists m ; split ; [ | split ; [ | split ] ] ; auto.
  split ; intros w H ; destruct H as [ H | H ] ; solve [ rewrite H in * ; simpl ; auto ] || solve [ right ; 
    apply Heql ; simpl ; auto ] || solve [ rewrite H in * ; apply Heql in Hin' ; auto ] || apply Heql in H ; auto.
  destruct H as [ Hnot_inL [ k [ Hcount Heq ] ] ].
  destruct (IHL u k Hin Hcount) as [ M [ m [ Hnot_inM [ HM [ Heql Heq' ] ] ] ] ].
  exists (v :: M) ; exists k ; split ; [ | split ; [ | split ] ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite H in * ; contradiction | contradiction ].
  rewrite Heq' ; apply count_exc ; solve [ auto ] || intro H.
  assert (In v (u :: M)) as H' by ( simpl ; auto ) ; apply Heql in H' ; contradiction.
  split ; intros w H ; destruct H as [ H | H ] ; solve [ simpl in * ; tauto ] || 
    solve [ rewrite H in * ; simpl ; auto ] || solve [ apply Heql in H ; simpl in * ; tauto ] || auto.
  destruct H as [ H | H ] ; [ simpl ; auto | right ; apply Heql ; simpl ; auto ].
Qed.

(* Correspondence between the count predicate and inclusion *)
Lemma count_incl : forall (M N : list U) (m n : nat),
  incl M N -> count M m -> count N n -> m <= n.
Proof.
  intro M ; induction M as [ | u M ] ; intros N m n Hincl HM HN ; [ inversion HM ; lia | ].
  apply count_cases in HM ; destruct HM as [ HM | HM ].
  apply (IHM N) ; tauto || intros v H ; apply Hincl ; simpl ; auto.
  destruct HM as [ Hnot_inM [ m' [ HM Heq ] ] ].
  destruct (count_rem u N n) as [ N' [ n' H ] ] ; solve [ auto ] || solve [ apply Hincl ; simpl ; auto ] || auto.
  destruct H as [ Hnot_inN' [ HN' [ Heql Heq' ] ] ] ; assert (m' <= n') ; lia || apply (IHM N') ; auto.
  intros v H ; assert (In v (u :: M)) as H' by ( simpl ; auto ) ; apply Hincl in H'.
  apply Heql in H' ; destruct H' as [ H' | H' ] ; solve [ auto ] || rewrite H' in * ; contradiction.
Qed.

(* Correspondence between the count predicate and set-theoretic equality on lists of vertices *)
Lemma count_eql : forall (M N : list U) (m n : nat),
  eql M N -> count M m -> count N n -> m = n.
Proof.
  intros M N m n H HM HN ; destruct H ; assert (m <= n /\ n <= m) ; lia || split ;
    [ apply count_incl with M N | apply count_incl with N M ] ; auto.
Qed.

(* The count of disjoint lists is additive *)
Lemma count_disj : forall (M N : list U) (m n : nat),
  disj M N -> count M m -> count N n -> count (M ++ N) (m + n).
Proof.
  intro M ; induction M as [ | u M ] ; intros N m n Hdisj HM HN ; [ simpl ; inversion HM ; simpl ; auto | ].
  simpl ; apply count_cases in HM ; destruct HM as [ HM | HM ].
  apply count_inc ; [ apply IHM ; tauto || auto | apply in_or_app ; tauto ].
  intros v H ; apply (Hdisj v) ; simpl ; split ; tauto.
  destruct HM as [ Hnot_inM [ k [ HK Heq ] ] ] ; rewrite Heq.
  replace (k + 1 + n) with ((k + n) + 1) by lia ; apply count_exc.
  apply IHM ; solve [ auto ] || intros v H ; apply (Hdisj v) ; simpl ; split ; tauto.
  intro H ; apply in_app_or in H ; destruct H as [ H | H ] ; contradiction || auto.
  apply (Hdisj u) ; simpl ; split ; auto.
Qed.

(* Only an empty list can have count zero *)
Lemma count_zero_nil : forall (L : list U), count L 0 -> L = nil.
Proof.
  intro L ; induction L as [ | u L ] ; intro H ; auto.
  apply count_cases in H ; destruct H as [ [ Hin Hcount ] | H ].
  apply IHL in Hcount ; rewrite Hcount in Hin ; simpl in Hin ; contradiction.
  destruct H as [ _ [ m [ _ H ] ] ] ; assert (0 <> m + 1) by lia ; contradiction.
Qed.

(* If a list has a non-zero count it must contain at least one element *)
Lemma count_nz_in : forall (L : list U) (n : nat), count L n -> n > 0 -> exists (u : U), In u L.
Proof.
  intros L n Hcount Hgt_zero ; destruct L as [ | u L ] ; [ | exists u ; simpl ; auto ].
  replace n with 0 in * by ( inversion Hcount ; auto ) ; assert (~ 0 > 0) by lia ; contradiction.
Qed.

(* Every arc also appears in the list of vertices *)
Lemma in_arc_in_vert : forall (u v : U) (D : digraph), In (u, v) (A D) -> In u (V D) /\ In v (V D).
Proof.
  intros u v D H ; split ; apply in_or_app ; right ; apply in_or_app ; [ left | right ] ;
    apply in_map_iff ; exists (u, v) ; simpl ; split ; auto.
Qed.

(* A sub-list of vertices corresponding to a certain property always exists *)
Lemma sub_list_ex : forall (T : Type) (P : T -> Prop) (L : list T),
  exists (M : list T), forall (x : T), In x M <-> In x L /\ P x.
Proof.
  intros T P L ; induction L as [ | y L ] ; [ | destruct IHL as [ M Hiff ] ].
  exists nil ; intro x ; split ; intro H ; [ simpl in H ; contradiction | simpl in * ; tauto ].
  destruct (CL (P y)) as [ HP | HnotP ] ; [ exists (y :: M) | exists M ] ; intro x ; split ; intro H.
  destruct H as [ H | H ] ; [ rewrite H in * ; split | apply Hiff in H ] ; simpl in * ; tauto.
  destruct H as [ [ H | H ] HP' ] ; [ simpl ; auto | right ; apply Hiff ; split ; auto ].
  apply Hiff in H ; simpl ; split ; tauto.
  destruct H as [ [ H | H ] HP' ] ; [ rewrite H in * ; contradiction | apply Hiff ; split ; auto ].
Qed.

(* The out-neighborhood of a vertex always exists *)
Lemma nbh_out_ex : forall (u : U) (D : digraph), exists (N : list U), nbh_out u N D.
Proof.
  intros u D ; destruct (sub_list_ex U (fun v => In (u, v) (A D)) (V D)) as [ N Hiff ].
  exists N ; intro v ; split ; intro H ; [ apply Hiff in H ; tauto | apply Hiff ; split ; auto ].
  apply in_arc_in_vert in H ; tauto.
Qed.

(* For every subset of vertices, a sub-digraph corresponding to minus_set always exists *)
Lemma minus_set_ex : forall (X : list U) (D : digraph), incl X (V D) -> exists (D' : digraph), minus_set X D' D.
Proof.
  intros X D Hincl ; destruct (sub_list_ex U (fun v => ~ In v X) (V D)) as [ V' HiffV ].
  destruct (sub_list_ex (U * U) (fun uv => ~ In (fst uv) X /\ ~ In (snd uv) X) (A D)) as [ A' HiffA ].
  exists (V', A') ; split ; [ split ; intros u H | split ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hincl in H ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ simpl in H ; apply HiffV in H ; tauto | ].
  simpl in H ; apply in_app_or in H ; destruct H as [ H | H ] ; apply in_map_iff in H ;
    destruct H as [ [ v w ] [ Heq Hin ] ] ; simpl in Heq ; rewrite Heq in * ; apply HiffA in Hin ;
    destruct Hin as [ H _ ] ; apply in_arc_in_vert in H ; tauto.
  destruct (CL (In u X)) as [ HinX | Hnot_inX ] ; [ apply in_or_app ; auto | ].
  apply in_or_app ; right ; apply in_or_app ; simpl ; left ; apply HiffV ; split ; auto.
  intros u H ; destruct H as [ HinX H ] ; apply in_app_or in H ; destruct H as [ H | H ].
  simpl in H ; apply HiffV in H ; destruct H ; contradiction.
  simpl in H ; apply in_app_or in H ; destruct H as [ H | H ] ; apply in_map_iff in H ;
    destruct H as [ [ v w ] [ Heq Hin ] ] ; simpl in Heq ; rewrite Heq in * ; apply HiffA in Hin ;
    simpl in Hin ; destruct Hin as [ _ [ Hnot_in Hnot_in' ] ] ; contradiction.
  simpl ; intros u v ; split ; intro H ; [ apply HiffA in H ; simpl in H ; auto | apply HiffA ; simpl ; auto ].
Qed.

(* The minus_set predicate always corresponds to a smaller digraph (provided that X is not empty) *)
Lemma minus_set_smaller : forall (X : list U) (D' D : digraph) (m n : nat),
  minus_set X D' D -> X <> nil -> count (V D) n -> count (V D') m -> m < n.
Proof.
  intros X D' D m n Hminus_set Hnot_nil HcountD HcountD' ; assert (exists (u : U), In u X) as Hin_ex.
  destruct X as [ | u X ] ; [ assert False ; contradiction || apply Hnot_nil ; auto | exists u ; simpl ; auto ].
  destruct Hin_ex as [ u HinX ] ; assert (In u (V D)) as HinV by ( apply Hminus_set ; apply in_or_app ; auto ).
  destruct (count_rem u (V D) n HinV HcountD) as [ V' [ k [ Hnot_inV' [ HcountV' [ Heql Heq ] ] ] ] ].
  assert (m <= k) ; lia || apply count_incl with (V D') V' ; solve [ auto ] || intros v H.
  assert (In v (X ++ V D')) as Hin by ( apply in_or_app ; auto ) ; apply Hminus_set in Hin ; apply Heql in Hin.
  destruct Hin as [ Heq' | HinV' ] ; [ rewrite Heq' in * ; assert False ; contradiction || auto | auto ].
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; split ; auto.
Qed.

(* For every digraph a breakdown schema exists *)
Lemma bds_ex : forall (D : digraph), simple D -> exists (B : list (U * list U)), bds D B.
Proof.
  intros D Hsimple ; destruct (count_ex (V D)) as [ n Hcount ] ; revert Hsimple Hcount.
  revert D ; induction n using strong_ind ; rename H into IH ; intros D Hsimple Hcount.
  assert (n = 0 \/ n > 0) as H by lia ; destruct H as [ Hvert_zero | Hvert_not_zero ].
  rewrite Hvert_zero in * ; clear Hvert_zero n ; exists nil ; apply bds_vert_nil ; apply count_zero_nil in Hcount ; auto.
  destruct (CL (A D = nil)) as [ Harcs_nil | Harcs_not_nil ].
  assert (exists (u : U), In u (V D)) as Hex_in by ( apply count_nz_in with (L := V D) in Hvert_not_zero ; auto ).
  destruct Hex_in as [ u HinV ] ; destruct (minus_set_ex (u :: nil) D) as [ D' Hminus_set ].
  intros v H ; destruct H as [ H | H ] ; [ rewrite H in * ; auto | simpl in H ; contradiction ].
  destruct (count_ex (V D')) as [ m Hcount' ] ; destruct (IH m) with (D := D') as [ B Hbds ] ; auto.
  apply (minus_set_smaller (u :: nil) D' D m n) ; solve [ auto ] || intro H ; inversion H.
  intros v Harc ; apply (Hsimple v) ; apply Hminus_set in Harc ; tauto.
  exists ((u, nil) :: B) ; apply bds_arcs_nil with D' ; auto.
  destruct (rel_src_leq_deg D Hsimple Harcs_not_nil) as [ u  [ k [ d H ] ] ].
  destruct H as [ HinV [ Hdeg_out [ Hnum_rel_src [ Hgeq_one Hgeq_k ] ] ] ].
  destruct (nbh_out_ex u D) as [ N Hnbh_out ] ; destruct (minus_set_ex (u :: N) D) as [ D' Hminus_set ].
  intros v H ; destruct H as [ H | H ] ; [ rewrite H in * ; auto | 
    apply Hnbh_out in H ; apply in_arc_in_vert in H ; tauto ].
  destruct (count_ex (V D')) as [ m Hcount' ] ; destruct (IH m) with (D := D') as [ B Hbds ] ; auto.
  apply (minus_set_smaller (u :: N) D' D m n) ; solve [ auto ] || intro H ; inversion H.
  intros v Harc ; apply (Hsimple v) ; apply Hminus_set in Harc ; tauto.
  exists ((u, N) :: B) ; apply bds_step with D' d k ; auto.
Qed.

(* Based on the breakdown schema B we can construct a quasi-kernel Q for D *)
Lemma bds_impl_qkernel : forall (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> exists (Q : list U), qkernel Q D /\ incl Q (map fst B) /\ qk_constr Q B D.
Proof.
  intros D B Hsimple H ; induction H as [ D Heq_nil | D D' B u Heq_nil Hminus_set Hbds IH | 
    D D' B u N d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  exists nil ; split ; [ split ; [ split | ] | split ] ; solve [ intros u H ; simpl in H ; contradiction ] || auto.
  intros u H ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct IH as [ Q [ Hqkernel [ Hincl Hqk_constr ] ] ].
  intros v H ; apply (Hsimple v) ; apply Hminus_set in H ; tauto.
  exists (u :: Q) ; split ; [ split ; [ split | ] | split ] ; auto.
  intros v H ; destruct H as [ H | H ] ; [ rewrite <- H in * ; apply Hminus_set ; simpl ; auto | ].
  apply Hqkernel in H ; apply Hminus_set ; simpl ; right ; auto.
  intros v w Hv Hw Harc ; rewrite Heq_nil in Harc ; simpl in Harc ; contradiction.
  intros w H ; apply Hminus_set in H ; destruct H as [ H | H ] ; [ simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ simpl in H ; contradiction | ].
  apply Hqkernel in H ; destruct H as [ H | [ H | H ] ] ; [ simpl ; auto | | ].
  destruct H as [ v [ _ H ] ] ; apply Hminus_set in H ; destruct H as [ H _ ] ;
    rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct H as [ x [ y [ _ [ H _ ] ] ] ] ; apply Hminus_set in H.
  destruct H as [ H _ ] ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  simpl ; intros v H ; destruct H as [ H | H ] ; [ simpl ; auto | apply Hincl in H ; simpl ; auto ].
  intros w N H ; simpl in H ; destruct H as [ H | H ] ; [ inversion H ; simpl ; auto | ].
  apply Hqk_constr in H ; destruct H as [ H | [ H | H ] ] ; [ simpl ; auto | | ].
  destruct H as [ x [ HinQ Harc ] ] ; apply Hminus_set in Harc.
  destruct Harc as [ H _ ] ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct H as [ Heq_nil' [ x [ y [ M [ HinQ [ HinB [ HinM Harc ] ] ] ] ] ] ].
  right ; right ; split ; [ auto | exists x ; exists y ; exists M ].
  split ; [ | split ; [ | split ] ] ; solve [ simpl ; auto ] || apply Hminus_set in Harc ; tauto.
  destruct IH as [ Q [ Hqkernel [ Hincl Hqk_constr ] ] ].
  intros v H ; apply (Hsimple v) ; apply Hminus_set in H ; tauto.
  destruct (CL (exists (t : U), In t Q /\ In (t, u) (A D))) as [ Hinw_ex | Hinw_not_ex ].
  destruct Hinw_ex as [ t [ Ht_inQ Harc_tu ] ] ; exists Q ; split ; [ split ; [ split | ] | split ].
  intros v H ; apply Hqkernel in H ; apply Hminus_set ; simpl ; right ; apply in_or_app ; auto.
  intros v w Hv Hw Harc ; destruct Hqkernel as [ [ Hincl' Hindep_prop ] _ ].
  apply (Hindep_prop v w) ; solve [ auto ] || apply Hminus_set ; split ; [ | split ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  apply Hincl' in Hv ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; split ; simpl ; auto.
  apply Hincl' in Hv ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; split ; simpl ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  apply Hincl' in Hw ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; split ; simpl ; auto.
  apply Hincl' in Hw ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; split ; simpl ; auto.
  intros w H ; apply Hminus_set in H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  right ; left ; exists t ; split ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hnbh_out in H | ].
  right ; right ; exists t ; exists u ; split ; [ | split ] ; auto.
  apply Hqkernel in H ; destruct H as [ H | [ H | H ] ] ; auto.
  destruct H as [ v [ HinQ Harc ] ] ; right ; left ; exists v ; split ; 
    solve [ auto ] || apply Hminus_set in Harc ; tauto.
  destruct H as [ x [ y [ HinQ [ Harc_xy Harc_yw ] ] ] ] ; right ; right ;
    exists x ; exists y ; split ; [ | split ] ; solve [ auto ] ||
    apply Hminus_set in Harc_xy ; apply Hminus_set in Harc_yw ; tauto.
  intros v H ; simpl in H ; apply Hincl in H ; simpl ; auto.
  intros w M H ; simpl in H ; destruct H as [ H | H ].
  replace w with u in * by ( inversion H ; auto ).
  replace M with N in * by ( inversion H ; auto ).
  right ; left ; exists t ; split ; auto.
  apply Hqk_constr in H ; destruct H as [ H | [ H | H ] ] ; auto.
  destruct H as [ x [ HinQ Harc ] ] ; right ; left ; exists x ; split ; 
    solve [ auto ] || apply Hminus_set in Harc ; tauto.
  destruct H as [ Heq_nil [ x [ y [ M' [ HinQ [ HinB [ HinM Harc ] ] ] ] ] ] ].
  right ; right ; split ; [ auto | exists x ; exists y ; exists M' ; split ; auto ].
  split ; [ | split ] ; simpl ; solve [ auto ] || apply Hminus_set in Harc ; tauto.
  exists (u :: Q) ; split ; [ split ; [ split | ] | split ] ; auto.
  intros v H ; destruct H as [ H | H ] ; [ rewrite <- H ; apply Hminus_set ; simpl ; auto | ].
  apply Hqkernel in H ; apply Hminus_set ; simpl ; right ; apply in_or_app ; auto.
  intros v w Hv Hw Harc ; destruct Hv as [ Hv | Hv ] ; destruct Hw as [ Hw | Hw ].
  rewrite <- Hv in * ; rewrite <- Hw in * ; apply Hsimple in Harc ; contradiction.
  rewrite <- Hv in * ; apply Hnbh_out in Harc ; destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj w) ; simpl ; split ; [ auto | apply Hqkernel in Hw ; auto ].
  rewrite <- Hw in * ; apply Hinw_not_ex ; exists v ; split ; auto.
  destruct Hqkernel as [ [ Hincl' Hindep_prop ] _ ] ; apply (Hindep_prop v w) ; auto.
  apply Hminus_set ; split ; [ | split ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; simpl ; split ; auto.
  apply Hincl' in Hv ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; simpl ; split ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  apply Hinw_not_ex ; exists v ; split ; auto.
  apply Hincl' in Hw ; destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; simpl ; split ; auto.
  intros w H ; apply Hminus_set in H ; destruct H as [ H | H ] ; [ simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hnbh_out in H | ].
  right ; left ; exists u ; split ; simpl ; auto.
  apply Hqkernel in H ; destruct H as [ H | [ H | H ] ] ; [ simpl ; auto | | ].
  destruct H as [ v [ HinQ Harc ] ] ; right ; left ; exists v ; split ; simpl ; 
    solve [ auto ] || apply Hminus_set in Harc ; tauto.
  destruct H as [ x [ y [ HinQ [ Harc_xy Harc_yw ] ] ] ] ; right ; right ; exists x ; exists y ;
    split ; [ | split ] ; solve [ simpl ; auto ] || apply Hminus_set in Harc_xy ; apply Hminus_set in Harc_yw ; tauto.
  intros v H ; destruct H as [ H | H ] ; [ simpl ; auto | apply Hincl in H ; simpl ; auto ].
  intros w M H ; destruct H as [ H | H ] ; [ inversion H ; simpl ; auto | ].
  apply Hqk_constr in H ; destruct H as [ H | [ H | H ] ] ; [ simpl ; auto | | ].
  destruct H as [ x [ HinQ Harc ] ] ; right ; left ; exists x ; simpl ; split ; auto.
  apply Hminus_set in Harc ; tauto.
  destruct H as [ Heq_nil [ x [ y [ M' [ HinQ [ HinB [ HinM Harc ] ] ] ] ] ] ].
  right ; right ; split ; [ auto | exists x ; exists y ; exists M' ; split ; simpl ; auto ].
  split ; [ auto | split ; auto ].
  apply Hminus_set in Harc ; tauto.
Qed.

(* The smallest qkernel derivable from a breakdown schema always exists *)
Lemma qkernel_smallest_ex : forall (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> exists (Q : list U), qkernel_smallest Q D B.
Proof.
  intros D B Hsimple Hbds ; destruct (bds_impl_qkernel D B) as [ Q [ Hqkernel [ Hincl Hqk_constr ] ] ] ; auto.
  destruct (count_ex Q) as [ n Hcount ] ; revert Hsimple Hbds Hqkernel Hincl Hqk_constr Hcount ; revert D B Q.
  induction n using strong_ind ; rename H into IH ; intros D B Q Hsimple Hbds Hqkernel Hincl Hqk_constr Hcount.
  destruct (CL (exists (Q' : list U) (m : nat), qkernel Q' D /\ incl Q' (map fst B) /\ qk_constr Q' B D /\
    count Q' m /\ m < n)) as [ Hsmaller | Hsmaller_not_ex ]. 
  destruct Hsmaller as [ Q' [ m [ Hqkernel' [ Hincl' [ Hqk_constr' [ Hcount' Hless ] ] ] ] ] ].
  apply (IH m) with (Q := Q') ; auto.
  exists Q ; split ; [ | split ; [ | split ] ]  ; auto.
  intros Q' m k Hqkernel' Hincl' Hqk_constr' HcountQ HcountQ'.
  assert (m = n) as Heq_mn by ( apply count_univ with Q ; auto ).
  rewrite Heq_mn in * ; destruct (CL (k < m)) ; lia || auto.
  assert False ; contradiction || apply Hsmaller_not_ex.
  exists Q' ; exists k ; split ; [ | split ; [ | split ; [ | split ] ] ] ; lia || auto.
Qed.

(* Elements in the breakdown schema are included in the vertex set *)
Lemma in_bds_in_vert : forall (u : U) (N : list U) (D : digraph) (B : list (U * list U)),
  simple D -> In (u, N) B -> bds D B -> incl (u :: N) (V D).
Proof.
  intros u N D B Hsimple HinB H ; induction H as [ D Heq_nil | D D' B v Heq_nil Hminus_set Hbds IH | 
    D D' B v K d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HinB ; contradiction.
  destruct HinB as [ H | H ] ; [ | apply IH in H ].
  replace v with u in * by ( inversion H ; auto ) ; replace N with (@nil U) in * by ( inversion H ; auto ).
  clear H ; intros w H ; destruct H as [ H | H ] ; 
    [ rewrite <- H in * ; apply Hminus_set ; simpl ; auto | simpl in H ; contradiction ].
  intros w H' ; apply H in H' ; apply Hminus_set ; apply in_or_app ; auto.
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  destruct HinB as [ H | H ] ; [ | apply IH in H ].
  replace v with u in * by ( inversion H ; auto ) ; replace N with K in * by ( inversion H ; auto ) ; clear H.
  intros w H ; destruct H as [ H | H ] ; [ rewrite <- H in * ; apply Hminus_set ; simpl ; auto | ].
  apply Hnbh_out in H ; apply in_arc_in_vert in H ; tauto.
  intros w H' ; apply H in H' ; apply Hminus_set ; apply in_or_app ; auto.
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
Qed.

(* A single vertex can only have one neighborhood in the breakdown schema *)
Lemma bds_rhs_inj : forall (u : U) (M N : list U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In (u, M) B -> In (u, N) B -> M = N.
Proof.
  intros u M N D B Hsimple H HM HN ; induction H as [ D Heq_nil | D D' B v Heq_nil Hminus_set Hbds IH | 
    D D' B v K d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HM ; contradiction.
  destruct HM as [ HM | HM ] ; destruct HN as [ HN | HN ] ; [ inversion HM ; inversion HN ; auto | | | ].
  replace v with u in * by ( inversion HM ; auto ) ; apply in_bds_in_vert with (D := D') in HN ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ] ; 
    apply (Hdisj u) ; split ; [ simpl ; auto | apply HN ; simpl ; auto ].
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  replace v with u in * by ( inversion HN ; auto ) ; apply in_bds_in_vert with (D := D') in HM ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ] ; 
    apply (Hdisj u) ; split ; [ simpl ; auto | apply HM ; simpl ; auto ].
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  apply IH ; solve [ auto ] || intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  destruct HM as [ HM | HM ] ; destruct HN as [ HN | HN ].
  replace M with K by ( inversion HM ; auto ) ; replace N with K by ( inversion HN ; auto ) ; auto.
  replace v with u in * by ( inversion HM ; auto ) ; apply in_bds_in_vert with (D := D') in HN ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ] ; 
    apply (Hdisj u) ; split ; [ simpl ; auto | apply HN ; simpl ; auto ].
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  replace v with u in * by ( inversion HN ; auto ) ; apply in_bds_in_vert with (D := D') in HM ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ] ; 
    apply (Hdisj u) ; split ; [ simpl ; auto | apply HM ; simpl ; auto ].
  intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
  apply IH ; solve [ auto ] || intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto.
Qed.

(* Inclusion of (u,N) in the breakdown schema means that N is the neighborhood of u *)
Lemma bds_impl_arc : forall (u v : U) (N : list U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In (u, N) B -> In v N -> In (u, v) (A D).
Proof.
  intros u v N D B Hsimple H HinB HinN ; induction H as [ D Heq_nil | D D' B w Heq_nil Hminus_set Hbds IH | 
    D D' B w N' d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HinB ; contradiction.
  destruct HinB as [ H | H ] ; [ | apply IH in H ; solve [ auto ] || solve [ apply Hminus_set in H ; tauto ] || auto ].
  replace N with (@nil U) in * by ( inversion H ; auto ) ; simpl in HinN ; contradiction.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  destruct HinB as [ H | H ] ; [ | apply IH in H ; solve [ auto ] || solve [ apply Hminus_set in H ; tauto ] || auto ].
  replace N with N' in * by ( inversion H ; auto ) ; replace w with u in * by ( inversion H ; auto ) ;
    apply Hnbh_out in HinN ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
Qed.

(* Every vertex is included in the breakdown schema *)
Lemma in_vert_in_bds : forall (u : U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In u (V D) -> exists (v : U) (N : list U), In (v, N) B /\ In u (v :: N).
Proof.
  intros u D B Hsimple H HinV ; induction H as [ D Heq_nil | D D' B v Heq_nil Hminus_set Hbds IH | 
    D D' B v N d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  rewrite Heq_nil in HinV ; simpl in HinV ; contradiction.
  apply Hminus_set in HinV ; destruct HinV as [ H | H ] ; [ rewrite H in * | ].
  exists u ; exists nil ; split ; simpl ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; [ simpl in H ; contradiction | ].
  apply IH in H ; solve [ intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto ] || auto.
  destruct H as [ w [ N [ HinB Hin ] ] ] ; exists w ; exists N ; split ; simpl ; auto.
  apply Hminus_set in HinV ; destruct HinV as [ H | H ] ; [ rewrite H in * | ].
  exists u ; exists N ; split ; simpl ; auto.
  apply in_app_or in H ; destruct H as [ H | H ].
  exists v ; exists N ; split ; simpl ; auto.
  apply IH in H ; solve [ intros w Harc ; apply (Hsimple w) ; apply Hminus_set in Harc ; tauto ] || auto.
  destruct H as [ w [ N' [ HinB Hin ] ] ] ; exists w ; exists N' ; split ; simpl ; auto.
Qed.

(* Any step (w,nil) which is itself under a b-step must have an epon which is itself a top-vertex of an a-step *)
Lemma qkernel_smallest_epon : forall (D : digraph) (B : list (U * list U)) (Q : list U) (w : U),
  simple D -> bds D B -> qkernel_smallest Q D B -> In (w, nil) B -> In w Q -> under_b_step w Q B D ->
    exists (x : U), epon w x Q D /\ In x (map fst B).
Proof.
  intros D B Q w Hsimple Hbds Hqkernel_smallest Hin_bds HinQ Hunder_b_step.
  destruct Hqkernel_smallest as [ Hqkernel [ Hincl_fst [ Hqk_constr Hsmallest_prop ] ] ].
  destruct (CL (exists (x : U), epon w x Q D /\ In x (map fst B))) as [ Hepon_ex | Hepon_not_ex ] ; auto.
  destruct (count_ex Q) as [ n Hcount ] ; destruct (count_rem w Q n) as [ Q' [ m H ] ] ; auto.
  destruct H as [ Hnot_inQ' [ Hcount' [ Heql Heq ] ] ] ; assert (incl Q' (map fst B)) as Hincl' by
    ( intros v H ; apply Hincl_fst ; apply Heql ; simpl ; auto ) ; assert (qkernel Q' D) as Hqkernel'.
  split ; [ split | ] ; [ intros v H ; destruct Hqkernel as [ [ Hincl_prop _ ] _ ] | | ].
  apply Hincl_prop ; apply Heql ; simpl ; auto.
  intros u v Hu Hv Harc ; destruct Hqkernel as [ [ Hincl_prop Hindep_prop ] _ ].
  apply (Hindep_prop u v) ; solve [ auto ] || apply Heql ; simpl ; auto.
  intros x H ; apply in_vert_in_bds with (B := B) in H ; auto.
  destruct H as [ v [ N [ HinB H ] ] ] ; destruct H as [ H | H ] ; [ rewrite H in * ; clear H v | ].
  assert (In (x, N) B) as Hin_fst by ( auto ).
  apply Hqk_constr in Hin_fst ; destruct Hin_fst as [ H | [ H | H ] ].
  apply Heql in H ; destruct H as [ H | H ] ; [ rewrite H in * ; clear H w | auto ].
  destruct Hunder_b_step as [ u [ v [ N' [ HinB' [ Hu_inQ [ HinN' Harc ] ] ] ] ] ].
  right ; right ; exists u ; exists v ; split ; [ | split ] ; auto.
  apply Heql in Hu_inQ ; destruct Hu_inQ as [ H | H ] ; [ rewrite H in * ; clear H x | auto ].
  assert (N' = nil) as Heq_nil by ( apply bds_rhs_inj with u D B ; auto ).
  rewrite Heq_nil in HinN' ; simpl in HinN' ; contradiction.
  apply bds_impl_arc with N' B ; auto.
  destruct H as [ u [ Hu_inQ Harc ] ] ; apply Heql in Hu_inQ ; destruct Hu_inQ as [ H | H ].
  rewrite H in * ; clear H w ; destruct (CL (exists (v : U), 
    In v Q /\ In (v, x) (A D) /\ v <> u)) as [ Halt_ex | Halt_not_ex ].
  destruct Halt_ex as [ v [ Hv_inQ [ Harc' Hnot_eq ] ] ] ; right ; left ; exists v ; split ; auto.
  apply Heql in Hv_inQ ; destruct Hv_inQ as [ H | H ] ; [ symmetry in H ; contradiction | auto ].
  assert False ; contradiction || apply Hepon_not_ex ; exists x ; split ; auto.
  split ; [ apply Heql ; simpl ; auto | split ; [ | split ] ] ; auto.
  intro H ; destruct Hqkernel as [ [ Hincl_prop Hindep_prop ] _ ] ; apply (Hindep_prop u x) ; auto.
  intros w Harc' Hw_inQ ; destruct (CL (w = u)) as [ H | H ] ; auto.
  assert False ; contradiction || apply Halt_not_ex ; exists w ; split ; [ | split ] ; auto.
  apply in_map_iff ; exists (x, N) ; split ; simpl ; auto.
  right ; left ; exists u ; split ; auto.
  destruct H as [ Heq_nil [ y [ z [ M [ HinQ' [ HinB' [ HinM Harc ] ] ] ] ] ] ].
  right ; right ; exists y ; exists z ; split ; [ | split ] ; auto.
  apply Heql in HinQ' ; destruct HinQ' as [ H | H ] ; [ rewrite <- H in * | auto ].
  assert (M = nil) as Heq_nil' by ( apply bds_rhs_inj with w D B ; auto ).
  rewrite Heq_nil' in HinM ; simpl in HinM ; contradiction.
  apply bds_impl_arc with M B ; auto.
  assert (In (v, N) B) as Hin_fst by ( auto ).
  rename H into HinN ; apply Hqk_constr in Hin_fst ; destruct Hin_fst as [ H | [ H | H ] ].
  apply Heql in H ; destruct H as [ H | H ] ; [ rewrite H in * ; clear H w | ].
  assert (N = nil) as Heq_nil by ( apply bds_rhs_inj with v D B ; auto ).
  rewrite Heq_nil in HinN ; simpl in HinN ; contradiction.
  right ; left ; exists v ; split ; [ auto | apply bds_impl_arc with N B ; auto ].
  destruct H as [ u [ H Harc ] ] ; apply Heql in H ; destruct H as [ H | H ] ; [ rewrite H in * ; clear H w | ].
  destruct (CL (exists (w : U), In w Q /\ In (w, v) (A D) /\ w <> u)) as [ Halt_ex | Halt_not_ex ].
  destruct Halt_ex as [ w [ Hw_inQ [ Harc' Hnot_eq ] ] ] ; right ; right ; 
    exists w ; exists v ; split ; [ | split ] ; auto.
  apply Heql in Hw_inQ ; destruct Hw_inQ as [ H | H ] ; [ symmetry in H ; contradiction | auto ].
  apply bds_impl_arc with N B ; auto.
  assert False ; contradiction || apply Hepon_not_ex ; exists v ; split ; auto.
  split ; [ apply Heql ; simpl ; auto | split ; [ | split ] ] ; auto.
  intro H ; destruct Hqkernel as [ [ Hincl_prop Hindep_prop ] _ ] ; apply (Hindep_prop u v) ; auto.
  intros w Harc' Hw_inQ ; destruct (CL (w = u)) as [ H | H ] ; auto.
  assert False ; contradiction || apply Halt_not_ex ; exists w ; split ; [ | split ] ; auto.
  apply in_map_iff ; exists (v, N) ; split ; simpl ; auto.
  right ; right ; exists u ; exists v ; split ; [ | split ] ; auto.
  apply bds_impl_arc with N B ; auto.
  destruct H as [ H _ ] ; rewrite H in HinN ; simpl in HinN ; contradiction.
  assert (qk_constr Q' B D) as Hqk_constr'.
  intros v N H ; assert (In (v, N) B) as Hin_fst by auto ; apply Hqk_constr in H ; destruct H as [ H | [ H | H ] ].
  apply Heql in H ; destruct H as [ H | H ] ; [ rewrite <- H in * ; clear H v ; right ; right ; split | auto ].
  apply bds_rhs_inj with w D B ; auto.
  destruct Hunder_b_step as [ u [ v [ M [ HinB [ HinQ' [ HinM Harc ] ] ] ] ] ].
  exists u ; exists v ; exists M ; split ; [ | split ; [ | split ] ] ; auto.
  apply Heql in HinQ' ; destruct HinQ' as [ H | H ] ; [ rewrite H in * | auto ].
  assert (M = nil) as Heq_nil by ( apply bds_rhs_inj with u D B ; auto ).
  rewrite Heq_nil in HinM ; contradiction.
  destruct H as [ x [ H Harc ] ] ; apply Heql in H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  destruct (CL (exists (y : U), In y Q /\ In (y, v) (A D) /\ y <> w)) as [ Halt_ex | Halt_not_ex ].
  destruct Halt_ex as [ y [ Hy_inQ [ Harc' Hnot_eq ] ] ] ; right ; left ; exists y ; split ; auto.
  apply Heql in Hy_inQ ; destruct Hy_inQ as [ H' | H' ] ; [ symmetry in H' ; contradiction | auto ].
  assert False ; contradiction || apply Hepon_not_ex ; exists v ; split ; auto.
  split ; [ | split ; [ | split ] ] ; auto.
  intro H' ; destruct Hqkernel as [ [ Hincl_prop Hindep_prop ] _ ] ; apply (Hindep_prop w v) ; auto.
  intros z Harc' Hz_inQ ; destruct (CL (z = w)) as [ Heq' | Hnot_eq ] ; auto.
  assert False ; contradiction || apply Halt_not_ex ; exists z ; split ; [ | split ] ; auto.
  apply in_map_iff ; exists (v, N) ; simpl ; split ; auto.
  right ; left ; exists x ; split ; auto.
  destruct H as [ Heq_nil [ u [ x [ M [ HinQ' [ HinB [ HinM Harc ] ] ] ] ] ] ].
  right ; right ; split ; [ auto | exists u ; exists x ; exists M ; split ; [ | split ; [ | split ] ] ] ; auto.
  apply Heql in HinQ' ; destruct HinQ' as [ H | H ] ; [ rewrite H in * | auto ].
  assert (M = nil) as Heq_nil' by ( apply bds_rhs_inj with u D B ; auto ).
  rewrite Heq_nil' in HinM ; simpl in HinM ; contradiction.
  assert (n <= m) as Hleq by ( apply Hsmallest_prop with Q' ; auto ).
  assert (~ n <= m) by lia ; contradiction.
Qed.

(* The minus_set predicate is transitive with regard to the set that is removed *)
Lemma minus_set_trans : forall (X Y : list U) (D D' D'' : digraph),
  minus_set X D' D -> minus_set Y D'' D' -> minus_set (X ++ Y) D'' D.
Proof.
  intros X Y D D' D'' HX HY ; split ; [ | split ] ; [ split ; intros u H | | ].
  apply in_app_or in H ; destruct H as [ H | H ].
  apply in_app_or in H ; destruct H as [ H | H ].
  apply HX ; apply in_or_app ; auto.
  apply HX ; apply in_or_app ; right ; apply HY ; apply in_or_app ; auto.
  apply HX ; apply in_or_app ; right ; apply HY ; apply in_or_app ; auto.
  apply HX in H ; apply in_app_or in H ; destruct H as [ H | H ].
  apply in_or_app ; left ; apply in_or_app ; auto.
  apply HY in H ; apply in_app_or in H ; destruct H as [ H | H ].
  apply in_or_app ; left ; apply in_or_app ; auto.
  apply in_or_app ; auto.
  intros u H ; destruct H as [ H Hin ].
  apply in_app_or in H ; destruct H as [ H | H ].
  destruct HX as [ HeqlX [ HdisjX HarcsX ] ].
  apply (HdisjX u) ; split ; auto.
  apply HY ; apply in_or_app ; auto.
  destruct HY as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; split ; auto.
  intros u v ; split ; intro H.
  apply HY in H ; destruct H as [ Harc [ Hv Hu ] ] ; 
    apply HX in Harc ; destruct Harc as [ Harc [ Hv' Hu' ] ] ;
    split ; [ | split ] ; tauto || auto.
  intro H ; apply in_app_or in H ; destruct H ; contradiction.
  intro H ; apply in_app_or in H ; destruct H ; contradiction.
  destruct H as [ Harc [ Hu Hv ] ] ; apply HY ; split ; [ | split ].
  apply HX ; split ; [ | split ] ; auto.
  intro H ; apply Hu ; apply in_or_app ; auto.
  intro H ; apply Hv ; apply in_or_app ; auto.
  intro H ; apply Hu ; apply in_or_app ; auto.
  intro H ; apply Hv ; apply in_or_app ; auto.
Qed.

(* The minus_set predicate is reflexive if no vertices are removed *)
Lemma minus_set_nil : forall (D : digraph), minus_set nil D D.
Proof.
  intro D ; split ; [ | split ] ; [ simpl ; split ; intros u H ; auto | | ].
  intros u H ; destruct H as [ H _ ] ; simpl in H ; auto.
  intros u v ; split ; intro H ; tauto || auto.
Qed.

(* Every part (w, nil) of the breakdown schema is at some point a relative source *)
Lemma with_nil_rel_src : forall (w : U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In (w, nil) B -> (exists (v : U), In (v, w) (A D)) ->
    exists (u : U) (N : list U) (L R : list (U * list U)) (D' : digraph),
      B = L ++ (u, N) :: R /\ minus_set (coll_bds L) D' D /\ rel_src u w D' /\ nbh_out u N D'.
Proof.
  intros w D B Hsimple H HinB Hinw_ex ; induction H as [ D Heq_nil | D D' B u Heq_nil Hminus_set Hbds IH | 
    D D' B u N d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HinB ; contradiction.
  destruct Hinw_ex as [ v H ] ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct HinB as [ H | HinB ] ; [ replace w with u in * by ( inversion H ; auto ) | ].
  replace N with (@nil U) in * by ( inversion H ; auto ) ; clear H w.
  apply Hdeg_out in Hnbh_out ; replace d with 0 in * by ( inversion Hnbh_out ; auto ).
  assert (~ 0 >= 1) by lia ; contradiction.
  destruct (CL (exists (v : U), In (v, w) (A D'))) as [ Hinw_ex' | Hinw_not_ex ].
  destruct IH as [ u' [ N' [ L [ R [ D'' [ Heq_lists [ Hminus_set' Hrel_src ] ] ] ] ] ] ] ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  exists u' ; exists N' ; exists ((u, N) :: L) ; exists R ; exists D'' ; split ; [ | split ] ; auto.
  simpl ; rewrite Heq_lists ; auto.
  simpl ; replace (u :: N ++ coll_bds L) with ((u :: N) ++ coll_bds L) by ( simpl ; auto ).
  apply minus_set_trans with D' ; auto.
  destruct Hinw_ex as [ v Harc_vw ].
  assert (~ In w (u :: N)) as Hw_not_in_nbh.
  intro H ; apply in_bds_in_vert with (D := D') in HinB ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; split ; [ | apply HinB ] ; simpl ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  assert (In w (V D')) as Hw_inD'.
  apply in_bds_in_vert with (D := D') in HinB ; solve [ auto ] || 
    solve [ apply HinB ; simpl ; auto ] || auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  destruct (CL (In v (V D'))) as [ Hv_inD' | Hv_not_inD' ].
  assert False ; contradiction || apply Hinw_not_ex ; exists v.
  apply Hminus_set ; split ; [ | split ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ rewrite <- H in * | ].
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; split ; simpl ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; split ; simpl ; auto.
  assert (In v (u :: N)) as Hv_in_nbh.
  assert (In v (V D)) as HinV by ( apply in_arc_in_vert in Harc_vw ; tauto ).
  apply Hminus_set in HinV ; destruct HinV as [ H | H ] ; [ simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ simpl ; auto | contradiction ].
  destruct Hv_in_nbh as [ Heq | Hv_inN ] ; [ rewrite <- Heq in * ; clear Heq v | ].
  apply Hnbh_out in Harc_vw ; assert False ; contradiction || auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; simpl ; split ; auto.
  exists u ; exists N ; exists nil ; exists B ; exists D ; split ; [ | split ; [ | split ] ] ; auto.
  simpl ; apply minus_set_nil.
  split ; [ | split ].
  intro H ; apply Hnbh_out in H ; apply Hw_not_in_nbh ; simpl ; auto.
  exists v ; split ; solve [ auto ] || solve [ apply Hnbh_out in Hv_inN ; auto ] || auto.
  intros x Harc_xw ; destruct (CL (In x (u :: N))) as [ Hx_in_nbh | Hx_not_in_nbh ].
  destruct Hx_in_nbh as [ H | H ] ; [ rewrite <- H in * ; clear H x | apply Hnbh_out ; auto ].
  apply Hnbh_out in Harc_xw ; assert False ; contradiction || auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; split ; simpl ; auto.
  assert False ; contradiction || apply Hinw_not_ex ; exists x.
  apply Hminus_set ; split ; [ | split ] ; auto.
Qed.

(* The different vertices in the breakdown schema must have disjoint neighborhoods *)
Lemma bds_nbh_disj : forall (u v : U) (M N : list U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In (u, M) B -> In (v, N) B -> u <> v -> disj M N.
Proof.
  intros u v M N D B Hsimple H HM HN Hnot_eq ; induction H as [ D Heq_nil | D D' B w Heq_nil Hminus_set Hbds IH | 
    D D' B w K d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HM ; contradiction.
  destruct HM as [ HM | HM ] ; destruct HN as [ HN | HN ].
  replace M with (@nil U) in * by ( inversion HM ; auto ).
  replace N with (@nil U) in * by ( inversion HN ; auto ).
  intros x H ; destruct H as [ H _ ] ; simpl in H ; contradiction.
  replace w with u in * by ( inversion HM ; auto ).
  replace M with (@nil U) in * by ( inversion HM ; auto ).
  intros x H ; destruct H as [ H _ ] ; simpl in H ; contradiction.
  replace w with v in * by ( inversion HN ; auto ).
  replace N with (@nil U) in * by ( inversion HN ; auto ).
  intros x H ; destruct H as [ _ H ] ; simpl in H ; contradiction.
  apply IH ; solve [ auto ] || intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  destruct HM as [ HM | HM ] ; destruct HN as [ HN | HN ].
  replace u with w in * by ( inversion HM ; auto ).
  replace v with w in * by ( inversion HN ; auto ).
  assert False ; contradiction || apply Hnot_eq ; auto.
  replace w with u in * by ( inversion HM ; auto ).
  replace K with M in * by ( inversion HM ; auto ).
  apply in_bds_in_vert with (D := D') in HN ; auto.
  intros x H ; destruct H as [ HinM HinN ].
  destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj x) ; split ; [ simpl ; auto | apply HN ; simpl ; auto ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  replace w with v in * by ( inversion HN ; auto ).
  replace K with N in * by ( inversion HN ; auto ).
  apply in_bds_in_vert with (D := D') in HM ; auto.
  intros x H ; destruct H as [ HinM HinN ].
  destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj x) ; split ; [ simpl ; auto | apply HM ; simpl ; auto ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  apply IH ; solve [ auto ] || intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
Qed.

(* The start-vertices and the neighborhoods in the breakdown schema are disjoint *)
Lemma bds_sides_disj : forall (u : U) (N : list U) (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> In (u, N) B -> disj N (map fst B).
Proof.
  intros u N D B Hsimple H HinB ; induction H as [ D Heq_nil | D D' B v Heq_nil Hminus_set Hbds IH | 
    D D' B v M d n Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ].
  simpl in HinB ; contradiction.
  simpl ; destruct HinB as [ Heq | HinB ].
  replace v with u in * by ( inversion Heq ; auto ).
  replace N with (@nil U) in * by ( inversion Heq ; auto ).
  intros w H ; destruct H as [ H _ ] ; simpl in H ; contradiction.
  intros w H ; destruct H as [ HinN [ Heq | Hin_fst ] ].
  rewrite <- Heq in * ; clear Heq w.
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj v) ; split ; [ simpl ; auto | apply HinB ; simpl ; auto ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  apply IH in HinB ; [ apply (HinB w) ; split ; auto | ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  simpl ; destruct HinB as [ Heq | HinB ].
  replace v with u in * by ( inversion Heq ; auto ).
  replace M with N in * by ( inversion Heq ; auto ).
  intros w H ; destruct H as [ HinN [ Heq' | HinB ] ].
  rewrite <- Heq' in HinN ; apply Hnbh_out in HinN ; apply Hsimple in HinN ; auto.
  apply in_map_iff in HinB ; destruct HinB as [ [ x K ] [ Heq' HinB' ] ].
  simpl in Heq' ; rewrite Heq' in * ; clear Heq' x.
  apply in_bds_in_vert with (D := D') in HinB' ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj w) ; split ; [ simpl ; auto | apply HinB' ; simpl ; auto ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  intros w H ; destruct H as [ HinN [ Heq' | HinB' ] ].
  rewrite <- Heq' in * ; clear Heq' w.
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj v) ; split ; [ simpl ; auto | apply HinB ; simpl ; auto ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
  apply IH in HinB ; [ apply (HinB w) ; split ; auto | ].
  intros x H ; apply (Hsimple x) ; apply Hminus_set in H ; tauto.
Qed.

(* If a vertex is in the result of coll_bds then it occurs somewhere in the underlying set *)
Lemma in_coll_bds : forall (u : U) (B : list (U * list U)),
  In u (coll_bds B) -> exists (v : U) (N : list U), In (v, N) B /\ In u (v :: N).
Proof.
  intros u B ; induction B as [ | [ v N ] B ] ; intro H.
  simpl in H ; contradiction.
  simpl in H ; destruct H as [ H | H ] ; [ rewrite H in * | ].
  exists u ; exists N ; simpl ; split ; auto.
  apply in_app_or in H ; destruct H as [ H | H ].
  exists v ; exists N ; simpl ; split ; auto.
  apply IHB in H ; destruct H as [ w [ M [ HinB Hin ] ] ].
  exists w ; exists M ; split ; [ simpl ; auto | auto ].
Qed.

(* Counting lemma for the coll_bds function *)
Lemma count_coll_bds : forall (B : list (U * list U)) (m n : nat),
  (forall (u : U) (N : list U), In (u, N) B -> disj N (map fst B)) ->
    (forall (u v : U) (M N : list U), In (u, M) B -> In (v, N) B -> u <> v -> disj M N) ->
      (forall (u : U) (N : list U), In (u, N) B -> N <> nil) ->
        count (map fst B) m -> count (coll_bds B) n -> 2 * m <= n.
Proof.
  intro B ; induction B as [ | [ u N ] B ] ; intros m n Hdisj_sides Hinj Hnot_nil Hm Hn.
  simpl in Hm ; inversion Hm ; lia.
  simpl in Hm ; simpl in Hn ; apply count_cases in Hm ; destruct Hm as [ [ Hin Hm ] | H ].
  destruct (count_ex (coll_bds B)) as [ k HB ] ; assert (k <= n) as Hleq.
  apply count_incl with (coll_bds B) (u :: N ++ coll_bds B) ; auto.
  intros v H ; simpl ; right ; apply in_or_app ; auto.
  transitivity k ; [ apply IHB ; auto | auto ].
  intros v N' HinB ; assert (In (v, N') ((u, N) :: B)) as H by ( simpl ; auto ).
  apply Hdisj_sides in H ; simpl in H ; intros w H' ; apply (H w) ; simpl ; split ; tauto.
  intros v w M N' HM HN' Hnot_eq ; apply (Hinj v w) ; simpl ; auto.
  intros v N' HinB ; apply (Hnot_nil v) ; simpl ; auto.
  destruct H as [ Hnot_in_fst [ k [ Hcount_fst Heq ] ] ] ; rewrite Heq ; clear Heq m.
  destruct (count_ex (coll_bds B)) as [ c Hcount_coll_bds ].
  assert (disj (u :: N) (coll_bds B)) as Hdisj.
  intros v H ; destruct H as [ Hin Hin_coll ].
  apply in_coll_bds in Hin_coll ; destruct Hin_coll as [ w [ M [ HinB Hin' ] ] ].
  destruct Hin as [ Heq | HinN ] ; destruct Hin' as [ Heq' | HinM ].
  rewrite <- Heq in * ; rewrite Heq' in * ; clear Heq Heq' v w.
  apply Hnot_in_fst ; apply in_map_iff ; exists (u, M) ; simpl ; split ; auto.
  rewrite <- Heq in * ; clear Heq v ; assert (In (w, M) ((u, N) :: B)) as H by ( simpl ; auto ).
  apply Hdisj_sides in H ; apply (H u) ; split ; simpl ; auto.
  rewrite Heq' in * ; clear Heq' w ; assert (In (u, N) ((u, N) :: B)) as H by ( simpl ; auto ).
  apply Hdisj_sides in H ; apply (H v) ; split ; simpl ; auto.
  right ; apply in_map_iff ; exists (v, M) ; simpl ; split ; auto.
  assert (In (w, M) ((u, N) :: B)) as H by ( simpl ; auto ).
  apply Hinj with (u := u) (M := N) in H ; solve [ simpl ; auto ] || solve [ apply (H v) ; split ; auto ] || auto.
  intro Heq ; rewrite Heq in * ; apply Hnot_in_fst.
  apply in_map_iff ; exists (w, M) ; split ; simpl ; auto.
  destruct (count_ex (u :: N)) as [ d Hcount_uN ].
  assert (count (u :: N ++ coll_bds B) (d + c)) as Hcount_app.
  replace (u :: N ++ coll_bds B) with ((u :: N) ++ coll_bds B) by ( simpl ; auto ) ; apply count_disj ; auto.
  assert (n = d + c) as Heq ; [ apply count_eql with (u :: N ++ coll_bds B) (u :: N ++ coll_bds B) ; 
    solve [ auto ] || split ; intros v H ; auto | rewrite Heq ; clear Heq ].
  assert (d >= 2) as Hgeq_two.
  destruct (count_rem u (u :: N) d) as [ L [ e H ] ] ; simpl ; auto.
  destruct H as [ Hu_not_inL [ HcountL [ Heql Heq ] ] ] ; destruct N as [ | w N ].
  assert (In (u, nil) ((u, nil) :: B)) as H by ( simpl ; auto ).
  apply Hnot_nil in H ; assert False ; contradiction || apply H ; auto.
  destruct (count_rem w (w :: N) e) as [ K [ f H ] ] ; simpl ; auto.
  destruct (count_ex (w :: N)) as [ f Hcount_tmp ].
  assert (e = f) as Heq' ; [ apply count_eql with L (w :: N) ; solve [ auto ] || split ; intros v H | ].
  assert (In v (u :: L)) as H' by ( simpl ; auto ) ; apply Heql in H'.
  destruct H' as [ H' | H' ] ; [ rewrite H' in * ; contradiction | auto ].
  assert (In v (u :: w :: N)) as H' by ( simpl ; auto ) ; apply Heql in H'.
  destruct H' as [ H' | H' ] ; [ rewrite <- H' in * ; clear H' v | auto ].
  assert (In (u, w :: N) ((u, w :: N) :: B)) as H' by ( simpl ; auto ) ; apply Hdisj_sides in H'.
  simpl in H' ; assert False ; contradiction || apply (H' u) ; split ; simpl ; auto.
  rewrite Heq' in * ; clear Heq' e ; auto.
  destruct H as [ Hnot_inK [ HcountK [ Heql' Heq' ] ] ] ; lia.
  assert (2 * k <= c) ; lia || apply IHB ; auto.
  intros v M HinB ; assert (In (v, M) ((u, N) :: B)) as H by ( simpl ; auto ).
  apply Hdisj_sides in H ; intros w H' ; apply (H w) ; simpl ; split ; tauto.
  intros v w M N' HinB HinB' Hnot_eq ; apply Hinj with v w ; simpl ; auto.
  intros v M HinB ; apply Hnot_nil with v ; simpl ; auto.
Qed.

(* Counting argument based on the notion that the EPON predicate is injective *)
Lemma count_epon_leq : forall (M N Q : list U) (D : digraph) (m n : nat),
  (forall (u : U), In u M -> exists (v : U), epon u v Q D /\ In v N) -> count M m -> count N n -> m <= n.
Proof.
  intro M ; induction M as [ | u M ] ; intros N Q D m n Hhas_epon HM HN ; [ inversion HM ; lia | ].
  apply count_cases in HM ; destruct HM as [ [ HinM HM ] | H ].
  apply IHM with N Q D ; solve [ auto ] || intros v H ; apply Hhas_epon ; simpl ; auto.
  destruct H as [ Hnot_inM [ m' [ HM Heq_m ] ] ].
  destruct (sub_list_ex U (fun v => epon u v Q D) N) as [ L HiffL ].
  destruct (sub_list_ex U (fun v => ~ epon u v Q D) N) as [ K HiffK ].
  destruct (count_ex L) as [ l HcountL ] ; destruct (count_ex K) as [ k HcountK ].
  assert (eql N (L ++ K)) as Heql ; [ split ; intros v H | ].
  destruct (CL (epon u v Q D)) as [ His_epon | Hnot_epon ] ; apply in_or_app ;
    [ left ; apply HiffL ; split ; auto | right ; apply HiffK ; split ; auto ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply HiffL in H | apply HiffK in H ] ; tauto.
  assert (count (L ++ K) (l + k)) as Hcount_app ; [ apply count_disj ; auto | ].
  intros v H ; destruct H as [ HinL HinK ] ; apply HiffL in HinL ; apply HiffK in HinK.
  destruct HinL as [ HinN Hepon ] ; destruct HinK as [ _ Hnot_epon ] ; contradiction.
  assert (l > 0) as Hgt_zero ; [ assert (l = 0 \/ l > 0) as H by lia ; destruct H as [ Heq | H ] ; auto | ].
  rewrite Heq in HcountL ; apply count_zero_nil in HcountL.
  assert (In u (u :: M)) as H by ( simpl ; auto ) ; apply Hhas_epon in H.
  destruct H as [ v [ Hepon HinN ] ] ; assert (In v L) as HinL by ( apply HiffL ; split ; auto ).
  rewrite HcountL in HinL ; simpl in HinL ; contradiction.
  assert (n = l + k) as Heq by ( apply count_eql with N (L ++ K) ; auto ).
  assert (m' <= k) ; lia || apply IHM with K Q D ; auto.
  intros v HinM ; assert (In v (u :: M)) as H by ( simpl ; auto ) ; apply Hhas_epon in H.
  destruct H as [ w [ Hepon HinN ] ] ; exists w ; split ; auto.
  apply HiffK ; split ; [ auto | intro Hepon' ].
  destruct Hepon as [ Hv_inQ [ Hw_not_inQ [ Harc Hepon_prop ] ] ].
  destruct Hepon' as [ Hu_inQ [ _ [ Harc' Hepon_prop' ] ] ].
  apply Hepon_prop in Harc' ; auto.
  rewrite Harc' in * ; contradiction.
Qed.

(* Helper lemma for the coll_bds predicate *)
Lemma coll_bds_in : forall (B : list (U * list U)) (u : U) (N : list U),
  In (u, N) B -> incl (u :: N) (coll_bds B).
Proof.
  intro B ; induction B as [ | [ v M ] B ] ; intros u N H ; [ simpl in H ; contradiction | ].
  destruct H as [ H | H ] ; [ replace v with u in * by ( inversion H ; auto ) | ].
  replace M with N in * by ( inversion H ; auto ) ; clear H v M ; simpl.
  intros v H ; destruct H as [ H | H ] ; simpl ; auto.
  right ; apply in_or_app ; auto.
  apply IHB in H ; simpl ; intros w H'.
  apply H in H' ; simpl ; right ; apply in_or_app ; auto.
Qed.

(* Helper lemma to handle the coll_bds_nbh predicate *)
Lemma coll_bds_nbh_in : forall (B : list (U * list U)) (u v : U) (N : list U),
  In (u, N) B -> In v N -> In v (coll_bds_nbh B).
Proof.
  intro B ; induction B as [ | [ w M ] B ] ; intros u v N HinB HinN ; [ simpl in HinB ; contradiction | ].
  destruct HinB as [ H | H ] ; [ replace w with u in * by ( inversion H ; auto ) | ].
  replace M with N in * by ( inversion H ; auto ) ; clear H M w ; simpl ; apply in_or_app ; auto.
  apply IHB with (v := v) in H ; solve [ auto ] || simpl ; apply in_or_app ; auto.
Qed.

(* Another helper lemma to handle the coll_bds_nbh predicate *)
Lemma in_coll_bds_nbh : forall (B : list (U * list U)) (u : U),
  In u (coll_bds_nbh B) -> exists (v : U) (N : list U), In (v, N) B /\ In u N.
Proof.
  intro B ; induction B as [ | [ v N ] B ] ; intros u H ; [ simpl in H ; contradiction | ].
  simpl in H ; apply in_app_or in H ; destruct H as [ H | H ].
  exists v ; exists N ; split ; simpl ; auto.
  apply IHB in H ; destruct H as [ w [ M [ HinB HinN ] ] ].
  exists w ; exists M ; split ; simpl ; auto.
Qed.

(* Counting argument for related sources under the same neighborhood in the breakdown schema *)
Lemma count_rel_src : forall (D D' : digraph) (B L R : list (U * list U)) (u : U) (N C : list U) (n c : nat),
  simple D -> bds D B -> B = L ++ (u, N) :: R -> minus_set (coll_bds L) D' D -> 
    all_rel_src u C D' -> count N n -> count C c -> c <= n.
Proof.
  intros D D' B L R u N C n a Hsimple H Heq_list Hminus_set Hall_rel_src HN HC ; 
    revert Heq_list Hminus_set Hall_rel_src ; revert L R D' ; 
    induction H as [ D Heq_nil | D D'' B v Heq_nil Hminus_set' Hbds IH | 
    D D'' B v M d k Hminus_set' Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ] ;
    intros L R D' Heq_list Hminus_set Hall_rel_src.
  destruct L as [ | [ v M ] L ] ; simpl in Heq_list ; inversion Heq_list.
  destruct C as [ | w C ] ; [ inversion HC ; lia | ].
  assert (rel_src u w D') as Hrel_src by ( apply Hall_rel_src ; simpl ; auto ).
  destruct Hrel_src as [ _ [ H _ ] ] ; destruct H as [ x [ Harc Harc' ] ].
  apply Hminus_set in Harc ; destruct Harc as [ H _ ] ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct L as [ | [ w K ] L ] ; simpl in Heq_list.
  assert ((v, M) = (u, N)) as H by ( inversion Heq_list ; auto ).
  replace v with u in * by ( inversion H ; auto ).
  replace M with N in * by ( inversion H ; auto ).
  replace R with B in * by ( inversion Heq_list ; auto ) ; clear Heq_list H v M R.
  assert (all_rel_src u C D) as Hall_rel_src' ; simpl in Hminus_set.
  assert (eql (V D) (V D')) as HeqlV.
  split ; intros w H ; [ apply Hminus_set in H ; simpl in H ; auto | apply Hminus_set ; simpl ; auto ].
  assert (forall (x y : U), In (x, y) (A D) <-> In (x, y) (A D')) as HeqlA.
  intros x y ; split ; intro H ; [ apply Hminus_set ; split ; [ | split ] ; tauto | apply Hminus_set in H ; tauto ].
  assert (forall (w : U), rel_src u w D <-> rel_src u w D') as Hrel_src_eqv.
  intro w ; split ; intro H ; destruct H as [ Hnot_in [ Hex_conn Hrel_src_prop ] ].
  split ; [ intro H ; apply Hnot_in ; apply HeqlA ; auto | split ].
  destruct Hex_conn as [ v [ Harc Harc' ] ] ; exists v ; split ; apply HeqlA ; auto.
  intros v H ; apply HeqlA ; apply HeqlA in H ; auto.
  split ; [ intro H ; apply Hnot_in ; apply HeqlA ; auto | split ].
  destruct Hex_conn as [ v [ Harc Harc' ] ] ; exists v ; split ; apply HeqlA ; auto.
  intros v H ; apply HeqlA ; apply HeqlA in H ; auto.
  intro w ; split ; intro H ; [ apply Hall_rel_src in H ; apply Hrel_src_eqv in H ; auto | ].
  apply Hall_rel_src ; apply Hrel_src_eqv ; auto.
  apply Hnum_rel_src in Hall_rel_src' ; assert (a = k) as Heq by ( apply count_univ with C ; auto ).
  assert (n = d) as Heq' ; lia || apply count_univ with N ; auto.
  assert (B = L ++ (u, N) :: R) as H by ( inversion Heq_list ; auto ).
  apply IH with (D' := D') in H ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set' in Harc ; tauto.
  assert ((v, M) = (w, K)) as Heq by ( inversion Heq_list ; auto ).
  replace w with v in * by ( inversion Heq ; auto ).
  replace K with M in * by ( inversion Heq ; auto ) ; clear Heq w K ; split ; [ split ; intros w H' | split ].
  apply in_app_or in H' ; destruct H' as [ H' | H' ].
  apply in_coll_bds in H' ; destruct H' as [ x [ K [ HinL Hin ] ] ].
  assert (In (x, K) B) as HinB by ( rewrite H ; apply in_or_app ; auto ).
  apply in_bds_in_vert with (D := D'') in HinB ; auto.
  intros y Harc ; apply (Hsimple y) ; apply Hminus_set' in Harc ; tauto.
  assert (In w (coll_bds ((v, M) :: L) ++ V D')) as Hin by ( apply in_or_app ; auto ).
  apply Hminus_set in Hin ; apply Hminus_set' in Hin.
  apply in_app_or in Hin ; destruct Hin as [ Hin | Hin ] ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj w) ; split ; simpl ; simpl in Hin ; auto.
  destruct Hin as [ Heq | HinM ] ; [ auto | right ; apply in_or_app ; auto ].
  assert (In w ((v :: M) ++ V D'')) as Hin by ( apply in_or_app ; auto ).
  apply Hminus_set' in Hin ; apply Hminus_set in Hin.
  simpl in Hin ; destruct Hin as [ Heq | Hin ] ; [ rewrite <- Heq in * ; clear Heq w | ].
  assert False ; contradiction || destruct Hminus_set' as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; split ; simpl ; auto.
  apply in_app_or in Hin ; destruct Hin as [ Hin | Hin ] ; [ | apply in_or_app ; auto ].
  apply in_app_or in Hin ; destruct Hin as [ Hin | Hin ] ; [ | apply in_or_app ; auto ].
  assert False ; contradiction || destruct Hminus_set' as [ _ [ Hdisj _ ] ] ; apply (Hdisj w) ; split ; simpl ; auto.
  intros w H' ; destruct H' as [ HinL HinVD' ] ; destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj w) ; simpl; split ; auto.
  right ; apply in_or_app ; auto.
  intros x y ; split ; intro H' ; [ apply Hminus_set in H' | ].
  destruct H' as [ Harc [ Hx Hy ] ] ; split ; [ | split ].
  apply Hminus_set' ; split ; [ | split ] ; auto.
  intro H' ; apply Hx ; simpl ; destruct H' as [ H' | H' ] ; auto.
  right ; apply in_or_app ; auto.
  intro H' ; apply Hy ; simpl ; destruct H' as [ H' | H' ] ; auto.
  right ; apply in_or_app ; auto.
  intro H' ; apply Hx ; simpl ; right ; apply in_or_app ; auto.
  intro H' ; apply Hy ; simpl ; right ; apply in_or_app ; auto.
  destruct H' as [ H' [ Hx Hy ] ] ; apply Hminus_set.
  apply Hminus_set' in H' ; destruct H' as [ Harc [ Hx' Hy' ] ] ; split ; [ | split ] ; auto.
  intro H' ; destruct H' as [ H' | H' ] ; apply Hx' ; simpl ; auto.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; contradiction || auto.
  intro H' ; destruct H' as [ H' | H' ] ; apply Hy' ; simpl ; auto.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; contradiction || auto.
Qed.

(* Counting argument for all related sources of a subset of the breakdown schema (used only for the a-steps) *)
Lemma count_all_rel_src : forall (D : digraph) (B : list (U * list U)),
  simple D -> bds D B -> forall (F : list U) (T : list (U * list U)) (m n : nat), incl T B ->
    (forall (w : U), In w F -> exists (u : U) (N : list U) (L R : list (U * list U)) (D' : digraph),
      B = L ++ (u, N) :: R /\ In (u, N) T /\ minus_set (coll_bds L) D' D /\ rel_src u w D') ->
    count (coll_bds_nbh T) n -> count F m -> m <= n.
Proof.
  intros D B Hsimple H ; induction H as [ D Heq_nil | D D' B u Heq_nil Hminus_set Hbds IH | 
    D D' B u N d k Hminus_set Hnbh_out Hdeg_out Hnum_rel_src Hgeq_one Hgeq_n Hbds IH ] ;
    intros F T m n Hincl His_rel_src HcountT HcountF.
  destruct F as [ | w F ] ; [ inversion HcountF ; lia | ].
  assert (In w (w :: F)) as H by ( simpl ; auto ) ; apply His_rel_src in H.
  destruct H as [ u [ N [ L [ R [ D' [ _ [ H _ ] ] ] ] ] ] ] ; apply Hincl in H ; simpl in H ; contradiction.
  destruct F as [ | w F ] ; [ inversion HcountF ; lia | ].
  assert (In w (w :: F)) as H by ( simpl ; auto ) ; apply His_rel_src in H.
  destruct H as [ u' [ N' [ L [ R [ D'' H ] ] ] ] ].
  destruct H as [ Heql_list [ HinT [ Hminus_set' Hrel_src ] ] ].
  destruct Hrel_src as [ _ [ H _ ] ] ; destruct H as [ v [ Harc _ ] ].
  apply Hminus_set' in Harc ; destruct Harc as [ H _ ] ; rewrite Heq_nil in H ; simpl in H ; contradiction.
  destruct (CL (In (u, N) T)) as [ HinT | Hnot_inT ].
  destruct (sub_list_ex (U * list U) (fun uN => uN <> (u, N)) T) as [ T' HiffT' ].
  destruct (sub_list_ex U (fun w => rel_src u w D) F) as [ W HiffW ].
  assert (eql (coll_bds_nbh T) (coll_bds_nbh T' ++ N)) as Heql_coll_bds_nbh.
  split ; intros v H ; [ apply in_coll_bds_nbh in H | ].
  destruct H as [ w [ M [ HinT' HinM ] ] ] ; destruct (CL ((w, M) = (u, N))) as [ Heq | Hnot_eq ].
  replace M with N in * by ( inversion Heq ; auto ) ; apply in_or_app ; auto.
  apply in_or_app ; left ; apply coll_bds_nbh_in with w M ; solve [ auto ] || apply HiffT' ; split ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; [ | apply coll_bds_nbh_in with u N ; auto ].
  apply in_coll_bds_nbh in H ; destruct H as [ w [ M [ HinT' HinM ] ] ].
  apply HiffT' in HinT' ; destruct HinT' as [ HinT' Hnot_eq ] ; apply coll_bds_nbh_in with w M ; auto.
  assert (disj (coll_bds_nbh T') N) as Hdisj_coll_bds_nbh.
  intros v H ; destruct H as [ HinT' HinN ] ; apply in_coll_bds_nbh in HinT'.
  destruct HinT' as [ w [ M [ HinT' HinN' ] ] ] ; apply HiffT' in HinT'.
  destruct HinT' as [ HinT' Hnot_eq ] ; apply Hincl in HinT'.
  destruct HinT' as [ Heq | HinB ] ; [ symmetry in Heq ; contradiction | ].
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj v) ; split ; [ | apply HinB ] ; simpl ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  destruct (count_ex (coll_bds_nbh T')) as [ n' HcountT' ].
  assert (n = n' + d) as Heq' ; [ apply count_eql with (coll_bds_nbh T) (coll_bds_nbh T' ++ N) ; 
    solve [ auto ] || apply count_disj ; auto | ].
  destruct (count_ex W) as [ c HcountW ] ; assert (c <= d) as Hleq.
  destruct (sub_list_ex U (fun w => rel_src u w D) (V D)) as [ R HiffR ].
  destruct (count_ex R) as [ r HcountR ] ; transitivity r.
  apply count_incl with W R ; auto.
  intros w H ; apply HiffW in H ; destruct H as [ HinF Hrel_src ] ; apply HiffR ; split ; auto.
  destruct Hrel_src as [ _ [ H _ ] ] ; destruct H as [ v [ _ Harc ] ] ; apply in_arc_in_vert in Harc ; tauto.
  assert (forall (w : U), In w R <-> rel_src u w D) as Hiff_no_VD.
  intro w ; split ; intro H ; [ apply HiffR in H ; tauto | apply HiffR ; split ; auto ].
  destruct H as [ _ [ H _ ] ] ; destruct H as [ v [ _ Harc ] ] ; apply in_arc_in_vert in Harc ; tauto.
  apply Hnum_rel_src in Hiff_no_VD ; assert (r = k) ; lia || apply count_univ with R ; auto.
  destruct (sub_list_ex U (fun w => ~ In w W) F) as [ X HiffX ].
  assert (eql F (W ++ X)) as HeqlF ; [ split ; intros w H | ].
  destruct (CL (In w W)) as [ HinW | Hnot_inW ] ; apply in_or_app ; auto.
  right ; apply HiffX ; split ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply HiffW in H | apply HiffX in H ] ; tauto.
  assert (disj W X) as HdisjF ; [ intros w H ; destruct H as [ HinW HinX ] | ].
  apply HiffX in HinX ; destruct HinX ; contradiction.
  destruct (count_ex X) as [ m' HcountX ].
  assert (m = c + m') as Heq'' ; [ apply count_eql with F (W ++ X) ; solve [ auto ] || apply count_disj ; auto | ].
  assert (m' <= n') ; lia || apply IH with X T' ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  intros wM H ; destruct wM as [ w M ].
  apply HiffT' in H ; destruct H as [ HinT' Hnot_eq ].
  apply Hincl in HinT' ; destruct HinT' as [ Heq | HinB ] ; [ symmetry in Heq ; contradiction | auto ].
  intros w HinX ; apply HiffX in HinX ; destruct HinX as [ HinF Hnot_inW ] ; assert (In w F) as HinF' by auto.
  apply His_rel_src in HinF ; destruct HinF as [ u' [ N' [ L [ R [ D'' H ] ] ] ] ].
  destruct H as [ Heq_list [ HinT' [ Hminus_set' Hrel_src ] ] ].
  destruct L as [ | [ x K ] L ] ; [ simpl in Heq_list | ].
  assert ((u, N) = (u', N')) as Heq_pair by ( inversion Heq_list ; auto ).
  replace u' with u in * by ( inversion Heq_pair ; auto ).
  replace N' with N in * by ( inversion Heq_pair ; auto ) ; clear Heq_pair u' N' ; simpl in Hminus_set'.
  assert (eql (V D'') (V D)) as HeqlV.
  split ; intros x H ; [ apply Hminus_set' ; simpl ; auto | apply Hminus_set' in H ; simpl in H ; auto ].
  assert (forall (x y : U), In (x, y) (A D'') <-> In (x, y) (A D)) as HeqlA.
  intros x y ; split ; intro H ; [ apply Hminus_set' in H ; tauto | ].
  apply Hminus_set' ; split ; [ | split ] ; auto.
  assert (rel_src u w D) as Hrel_src'.
  destruct Hrel_src as [ Hno_arc [ Hex_conn Hrel_src_prop ] ] ; split ; [ | split ].
  intro H ; apply Hno_arc ; apply HeqlA ; auto.
  destruct Hex_conn as [ v [ Harc Harc' ] ] ; exists v ; split ; solve [ auto ] || apply HeqlA ; auto.
  intros v Harc ; apply HeqlA ; apply Hrel_src_prop ; apply HeqlA ; auto.
  assert (In w W) ; contradiction || apply HiffW ; split ; auto.
  simpl in Heq_list ; assert ((u, N) = (x, K)) as Heq_pair by ( inversion Heq_list ; auto ).
  replace x with u in * by ( inversion Heq_pair ; auto ).
  replace K with N in * by ( inversion Heq_pair ; auto ) ; clear Heq_pair x K.
  assert (B = L ++ (u', N') :: R) as Heq_list' by ( inversion Heq_list ; auto ).
  exists u' ; exists N' ; exists L ; exists R ; exists D'' ; split ; [ | split ; [ | split ] ] ; auto.
  apply HiffT' ; split ; [ auto | intro Heq_pair ].
  replace u' with u in * by ( inversion Heq_pair ; auto ).
  replace N' with N in * by ( inversion Heq_pair ; auto ) ; clear Heq_pair u' N'.
  assert (In (u, N) B) as HinB by ( rewrite Heq_list' ; apply in_or_app ; simpl ; auto ).
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  destruct Hminus_set as [ _ [ Hdisj _ ] ] ; apply (Hdisj u) ; split ; [ | apply HinB ] ; simpl ; auto.
  intros x Harc ; apply (Hsimple x) ; apply Hminus_set in Harc ; tauto.
  split ; [ split ; intros x H | split ].
  apply in_app_or in H ; destruct H as [ H | H ].
  apply in_coll_bds in H ; destruct H as [ v [ M [ HinL Hin ] ] ].
  assert (In (v, M) B) as HinB by ( rewrite Heq_list' ; apply in_or_app ; auto ).
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  intros y Harc ; apply (Hsimple y) ; apply Hminus_set in Harc ; tauto.
  assert (In x (coll_bds ((u, N) :: L) ++ V D'')) as H' by ( apply in_or_app ; auto ).
  apply Hminus_set' in H' ; apply Hminus_set in H'.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; auto.
  assert False ; contradiction || destruct Hminus_set' as [ _ [ Hdisj _ ] ].
  apply (Hdisj x) ; split ; [ | auto ].
  simpl ; destruct H' as [ H' | H' ] ; [ auto | right ; apply in_or_app ; auto ].
  assert (In x ((u :: N) ++ V D')) as H' by ( apply in_or_app ; auto ).
  apply Hminus_set in H' ; apply Hminus_set' in H'.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; apply in_or_app ; auto.
  simpl in H' ; destruct H' as [ H' | H' ] ; [ rewrite <- H' in * | ].
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj u) ; simpl ; split ; auto.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj u) ; simpl ; split ; auto.
  assert False ; contradiction || apply (Hdisj x) ; simpl ; split ; auto.
  intros x H ; destruct H as [ HinL HinD'' ].
  destruct Hminus_set' as [ _ [ Hdisj _ ] ] ; apply (Hdisj x) ; split ; auto.
  simpl ; right ; apply in_or_app ; auto.
  intros x y ; split ; intro H.
  apply Hminus_set' in H ; destruct H as [ Harc [ Hx Hy ] ] ; split ; [ | split ] ; auto.
  apply Hminus_set ; split ; [ | split ] ; auto.
  intro H ; apply Hx ; simpl ; destruct H as [ H | H ] ; [ | right ; apply in_or_app ] ; auto.
  intro H ; apply Hy ; simpl ; destruct H as [ H | H ] ; [ | right ; apply in_or_app ] ; auto.
  intro H ; apply Hx ; simpl ; right ; apply in_or_app ; auto.
  intro H ; apply Hy ; simpl ; right ; apply in_or_app ; auto.
  destruct H as [ H [ Hx Hy ] ] ; apply Hminus_set in H ; destruct H as [ Harc [ Hx' Hy' ] ].
  apply Hminus_set' ; split ; [ | split ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ apply Hx' ; simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hx' ; simpl ; auto | contradiction ].
  intro H ; destruct H as [ H | H ] ; [ apply Hy' ; simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hy' ; simpl ; auto | contradiction ]. 
  apply IH with F T ; auto.
  intros y Harc ; apply (Hsimple y) ; apply Hminus_set in Harc ; tauto.
  intros vM H ; assert (In vM T) as H' by auto ; destruct vM as [ v M ] ; apply Hincl in H.
  destruct H as [ H | H ] ; [ rewrite H in * ; contradiction | auto ].
  intros w H ; apply His_rel_src in H ; destruct H as [ u' [ N' [ L [ R [ D'' H ] ] ] ] ].
  destruct H as [ Heq_list [ HinT [ Hminus_set' Hrel_src ] ] ].
  destruct L as [ | [ v M ] L ] ; [ simpl in Heq_list | ].
  assert ((u, N) = (u', N')) as Heq_pair by ( inversion Heq_list ; auto ).
  replace u' with u in * by ( inversion Heq_pair ; auto ).
  replace N' with N in * by ( inversion Heq_pair ; auto ) ; contradiction.
  simpl in Heq_list ; assert ((u, N) = (v, M)) as Heq_pair by ( inversion Heq_list ; auto ).
  replace v with u in * by ( inversion Heq_pair ; auto ).
  replace M with N in * by ( inversion Heq_pair ; auto ) ; clear Heq_pair M v.
  assert (B = L ++ (u', N') :: R) as Heq_list' by ( inversion Heq_list ; auto ).
  exists u' ; exists N' ; exists L ; exists R ; exists D'' ; split ; [ | split ; [ | split ] ] ; auto.
  split ; [ split ; intros x H | split ].
  apply in_app_or in H ; destruct H as [ H | H ].
  apply in_coll_bds in H ; destruct H as [ v [ M [ HinL Hin ] ] ].
  assert (In (v, M) B) as HinB by ( rewrite Heq_list' ; apply in_or_app ; auto ).
  apply in_bds_in_vert with (D := D') in HinB ; auto.
  intros y Harc ; apply (Hsimple y) ; apply Hminus_set in Harc ; tauto.
  assert (In x (coll_bds ((u, N) :: L) ++ V D'')) as H' by ( apply in_or_app ; auto ).
  apply Hminus_set' in H' ; apply Hminus_set in H'.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; auto.
  assert False ; contradiction || destruct Hminus_set' as [ _ [ Hdisj _ ] ].
  apply (Hdisj x) ; split ; [ | auto ].
  simpl ; destruct H' as [ H' | H' ] ; [ auto | right ; apply in_or_app ; auto ].
  assert (In x ((u :: N) ++ V D')) as H' by ( apply in_or_app ; auto ).
  apply Hminus_set in H' ; apply Hminus_set' in H'.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; apply in_or_app ; auto.
  simpl in H' ; destruct H' as [ H' | H' ] ; [ rewrite <- H' in * | ].
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj u) ; simpl ; split ; auto.
  apply in_app_or in H' ; destruct H' as [ H' | H' ] ; auto.
  assert False ; contradiction || destruct Hminus_set as [ _ [ Hdisj _ ] ].
  apply (Hdisj u) ; simpl ; split ; auto.
  assert False ; contradiction || apply (Hdisj x) ; simpl ; split ; auto.
  intros x H ; destruct H as [ HinL HinD'' ].
  destruct Hminus_set' as [ _ [ Hdisj _ ] ] ; apply (Hdisj x) ; split ; auto.
  simpl ; right ; apply in_or_app ; auto.
  intros x y ; split ; intro H.
  apply Hminus_set' in H ; destruct H as [ Harc [ Hx Hy ] ] ; split ; [ | split ] ; auto.
  apply Hminus_set ; split ; [ | split ] ; auto.
  intro H ; apply Hx ; simpl ; destruct H as [ H | H ] ; [ | right ; apply in_or_app ] ; auto.
  intro H ; apply Hy ; simpl ; destruct H as [ H | H ] ; [ | right ; apply in_or_app ] ; auto.
  intro H ; apply Hx ; simpl ; right ; apply in_or_app ; auto.
  intro H ; apply Hy ; simpl ; right ; apply in_or_app ; auto.
  destruct H as [ H [ Hx Hy ] ] ; apply Hminus_set in H ; destruct H as [ Harc [ Hx' Hy' ] ].
  apply Hminus_set' ; split ; [ | split ] ; auto.
  intro H ; destruct H as [ H | H ] ; [ apply Hx' ; simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hx' ; simpl ; auto | contradiction ].
  intro H ; destruct H as [ H | H ] ; [ apply Hy' ; simpl ; auto | ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply Hy' ; simpl ; auto | contradiction ].
Qed.

(* We can now formulate and prove the Small Quasi-Kernel Conjecture (under the axiom as stated above) *)
Theorem SQKC : forall (D : digraph) (n : nat), simple D -> src_free D -> count (V D) n ->
  exists (Q : list U) (m : nat), qkernel Q D /\ count Q m /\ 2 * m <= n.
Proof.
  intros D n Hsimple Hsrc_free Hcount ; destruct (bds_ex D Hsimple) as [ B Hbds ].
  destruct (qkernel_smallest_ex D B Hsimple Hbds) as [ Q Hqkernel_smallest ].
  destruct (count_ex Q) as [ m Hcount' ] ; exists Q ; exists m ; split ; [ | split ] ; 
    solve [ auto ] || solve [ destruct Hqkernel_smallest ; auto ] || auto.
  destruct (sub_list_ex U (fun u => In (u, nil) B) Q) as [ R HiffR ].
  destruct (sub_list_ex U (fun u => exists (N : list U), In (u, N) B /\ N <> nil) Q) as [ T HiffT ].
  destruct (count_ex R) as [ r HcountR ] ; destruct (count_ex T) as [ t HcountT ].
  assert (m = r + t) as Heq_m_rt ; [ apply count_eql with Q (R ++ T) ; auto | ].
  split ; intros u H ; [ assert (In u Q) as Hin' by auto ; apply Hqkernel_smallest in H | ].
  apply in_map_iff in H ; destruct H as [ [ v N ] [ Heq Hin ] ].
  simpl in Heq ; rewrite Heq in * ; clear Heq v ; apply in_or_app.
  destruct (CL (N = nil)) as [ Heq_nil | Hnot_eq_nil ].
  left ; apply HiffR ; split ; [ auto | rewrite Heq_nil in * ; auto ].
  right ; apply HiffT ; split ; [ auto | exists N ; split ; auto ].
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply HiffR in H | apply HiffT in H ] ; tauto.
  apply count_disj ; solve [ auto ] || intros u H ; destruct H as [ HinR HinT ].
  apply HiffR in HinR ; apply HiffT in HinT ; destruct HinR as [ _ HinB ].
  destruct HinT as [ _ [ N [ HinB' Hnot_nil ] ] ] ; assert (N = nil) ; 
    contradiction || apply bds_rhs_inj with u D B ; auto.
  rewrite Heq_m_rt ; replace (2 * (r + t)) with (2 * r + 2 * t) by lia.
  destruct (sub_list_ex (U * list U) (fun uN => ~ In (fst uN) Q) B) as [ R' HiffR' ].
  destruct (sub_list_ex (U * list U) (fun uN => In (fst uN) Q /\ snd uN <> nil) B) as [ T' HiffT' ].
  assert (incl (R ++ coll_bds R' ++ coll_bds T') (V D)) as Hincl_in_vert.
  intros u H ; apply in_app_or in H ; destruct H as [ H | H ].
  apply HiffR in H ; destruct H as [ _ HinB ].
  apply in_bds_in_vert with (D := D) in HinB ; solve [ auto ] || apply HinB ; simpl ; auto.
  apply in_app_or in H ; destruct H as [ H | H ].
  apply in_coll_bds in H ; destruct H as [ v [ N [ HinR' Hin ] ] ].
  apply HiffR' in HinR' ; destruct HinR' as [ HinB _ ].
  apply in_bds_in_vert with (D := D) in HinB ; auto.
  apply in_coll_bds in H ; destruct H as [ v [ N [ HinT' Hin ] ] ].
  apply HiffT' in HinT' ; destruct HinT' as [ HinB _ ].
  apply in_bds_in_vert with (D := D) in HinB ; auto.
  assert (disj (coll_bds R') (coll_bds T')) as Hdisj_coll_bds.
  intros u H ; destruct H as [ HinR' HinT' ].
  apply in_coll_bds in HinR' ; apply in_coll_bds in HinT'.
  destruct HinR' as [ v [ M [ HinR' Hv_in ] ] ].
  destruct HinT' as [ w [ N [ HinT' Hw_in ] ] ].
  apply HiffR' in HinR' ; destruct HinR' as [ HinB Hnot_inQ ] ; simpl in Hnot_inQ.
  apply HiffT' in HinT' ; destruct HinT' as [ HinB' [ HinQ _ ] ] ; simpl in HinQ.
  destruct Hv_in as [ Heq | HinM ] ; destruct Hw_in as [ Heq' | HinN ].
  rewrite Heq in * ; clear Heq v ; rewrite Heq' in * ; clear Heq' w ; contradiction.
  rewrite Heq in * ; clear Heq v ; apply bds_sides_disj with (D := D) in HinB' ; auto.
  apply (HinB' u) ; split ; [ auto | apply in_map_iff ; exists (u, M) ; split ; simpl ; auto ].
  rewrite Heq' in * ; clear Heq' w ; apply bds_sides_disj with (D := D) in HinB ; auto.
  apply (HinB u) ; split ; [ auto | apply in_map_iff ; exists (u, N) ; split ; simpl ; auto ].
  destruct (CL (v = w)) as [ Heq | Hnot_eq ] ; [ rewrite Heq in * ; contradiction | ].
  apply bds_nbh_disj with (u := v) (M := M) (D := D) in HinB' ; auto.
  apply (HinB' u) ; split ; auto.
  destruct (count_ex (coll_bds R')) as [ r' HcountR' ].
  destruct (count_ex (coll_bds T')) as [ t' HcountT' ].
  assert (r + r' + t' <= n) as Hleq.
  apply count_incl with (R ++ coll_bds R' ++ coll_bds T') (V D) ; auto.
  rewrite app_assoc ; apply count_disj ; auto.
  intros u H ; destruct H as [ H HinT' ].
  apply in_app_or in H ; destruct H as [ HinR | HinR' ].
  apply HiffR in HinR ; apply in_coll_bds in HinT'.
  destruct HinT' as [ v [ N [ HinT' Hin ] ] ] ; apply HiffT' in HinT'.
  destruct HinR as [ HinQ HinB ] ; simpl in HinT' ; destruct HinT' as [ HinB' [ HinQ' Hnot_nil ] ].
  destruct Hin as [ Heq | HinN ] ; [ rewrite Heq in * ; clear Heq v | ].
  apply bds_rhs_inj with (M := @nil U) (D := D) in HinB' ; auto.
  apply bds_sides_disj with (D := D) in HinB' ; auto.
  apply (HinB' u) ; split ; auto.
  apply in_map_iff ; exists (u, nil) ; simpl ; split ; auto.
  apply (Hdisj_coll_bds u) ; split ; auto.
  apply count_disj ; auto.
  intros u H ; destruct H as [ HinR HinR' ] ; apply HiffR in HinR.
  apply in_coll_bds in HinR' ; destruct HinR' as [ v [ N [ HinR' Hin ] ] ].
  destruct Hin as [ Heq | HinN ] ; [ rewrite Heq in * ; clear Heq v | ].
  apply HiffR' in HinR' ; simpl in HinR' ; destruct HinR ; destruct HinR' ; contradiction.
  destruct HinR as [ HinQ HinB ] ; apply HiffR' in HinR'.
  simpl in HinR' ; destruct HinR' as [ HinB' Hnot_inQ ].
  apply bds_sides_disj with (D := D) in HinB' ; auto.
  apply (HinB' u) ; split ; auto.
  apply in_map_iff ; exists (u, nil) ; split ; simpl ; auto.
  transitivity (r + r' + t') ; auto.
  clear Hleq ; assert (2 * t <= t') as Hleq ; [ | assert (r <= r') ; lia || auto ].
  apply count_coll_bds with (B := T') ; auto.
  intros u N HinT' ; apply HiffT' in HinT' ; destruct HinT' as [ H _ ].
  apply bds_sides_disj with (D := D) in H ; auto.
  intros v H' ; apply (H v) ; split ; [ tauto | ].
  destruct H' as [ _ H' ] ; apply in_map_iff in H'.
  destruct H' as [ [ w M ] [ Heq HinT' ] ] ; simpl in Heq ; rewrite Heq in *.
  apply HiffT' in HinT' ; apply in_map_iff ; exists (v, M) ; split ; simpl ; tauto.
  intros u v M N HM HN Hnot_eq ; apply bds_nbh_disj with u v D B ; solve [ auto ] ||
    apply HiffT' in HM ; apply HiffT' in HN ; tauto.
  intros u N HinT' ; apply HiffT' in HinT' ; simpl in HinT' ; tauto.
  assert (eql T (map fst T')) as Heql ; [ split ; intros u H | ].
  apply HiffT in H ; destruct H as [ HinQ [ N [ HinB Hnot_nil ] ] ].
  assert (In (u, N) T') as HinT' by (  apply HiffT' ; simpl ; split ; [ | split ] ; auto ).
  apply in_map_iff ; exists (u, N) ; simpl ; split ; auto.
  apply in_map_iff in H ; destruct H as [ [ v N ] [ Heq HinT' ] ] ; simpl in Heq ; rewrite Heq in *.
  apply HiffT' in HinT' ; apply HiffT ; simpl in HinT' ; split ; [ | exists N ; split ] ; tauto.
  destruct (count_ex (map fst T')) as [ c Hcount_fst ].
  assert (t = c) as Heq ; [ apply count_eql with T (map fst T') ; auto | rewrite Heq in * ; auto ].
  destruct (sub_list_ex U (fun u => under_b_step u Q B D) R) as [ Rb HiffRb ].
  assert (forall (u : U), In u Rb -> exists (v : U), epon u v Q D /\ In v (map fst R')) as Hhas_epon.
  intros u HinRb ; apply HiffRb in HinRb ; destruct HinRb as [ HinR Hunder_b_step ].
  apply HiffR in HinR ; destruct HinR as [ HinQ HinB ].
  apply qkernel_smallest_epon in Hunder_b_step ; auto.
  destruct Hunder_b_step as [ v [ Hepon Hin_fst ] ] ; exists v ; split ; auto.
  apply in_map_iff in Hin_fst ; destruct Hin_fst as [ [ w N ] [ Heq Hin ] ].
  simpl in Heq ; rewrite Heq in * ; clear Heq w.
  apply in_map_iff ; exists (v, N) ; split ; auto.
  apply HiffR' ; simpl ; split ; auto.
  intro HinQ' ; destruct Hepon as [ _ [ H' _ ] ] ; contradiction.
  destruct (count_ex Rb) as [ b HcountRb ] ; destruct (count_ex (map fst R')) as [ c Hcount_fstR' ].
  assert (b <= c) as Hleq_bc by ( apply count_epon_leq with Rb (map fst R') Q D ; auto ).
  destruct (sub_list_ex U (fun v => ~ under_b_step v Q B D) R) as [ Ra HiffRa ].
  assert (forall (w : U), In w Ra -> exists (u : U) (N : list U) (L R : list (U * list U)) (D' : digraph),
      B = L ++ (u, N) :: R /\ minus_set (coll_bds L) D' D /\ 
        rel_src u w D' /\ nbh_out u N D' /\ ~ In u Q) as HRa_rel_src.
  intros w H ; apply HiffRa in H ; destruct H as [ HinR Hnot_under_b_step ].
  apply HiffR in HinR ; destruct HinR as [ HinQ HinB ] ; apply with_nil_rel_src with (D := D) in HinB ; auto.
  destruct HinB as [ u [ N [ L [ K [ D' [ Heq_list [ Hminus_set [ Hrel_src Hnbh_out ] ] ] ] ] ] ] ].
  exists u ; exists N ; exists L ; exists K ; exists D' ; split ; [ | split ; [ | split ; [ | split ] ] ] ; auto.
  intro HinQ' ; assert (under_b_step w Q B D) ; contradiction || auto.
  unfold rel_src in Hrel_src ; destruct Hrel_src as [ Hno_arc [ Hex_conn Hrel_src_prop ] ].
  destruct Hex_conn as [ v [ Harc_uv Harc_vw ] ].
  exists u ; exists v ; exists N ; split ; [ | split ; [ | split ] ] ; auto.
  rewrite Heq_list ; apply in_or_app ; right ; simpl ; auto.
  apply Hnbh_out in Harc_uv ; auto.
  apply Hminus_set in Harc_vw ; tauto.
  apply Hsrc_free ; destruct Hqkernel_smallest as [ Hqkernel _ ].
  destruct Hqkernel as [ [ Hincl _ ] _ ] ; apply Hincl ; auto.
  destruct (count_ex Ra) as [ a HcountRa ].
  assert (disj Rb (map fst R')) as Hdisj.
  intros u H ; destruct H as [ HinRb Hin_fst ].
  apply HiffRb in HinRb ; destruct HinRb as [ HinR _ ] ; apply HiffR in HinR.
  apply in_map_iff in Hin_fst ; destruct Hin_fst as [ [ v N ] [ Heq HinR' ] ] ; simpl in Heq ; rewrite Heq in *.
  apply HiffR' in HinR' ; simpl in HinR' ; destruct HinR' as [ _ Hnot_inQ ].
  destruct HinR as [ HinQ _ ] ; contradiction.
  assert (r = a + b) as Heq_r_ab ;[ apply count_eql with R (Ra ++ Rb) ; auto | ].
  split ; intros u H ; [ destruct (CL (under_b_step u Q B D)) as [ H' | H' ] ; apply in_or_app | ].
  right ; apply HiffRb ; split ; auto.
  left ; apply HiffRa ; split ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; [ apply HiffRa in H | apply HiffRb in H ] ; tauto.
  apply count_disj ; solve [ auto ] || intros u H ; destruct H as [ HinRa HinRb ].
  apply HiffRa in HinRa ; apply HiffRb in HinRb ; destruct HinRa ; destruct HinRb ; contradiction.
  destruct (count_ex (coll_bds_nbh R')) as [ k Hcount_nbhR' ].
  assert (r' = c + k) as Heq_r_ck.
  apply count_eql with (coll_bds R') (map fst R' ++ coll_bds_nbh R') ; auto.
  split ; intros u H ; [ apply in_coll_bds in H | ].
  destruct H as [ v [ N [ HinR' Hin ] ] ] ; destruct Hin as [ Heq | Hin ].
  rewrite Heq in * ; clear Heq v ; apply in_or_app ; left.
  apply in_map_iff ; exists (u, N) ; simpl ; split ; auto.
  apply coll_bds_nbh_in with (v := u) in HinR' ; solve [ auto ] || apply in_or_app ; auto.
  apply in_app_or in H ; destruct H as [ H | H ] ; auto.
  apply in_map_iff in H ; destruct H as [ [ v N ] [ Heq Hin ] ] ; simpl in Heq ; rewrite Heq in *.
  apply coll_bds_in in Hin ; apply Hin ; simpl ; auto.
  apply in_coll_bds_nbh in H ; destruct H as [ v [ N [ HinR' HinN ] ] ].
  apply coll_bds_in in HinR' ; apply HinR' ; simpl ; auto.
  apply count_disj ; solve [ auto ] || intros u H ; destruct H as [ Hin_fstR' Hin_nbhR' ].
  assert (In u (map fst B)) as Hin_fstB.
  apply in_map_iff in Hin_fstR' ; destruct Hin_fstR' as [ [ v N ] [ Heq HinR' ] ].
  simpl in Heq ; rewrite Heq in * ; clear Heq v ; apply HiffR' in HinR'.
  apply in_map_iff ; exists (u, N) ; simpl ; split ; tauto.
  apply in_coll_bds_nbh in Hin_nbhR' ; destruct Hin_nbhR' as [ v [ N [ HinR' HinN ] ] ].
  apply HiffR' in HinR' ; destruct HinR' as [ HinB _ ].
  apply bds_sides_disj with (D := D) in HinB ; auto.
  apply (HinB u) ; split ; auto.
  assert (a <= k) ; lia || apply count_all_rel_src with D B Ra R' ; auto.
  intros uN H ; destruct uN as [ u N ] ; apply HiffR' in H ; tauto.
  intros w H ; apply HRa_rel_src in H ; destruct H as [ u [ N [ L [ R'' [ D' H ] ] ] ] ].
  destruct H as [ Heq_lists [ Hminus_set [ Hrel_src [ _ Hnot_inQ ] ] ] ].
  exists u ; exists N ; exists L ; exists R'' ; exists D' ; split ; [ | split ; [ | split ] ] ; auto.
  apply HiffR' ; simpl ; split ; auto.
  rewrite Heq_lists ; apply in_or_app ; right ; simpl ; auto.
Qed.
