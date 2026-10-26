Require Export Sparse.Sparsity.
From Stdlib Require Import Lra Lia.
Import ListNotations.

(* 分類器とは独立した、部分列と端点の幾何。 *)
Definition endpoint_of_seg (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s.

Definition endpoint_of (ls : list Segment) (p : Point) : Prop :=
  exists s, In s ls /\ endpoint_of_seg s p.

Definition in_sub_x_range (sub : list Segment) (p : Point) : Prop :=
  rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).

(* 初期埋め込みの準備条件。分類や蓋除去の条件は含めない。 *)
Record PreparedGeometry (l sub r : list Segment) : Prop := {
  prepared_sub_nonempty : sub <> [];
  prepared_sub_x_monotone : x_monotone_segs sub;
  prepared_sub_contained : sub_contained_in_endpoint_rect sub;
  prepared_boundary_axes :
    (embed (n, e, cx) (hd_segment sub) /\
      exists c, embed (n, e, c) (last_segment sub)) \/
    (embed (s, e, cc) (hd_segment sub) /\
      exists c, embed (s, e, c) (last_segment sub))
}.

(* 二セグメントへの置換で、内部の接続点を端点長方形の中に取る。 *)
Definition reconnect_slope_pair
  (p q : Point) (d1 d2 : Direction) (slope_p slope_q : R) : Prop :=
  exists middle slope_left slope_right,
    in_rect (rect_between p q) middle /\
    reconnect_slope p middle d1 slope_p slope_left /\
    reconnect_slope middle q d2 slope_right slope_q.

(* A1: 同じ証人について初期の疎性と、局所置換の端点傾きを準備する。 *)
Record PreparedSparseEmbedding
    (ds1 sub_ds ds2 : list Direction) (l sub r : list Segment) : Prop := {
  prepared_left_embed : embed_listDir ds1 l;
  prepared_sub_embed : embed_listDir sub_ds sub;
  prepared_right_embed : embed_listDir ds2 r;
  prepared_whole_embed : embed_listDir (ds1 ++ sub_ds ++ ds2) (l ++ sub ++ r);
  prepared_whole_sparse : sparse_embedding (l ++ sub ++ r);
  prepared_extensions_disjoint : extensions_disjoint (l ++ sub ++ r);
  prepared_geometry : PreparedGeometry l sub r;
  prepared_single_replacement : forall d d',
    sub_ds = [d; d'; d] -> d <> d' ->
    reconnect_slope (init (hd_segment sub)) (term (last_segment sub)) d
      (slope_init (hd_segment sub)) (slope_term (last_segment sub));
  prepared_pair_replacement : forall d d',
    sub_ds = [d; d; d'; d'] -> d <> d' ->
    reconnect_slope_pair (init (hd_segment sub)) (term (last_segment sub)) d d'
      (slope_init (hd_segment sub)) (slope_term (last_segment sub))
}.

Inductive CurveEnd := HeadEnd | LastEnd.

Definition extension_anchor (which : CurveEnd) (ls : list Segment) : Point :=
  match which with
  | HeadEnd => init (hd_segment ls)
  | LastEnd => term (last_segment ls)
  end.

Definition on_strict_extension (which : CurveEnd) (ls : list Segment) : Point -> Prop :=
  match which with
  | HeadEnd => onHead_extend_strict ls
  | LastEnd => onLast_extend_strict ls
  end.

Definition on_end_extension (which : CurveEnd) (ls : list Segment) : Point -> Prop :=
  match which with HeadEnd => onHead_extend ls | LastEnd => onLast_extend ls end.

Definition external_end_nonempty (which : CurveEnd) (l r : list Segment) : Prop :=
  match which with HeadEnd => l <> [] | LastEnd => r <> [] end.

Lemma connected_x_monotone_endpoints :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    fst (init (hd_segment sub)) < fst (term (last_segment sub)).
Proof.
  intros sub Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne.
  revert a. induction tail as [|b tail IH]; intros a Hconn Hmono.
  - apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (IH b HconnTail HmonoTail) as Htail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    change (fst (init a) < fst (term (last_segment (b :: tail)))).
    change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
Qed.

Lemma x_monotone_rect_x_bounds :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) = fst (init (hd_segment sub))
    /\ rx1 (rect_of sub) = fst (term (last_segment sub)).
Proof.
  intros sub Hne Hconn Hmono.
  pose proof (connected_x_monotone_endpoints sub Hne Hconn Hmono) as Hends.
  unfold rect_of; simpl.
  rewrite Rmin_left by lra.
  rewrite Rmax_right by lra.
  split; reflexivity.
Qed.

Lemma x_monotone_segment_point_bounds :
  forall s p,
    x_monotone_seg s ->
    onSegment s p ->
    fst (init s) <= fst p <= fst (term s).
Proof.
  intros s p Hmono Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - unfold x_monotone_seg, init_x, term_x in Hmono. lra.
  - unfold x_monotone_seg, init_x, term_x in Hmono. lra.
  - unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    cbn in Hinside.
    destruct Hinside as [Hx _].
    unfold x_monotone_seg, init_x, term_x in Hmono.
    rewrite Rmin_left in Hx by lra. rewrite Rmax_right in Hx by lra.
    lra.
Qed.

(* 連結な x 単調 sub 上の点は、その始点と終点が定める閉 x 範囲に入る。 *)

Lemma segment_has_point_at_x :
  forall seg x,
    rx0 (rect_of [seg]) <= x <= rx1 (rect_of [seg]) ->
    exists p, onSegment seg p /\ fst p = x.
Proof.
  intros seg x Hx.
  destruct (total_order_T (fst (init seg)) (fst (term seg)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init seg)) (fst (term seg)) <= x <=
            Rmax (fst (init seg)) (fst (term seg))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init seg)) (snd (term seg))) as [Hy | Hy].
    + destruct (exist_between_x_pos seg
                  (fst (init seg)) (fst (term seg))
                  (snd (init seg)) (snd (term seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg seg
                  (fst (init seg)) (fst (term seg))
                  (snd (init seg)) (snd (term seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x seg).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init seg)) (fst (term seg)) <= x <=
            Rmax (fst (init seg)) (fst (term seg))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term seg)) (snd (init seg))) as [Hy | Hy].
    + destruct (exist_between_x_pos seg
                  (fst (term seg)) (fst (init seg))
                  (snd (term seg)) (snd (init seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg seg
                  (fst (term seg)) (fst (init seg))
                  (snd (term seg)) (snd (init seg)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結した二つの x 区間の和は、両外端を結ぶ区間を覆う。 *)
Lemma x_interval_bridge : forall a b c x,
  Rmin a c <= x <= Rmax a c ->
  Rmin a b <= x <= Rmax a b \/
  Rmin b c <= x <= Rmax b c.
Proof.
  intros a b c x Hx.
  unfold Rmin, Rmax in *.
  repeat destruct Rle_dec; lra.
Qed.

(* x 単調でなくても、連結な列の両端間の各 x には sub 上の点がある。 *)
Lemma connected_sub_has_point_at_x :
  forall sub x,
    sub <> [] ->
    connected sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne.
  destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (Hlast :
        last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    assert (Hbetween :
        Rmin (fst (init a)) (fst (term (last_segment (b :: tail)))) <= x <=
        Rmax (fst (init a)) (fst (term (last_segment (b :: tail))))).
    { unfold rect_of in Hx. simpl in Hx. rewrite Hlast in Hx.
      exact Hx. }
    destruct (x_interval_bridge
                (fst (init a)) (fst (term a))
                (fst (term (last_segment (b :: tail)))) x Hbetween)
      as [Ha | Htail].
    + destruct (segment_has_point_at_x a x Ha) as [q [Hon Hqx]].
      exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
    + assert (HxTail :
        rx0 (rect_of (b :: tail)) <= x <=
        rx1 (rect_of (b :: tail))).
      { unfold rect_of. simpl. rewrite <- Hab. exact Htail. }
      destruct (IH b x HconnTail HxTail) as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

Lemma x_monotone_sub_has_point :
  forall sub x,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hmono Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros seg Hseg. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    change (rx0 (rect_of (a :: b :: tail)) = fst (init a)) in Hleft.
    assert (Hlast :
      last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hleft, Hright in Hx.
    destruct (Rle_dec x (fst (term a))) as [Hxa | Hax].
    + assert (Hsingle :
          rx0 (rect_of [a]) <= x <= rx1 (rect_of [a])).
      { pose proof (Hmono a ltac:(now left)) as Ha.
        unfold x_monotone_seg, init_x, term_x in Ha.
        change (Rmin (fst (init a)) (fst (term a)) <= x <=
                Rmax (fst (init a)) (fst (term a))).
        rewrite Rmin_left by lra. rewrite Rmax_right by lra. lra. }
      destruct (segment_has_point_at_x a x Hsingle) as [q [Hon Hqx]].
      exists q. split.
      * exists a. split; [now left | exact Hon].
      * exact Hqx.
    + assert (Htailx :
          rx0 (rect_of (b :: tail)) <= x <=
          rx1 (rect_of (b :: tail))).
      { pose proof (x_monotone_rect_x_bounds
                      (b :: tail) ltac:(discriminate)
                      HconnTail HmonoTail) as [HtailLeft HtailRight].
        change (rx0 (rect_of (b :: tail)) = fst (init b)) in HtailLeft.
        rewrite HtailLeft, HtailRight.
        rewrite Hlast in Hx. rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[seg [Hseg Hon]] Hqx]].
      exists q. split.
      * exists seg. split; [now right | exact Hon].
      * exact Hqx.
Qed.

Lemma prepared_geometry_transport : forall l sub r l' r',
  PreparedGeometry l sub r -> PreparedGeometry l' sub r'.
Proof.
  intros l sub r l' r' H. destruct H. constructor; assumption.
Qed.

Lemma x_monotone_sub_point_in_x_range :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    in_sub_x_range sub p.
Proof.
  intros sub p Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a p.
  induction tail as [|b tail IH]; intros a p Hconn Hmono
      [seg [Hseg Hon]].
  - simpl in Hseg. destruct Hseg as [Hseg | Hseg]; [subst seg | contradiction].
    pose proof (Hmono a ltac:(now left)) as Ha.
    pose proof (x_monotone_rect_x_bounds
                  [a] ltac:(discriminate) Hconn Hmono) as [Hleft Hright].
    pose proof (x_monotone_segment_point_bounds a p Ha Hon) as Hx.
    unfold in_sub_x_range. rewrite Hleft, Hright.
    exact Hx.
  - simpl in Hseg. destruct Hseg as [Hseg | Hseg].
    + subst seg.
      pose proof (Hmono a ltac:(now left)) as Ha.
      pose proof (x_monotone_segment_point_bounds a p Ha Hon) as Hx.
      assert (Hab : term a = init b).
      { apply (Hconn 0%nat a b); reflexivity. }
      assert (HconnTail : connected (b :: tail)).
      { intros i s1 s2 H1 H2.
        apply (Hconn (S i) s1 s2); simpl; assumption. }
      assert (HmonoTail : x_monotone_segs (b :: tail)).
      { intros t Ht. apply Hmono. now right. }
      pose proof (x_monotone_rect_x_bounds
                    (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
        as [Hleft Hright].
      pose proof (connected_x_monotone_endpoints
                    (b :: tail) ltac:(discriminate)
                    HconnTail HmonoTail) as Htail.
      assert (Hlast :
          last_segment (a :: b :: tail) = last_segment (b :: tail)).
      { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
        apply last_app_nonnil. discriminate. }
      unfold in_sub_x_range. rewrite Hleft, Hright.
      rewrite Hlast.
      change (fst (init a) <= fst p <=
              fst (term (last_segment (b :: tail)))).
      change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
      rewrite <- Hab in Htail. lra.
    + assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    unfold in_sub_x_range. rewrite Hleft, Hright.
    pose proof (IH b p HconnTail HmonoTail
                  (ex_intro _ seg (conj Hseg Hon))) as HpTail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    pose proof (x_monotone_rect_x_bounds
                  (b :: tail) ltac:(discriminate)
                  HconnTail HmonoTail) as [HtailLeft HtailRight].
    unfold in_sub_x_range in HpTail.
    rewrite HtailLeft, HtailRight in HpTail.
    change (fst (init b) <= fst p <=
            fst (term (last_segment (b :: tail)))) in HpTail.
    assert (Hlast :
        last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hlast.
    change (fst (init a) <= fst p <=
            fst (term (last_segment (b :: tail)))).
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
Qed.


Lemma inner_sub_x_bounds : forall sub i seg,
  sub <> [] -> connected sub -> x_monotone_segs sub ->
  nth_error sub i = Some seg ->
  (i<>0%nat -> fst (init (hd_segment sub)) < init_x seg) /\
  ((S i < length sub)%nat -> term_x seg < fst (term (last_segment sub))).
Proof.
  intros sub i seg Hne Hconn Hmono Hi.
  assert (Hlt : (i<length sub)%nat) by (eapply nth_error_lt; eassumption).
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono) as [Hleft Hright].
  split.
  - intros Hin.
    destruct (nth_error sub (i-1)) as [prev|] eqn:Hp.
    2: { apply nth_error_None in Hp. lia. }
    pose proof (Hmono prev (nth_error_In _ _ Hp)) as Hprev.
    assert (Hnext : nth_error sub (S (i-1))=Some seg) by (replace (S (i-1)) with i by lia; exact Hi).
    pose proof (Hconn (i-1)%nat prev seg Hp Hnext) as Hjoin.
    pose proof (x_monotone_sub_point_in_x_range sub (init prev) Hne Hconn Hmono
      ltac:(exists prev; split; [now apply nth_error_In in Hp | apply onInit])) as Hx.
    unfold in_sub_x_range in Hx. rewrite Hleft in Hx.
    unfold x_monotone_seg,init_x,term_x in Hprev |- *. rewrite Hjoin in Hprev. lra.
  - intros Hin.
    destruct (nth_error sub (S i)) as [next|] eqn:Hn.
    2: { apply nth_error_None in Hn. lia. }
    pose proof (Hmono next (nth_error_In _ _ Hn)) as Hnext.
    pose proof (Hconn i seg next Hi Hn) as Hjoin.
    pose proof (x_monotone_sub_point_in_x_range sub (term next) Hne Hconn Hmono
      ltac:(exists next; split; [now apply nth_error_In in Hn | apply onTerm])) as Hx.
    unfold in_sub_x_range in Hx. rewrite Hright in Hx.
    unfold x_monotone_seg,init_x,term_x in Hnext |- *. rewrite Hjoin. lra.
Qed.

Lemma dc_predecessor_north_cx : forall p,
  dc p (n,e,cx) -> exists h, p=(n,h,cc).
Proof.
  intros [[v h] c] H. destruct v,h,c; inversion H; subst; simpl in *; eauto.
Qed.

Lemma dc_predecessor_south_cc : forall p,
  dc p (s,e,cc) -> exists h, p=(s,h,cx).
Proof.
  intros [[v h] c] H. destruct v,h,c; inversion H; subst; simpl in *; eauto.
Qed.

Lemma dc_successor_north_east : forall c p,
  dc (n,e,c) p ->
  (exists h, p=(n,h,cx)) \/ p=(n,e,cc) \/ p=(s,e,cx).
Proof.
  intros c [[v h] co] H. destruct c,v,h,co; inversion H; subst; simpl in *; eauto.
Qed.

Lemma dc_successor_south_east : forall c p,
  dc (s,e,c) p ->
  (exists h, p=(s,h,cc)) \/ p=(s,e,cx) \/ p=(n,e,cc).
Proof.
  intros c [[v h] co] H. destruct c,v,h,co; inversion H; subst; simpl in *; eauto.
Qed.
