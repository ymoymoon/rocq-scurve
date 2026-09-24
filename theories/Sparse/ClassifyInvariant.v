Require Export Sparse.ClassifySpec.
Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Stdlib.Reals.Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.

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

(* x 単調な連結列では、全体長方形の左右端は列の始終点である。 *)
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

(* セグメントの端点 x 区間内の各 x 座標は、セグメント上で実現される。 *)
Lemma segment_has_point_at_x :
  forall s x,
    rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]) ->
    exists p, onSegment s p /\ fst p = x.
Proof.
  intros s x Hx.
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init s)) (snd (term s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term s)) (snd (init s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結な x 単調 sub は、始終点間の各 x 座標を通る。 *)
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
    { intros s Hs. apply Hmono. now right. }
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
        rewrite Rmin_left by lra. rewrite Rmax_right by lra.
        lra. }
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
        rewrite Hlast in Hx.
        rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

(* x が始点から終点へ増えるセグメント上では、各点の x もその間にある。 *)
Lemma x_monotone_segment_point_bounds :
  forall s p,
    x_monotone_seg s ->
    onSegment s p ->
    init_x s <= fst p <= term_x s.
Proof.
  intros seg p Hmono [t [[Ht0 Ht1] Hpoint]]. subst p.
  unfold x_monotone_seg, init_x, term_x in Hmono.
  destruct (x_strictly_monotone_seg seg) as [Hinc | Hdec].
  - split.
    + destruct (Req_dec t 0) as [-> | Ht]; [right; reflexivity |].
      left. apply Hinc. lra.
    + destruct (Req_dec t 1) as [-> | Ht]; [right; reflexivity |].
      left. apply Hinc. lra.
  - exfalso.
    pose proof (Hdec 0 1 ltac:(lra)) as Hbackwards.
    change (fst (point seg 0) < fst (point seg 1)) in Hmono.
    change (fst (point seg 1) < fst (point seg 0)) in Hbackwards.
    lra.
Qed.

(* 一つの x 単調セグメントは同じ x 座標を二度取らない。 *)
Lemma x_monotone_segment_same_x_unique :
  forall s p q,
    x_monotone_seg s ->
    onSegment s p ->
    onSegment s q ->
    fst p = fst q ->
    p = q.
Proof.
  intros seg p q Hmono
    [tp [[Htp0 Htp1] Hpointp]]
    [tq [[Htq0 Htq1] Hpointq]] Hx.
  subst p q.
  destruct (x_strictly_monotone_seg seg) as [Hinc | Hdec];
  destruct (total_order_T tp tq) as [[Hlt | Heq] | Hgt].
  - pose proof (Hinc tp tq ltac:(lra)) as Hstrict. lra.
  - now subst tq.
  - pose proof (Hinc tq tp ltac:(lra)) as Hstrict. lra.
  - pose proof (Hdec tp tq ltac:(lra)) as Hstrict. lra.
  - now subst tq.
  - pose proof (Hdec tq tp ltac:(lra)) as Hstrict. lra.
Qed.

(* 連結な x 単調列上の全点は、列全体の始終点 x の間にある。 *)
Lemma connected_x_monotone_point_bounds :
  forall ls p,
    ls <> [] ->
    connected ls ->
    x_monotone_segs ls ->
    onSegmentlist ls p ->
    init_x (hd_segment ls) <= fst p <= term_x (last_segment ls).
Proof.
  induction ls as [|a tail IH]; intros p Hne Hconn Hmono
    [seg [Hin Hon]]; [contradiction |].
  destruct tail as [|b rest].
  - simpl in Hin. destruct Hin as [<- | Hin]; [|contradiction].
    simpl. apply x_monotone_segment_point_bounds; [|exact Hon].
    apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: rest)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: rest)).
    { intros s Hs. apply Hmono. now right. }
    assert (Hlast :
      last_segment (a :: b :: rest) = last_segment (b :: rest)).
    { change (last_segment ([a] ++ b :: rest) = last_segment (b :: rest)).
      apply last_app_nonnil. discriminate. }
    destruct Hin as [Hseg | Hseg].
    + subst seg.
      pose proof (x_monotone_segment_point_bounds a p
                    (Hmono a ltac:(now left)) Hon) as [Hleft Hpa].
      pose proof (connected_x_monotone_endpoints
                    (b :: rest) ltac:(discriminate)
                    HconnTail HmonoTail) as Htail.
      simpl. rewrite Hlast. split; [exact Hleft |].
      change (fst p <= fst (term a)) in Hpa.
      change (fst (init b) < fst (term (last_segment (b :: rest))))
        in Htail.
      change (fst p <= fst (term (last_segment (b :: rest)))).
      rewrite Hab in Hpa. lra.
    + pose proof (IH p ltac:(discriminate) HconnTail HmonoTail
                    (ex_intro _ seg (conj Hseg Hon))) as [Hbp Hright].
      pose proof (Hmono a ltac:(now left)) as Ha.
      simpl. rewrite Hlast. split; [|exact Hright].
      change (fst (init a) < fst (term a)) in Ha.
      change (fst (init b) <= fst p) in Hbp.
      change (fst (init a) <= fst p).
      rewrite Hab in Ha. lra.
Qed.

Lemma x_monotone_sub_point_rect_bounds :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).
Proof.
  intros sub p Hne Hconn Hmono Hp.
  pose proof (connected_x_monotone_point_bounds
                sub p Hne Hconn Hmono Hp) as Hbounds.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono)
    as [Hleft Hright].
  rewrite Hleft, Hright. exact Hbounds.
Qed.

(* 補正開始点が sub より外側なら、その側の補正は sub 上で発火しない。 *)
Lemma outside_patch_start_does_not_force_on_sub :
  forall sub p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    ((patch_side patch = CutLeft
      /\ patch_start_x patch <= rx0 (rect_of sub))
     \/ (patch_side patch = CutRight
         /\ rx1 (rect_of sub) <= patch_start_x patch)) ->
    patch_does_not_force_at patch p.
Proof.
  intros sub p [side start trace force inclusive]
    Hne Hconn Hmono Hp Houtside.
  left. unfold patch_active_at; simpl.
  pose proof (x_monotone_sub_point_rect_bounds
                sub p Hne Hconn Hmono Hp) as [Hleft Hright].
  destruct side; simpl in Houtside |- *.
  - destruct Houtside as [[_ Hstart] | [Hbad _]]; [|discriminate].
    intro Hactive. apply (Rlt_irrefl (fst p)).
    eapply Rlt_le_trans; [exact Hactive |].
    eapply Rle_trans; [exact Hstart | exact Hleft].
  - destruct Houtside as [[Hbad _] | [_ Hstart]]; [discriminate |].
    intro Hactive. apply (Rlt_irrefl start).
    eapply Rlt_le_trans; [exact Hactive |].
    eapply Rle_trans; [exact Hright | exact Hstart].
Qed.

Lemma singleton_head_left_patch_does_not_force_on_sub :
  forall s sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    connected ([s] ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch [s] r HeadEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros s sub r p patch Hne Hconn Hmono Hwhole Hp Hpatch.
  destruct (make_end_patch_side_and_start
              [s] r HeadEnd CutLeft patch Hpatch)
    as [seg [Hseg [Hside Hstart]]].
  simpl in Hseg. injection Hseg as <-. simpl in Hstart.
  pose proof (connected_app_junction [s] (sub ++ r)
                Hwhole ltac:(discriminate)
                ltac:(destruct sub; [contradiction | discriminate])) as Hjoin.
  simpl in Hjoin.
  destruct sub as [|a tail]; [contradiction |].
  change (term s = init a) in Hjoin.
  pose proof (x_monotone_rect_x_bounds
                (a :: tail) ltac:(discriminate) Hconn Hmono) as [Hleft _].
  apply (outside_patch_start_does_not_force_on_sub
           (a :: tail) p patch); try assumption.
  left. split; [exact Hside |].
  rewrite Hstart, Hjoin, Hleft. reflexivity.
Qed.

Lemma singleton_last_right_patch_does_not_force_on_sub :
  forall l sub s p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    connected (l ++ sub ++ [s]) ->
    onSegmentlist sub p ->
    make_end_patch l [s] LastEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros l sub s p patch Hne Hconn Hmono Hwhole Hp Hpatch.
  destruct (make_end_patch_side_and_start
              l [s] LastEnd CutRight patch Hpatch)
    as [seg [Hseg [Hside Hstart]]].
  simpl in Hseg. injection Hseg as <-. simpl in Hstart.
  change (patch_start_x patch = fst (init s)) in Hstart.
  assert (Hwhole' : connected ((l ++ sub) ++ [s])).
  { replace ((l ++ sub) ++ [s]) with (l ++ (sub ++ [s])) by
      apply app_assoc.
    exact Hwhole. }
  pose proof (connected_app_junction (l ++ sub) [s]
                Hwhole'
                ltac:(intro Hnil; apply app_eq_nil in Hnil as [_ Hsub]; contradiction)
                ltac:(discriminate)) as Hjoin.
  simpl in Hjoin.
  rewrite last_app_nonnil in Hjoin by exact Hne.
  change (term (last_segment sub) = init s) in Hjoin.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono) as [_ Hright].
  apply (outside_patch_start_does_not_force_on_sub sub p patch);
    try assumption.
  right. split; [exact Hside |].
  rewrite Hstart, <- Hjoin, Hright. reflexivity.
Qed.

(* 左側の先頭補正で先頭が二本以上ある場合は、疎性と先頭延長線の
   交差順序を結ぶ幾何が必要になる。 *)
Lemma multi_head_left_patch_does_not_force_on_sub :
  forall a b tail sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding ((a :: b :: tail) ++ sub ++ r) ->
    connected ((a :: b :: tail) ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch (a :: b :: tail) r HeadEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 先頭の右側補正では、延長線と更新済み右境界の相対位置が本質的。 *)
Lemma nonempty_head_right_patch_does_not_force_on_sub :
  forall a tail sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding ((a :: tail) ++ sub ++ r) ->
    connected ((a :: tail) ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch (a :: tail) r HeadEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 末尾の左側補正は上の双対で、更新済み左境界との比較を要する。 *)
Lemma nonempty_last_left_patch_does_not_force_on_sub :
  forall l sub a tail p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ (a :: tail)) ->
    connected (l ++ sub ++ (a :: tail)) ->
    onSegmentlist sub p ->
    make_end_patch l (a :: tail) LastEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 右側の末尾補正で末尾が二本以上ある場合の双対的な幾何。 *)
Lemma multi_last_right_patch_does_not_force_on_sub :
  forall l sub a b tail p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ (a :: b :: tail)) ->
    connected (l ++ sub ++ (a :: b :: tail)) ->
    onSegmentlist sub p ->
    make_end_patch l (a :: b :: tail) LastEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* end、左右、空/singleton/一般列を分けると、未証明なのは上の四つの
   延長線・更新境界の幾何だけになる。 *)
Lemma end_patch_does_not_force_on_sub :
  forall l sub r p k side patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch l r k side = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros l sub r p k side patch Hne Hconn Hmono Hsparse Hwhole Hp Hpatch.
  destruct k, side.
  - destruct l as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + destruct tail as [|b tail].
      * eapply singleton_head_left_patch_does_not_force_on_sub; eauto.
      * eapply multi_head_left_patch_does_not_force_on_sub; eauto.
  - destruct l as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + eapply nonempty_head_right_patch_does_not_force_on_sub; eauto.
  - destruct r as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + eapply nonempty_last_left_patch_does_not_force_on_sub; eauto.
  - destruct r as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + destruct tail as [|b tail].
      * eapply singleton_last_right_patch_does_not_force_on_sub; eauto.
      * eapply multi_last_right_patch_does_not_force_on_sub; eauto.
Qed.

Lemma end_patches_do_not_force_on_sub :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onSegmentlist sub p ->
      end_patches_do_not_force_at l r p.
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole p Hp
    k side patch Hpatch.
  eapply end_patch_does_not_force_on_sub; eauto.
Qed.

(* 連結な x 単調列は各 x 座標に高々一つの点を持つ。 *)
Lemma x_monotone_sub_point_unique :
  forall sub p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    onSegmentlist sub q ->
    fst p = fst q ->
    p = q.
Proof.
  induction sub as [|a tail IH]; intros p q Hne Hconn Hmono
    [sp [Hsp Hp]] [sq [Hsq Hq]] Hx; [contradiction |].
  destruct tail as [|b rest].
  - simpl in Hsp, Hsq.
    destruct Hsp as [<- | Hsp], Hsq as [<- | Hsq];
      try contradiction.
    eapply x_monotone_segment_same_x_unique; eauto.
    apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: rest)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: rest)).
    { intros s Hs. apply Hmono. now right. }
    destruct Hsp as [Hsp | Hsp], Hsq as [Hsq | Hsq].
    + subst sp sq. eapply x_monotone_segment_same_x_unique; eauto.
      apply Hmono. now left.
    + subst sp.
      pose proof (x_monotone_segment_point_bounds a p
                    (Hmono a ltac:(now left)) Hp) as [_ Hpa].
      pose proof (connected_x_monotone_point_bounds
                    (b :: rest) q ltac:(discriminate)
                    HconnTail HmonoTail
                    (ex_intro _ sq (conj Hsq Hq))) as [Hbq _].
      change (fst p <= fst (term a)) in Hpa.
      change (fst (init b) <= fst q) in Hbq.
      assert (Hpx : fst p = fst (term a)) by
        (rewrite <- Hab in Hbq; lra).
      assert (Hqx : fst q = fst (init b)) by
        (rewrite <- Hab; lra).
      assert (Hpterm : p = term a).
      { exact (x_monotone_segment_same_x_unique a p (term a)
                 (Hmono a ltac:(now left)) Hp (onTerm a) Hpx). }
      assert (Hqinit : q = init b).
      { eapply (IH q (init b) ltac:(discriminate)
                  HconnTail HmonoTail).
        - exists sq. now split.
        - exists b. split; [now left | apply onInit].
        - exact Hqx. }
      now rewrite Hpterm, Hqinit, Hab.
    + subst sq.
      pose proof (connected_x_monotone_point_bounds
                    (b :: rest) p ltac:(discriminate)
                    HconnTail HmonoTail
                    (ex_intro _ sp (conj Hsp Hp))) as [Hbp _].
      pose proof (x_monotone_segment_point_bounds a q
                    (Hmono a ltac:(now left)) Hq) as [_ Hqa].
      change (fst (init b) <= fst p) in Hbp.
      change (fst q <= fst (term a)) in Hqa.
      assert (Hqx : fst q = fst (term a)) by
        (rewrite <- Hab in Hbp; lra).
      assert (Hpx : fst p = fst (init b)) by
        (rewrite <- Hab; lra).
      assert (Hqterm : q = term a).
      { exact (x_monotone_segment_same_x_unique a q (term a)
                 (Hmono a ltac:(now left)) Hq (onTerm a) Hqx). }
      assert (Hpinit : p = init b).
      { eapply (IH p (init b) ltac:(discriminate)
                  HconnTail HmonoTail).
        - exists sp. now split.
        - exists b. split; [now left | apply onInit].
        - exact Hpx. }
      now rewrite Hpinit, Hqterm, Hab.
    + eapply (IH p q ltac:(discriminate) HconnTail HmonoTail).
      * exists sp. now split.
      * exists sq. now split.
      * exact Hx.
Qed.

Lemma choose_sub_y_eq :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    choose_sub_y sub (fst p) = snd p.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  destruct p as [x y]. simpl in *.
  assert (Hex : exists y0, onSegmentlist sub (x, y0)).
  { exists y. exact Hp. }
  pose proof (choose_sub_y_spec sub x Hex) as Hchosen.
  pose proof (x_monotone_sub_point_unique sub
                (x, choose_sub_y sub x) (x, y)
                Hne Hconn Hmono Hchosen Hp eq_refl) as Heq.
  now injection Heq.
Qed.

Lemma simple_height_on_sub :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    simple_height sub (fst p) = snd p.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  pose proof (connected_x_monotone_point_bounds
                sub p Hne Hconn Hmono Hp) as Hbounds.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono)
    as [Hleft Hright].
  unfold simple_height.
  destruct (Rlt_dec (fst p) (rx0 (rect_of sub))) as [Hlt | Hnlt].
  - rewrite Hleft in Hlt. unfold init_x in Hbounds. lra.
  - destruct (Rlt_dec (rx1 (rect_of sub)) (fst p)) as [Hlt | Hnlt'].
    + rewrite Hright in Hlt. unfold term_x in Hbounds. lra.
    + now apply choose_sub_y_eq.
Qed.

Lemma simple_classify_sub_fixed :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    state_region (simple_classify_state sub) p = RegFix.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  unfold simple_classify_state, classify_at_height; simpl.
  rewrite (simple_height_on_sub sub p Hne Hconn Hmono Hp).
  destruct (Rlt_dec (snd p) (snd p)); [lra |].
  destruct (Rlt_dec (snd p) (snd p)); [lra | reflexivity].
Qed.

(* sub 上で各 end 補正が発火しなければ、最終分類でも sub は固定される。 *)
Lemma classify_sub_fixed_from_end_patch_safety :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    end_patches_do_not_force_at l r p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hp Hsafe.
  rewrite (classify_eq_simple_when_end_patches_do_not_force
             l sub r p Hsafe).
  now apply simple_classify_sub_fixed.
Qed.

Lemma classify_without_sides_sub_fixed :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    classify [] sub [] p = RegFix.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  rewrite classify_without_sides_eq_simple.
  now apply simple_classify_sub_fixed.
Qed.

Lemma classify_at_height_same_x_monotone :
  forall height p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify_at_height height q)
      (classify_at_height height p).
Proof.
  intros height [xp yp] [xq yq] Hx Hy. simpl in Hx, Hy. subst xq.
  unfold classify_at_height. simpl.
  destruct (Rlt_dec yp (height xp)) as [Hpdown | Hpdown].
  - destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown].
    + now left.
    + destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Down.
      * right. apply RegFix_above_Down.
  - destruct (Rlt_dec (height xp) yp) as [Hpup | Hpup].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup]; [now left | lra].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Fix.
      * lra.
Qed.

Lemma simple_classify_same_x_monotone :
  forall sub p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (state_region (simple_classify_state sub) q)
      (state_region (simple_classify_state sub) p).
Proof.
  intros sub p q Hx Hy.
  exact (classify_at_height_same_x_monotone
           (simple_height sub) p q Hx Hy).
Qed.

Definition vertically_monotone_region (f : Point -> Region) : Prop :=
  forall p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above (f q) (f p).

Lemma apply_region_patch_preserves_vertical_monotonicity :
  forall old patch,
    vertically_monotone_region old ->
    vertically_monotone_region (apply_region_patch old patch).
Proof.
  intros old [side start trace force inclusive] Hold
    [xp yp] [xq yq] Hx Hy.
  simpl in Hx, Hy. subst xq.
  unfold apply_region_patch. simpl.
  destruct (patch_active_dec
              {| patch_side := side;
                 patch_start_x := start;
                 patch_reference := trace;
                 patch_force := force;
                 patch_inclusive := inclusive |} xp) as [Hactive | Hinactive].
  2: apply Hold; simpl; lra.
  destruct (trace_height trace xp) as [reference_y |] eqn:Hheight.
  2: apply Hold; simpl; lra.
  destruct force, inclusive;
    cbn [patch_forces_dec patch_forces_at forced_region].
  - destruct (Rle_dec reference_y yp) as [Hp | Hp];
    destruct (Rle_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec reference_y yp) as [Hp | Hp];
    destruct (Rlt_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rle_dec yp reference_y) as [Hp | Hp];
    destruct (Rle_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec yp reference_y) as [Hp | Hp];
    destruct (Rlt_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
Qed.

Lemma apply_patch_preserves_vertical_monotonicity :
  forall st patch,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region (state_region (apply_patch st patch)).
Proof.
  intros [region height] patch Hmono. simpl in *.
  now apply apply_region_patch_preserves_vertical_monotonicity.
Qed.

Lemma simple_state_vertically_monotone :
  forall sub,
    vertically_monotone_region (state_region (simple_classify_state sub)).
Proof.
  intros sub p q Hx Hy.
  now apply simple_classify_same_x_monotone.
Qed.

Lemma apply_end_at_preserves_vertical_monotonicity :
  forall st l r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (apply_end_at st l r k side)).
Proof.
  intros st l r k side Hmono. unfold apply_end_at.
  destruct (make_end_patch l r k side) as [patch |];
    [now apply apply_patch_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_end_preserves_vertical_monotonicity :
  forall st l sub r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_end st l sub r k side)).
Proof.
  intros st l sub r k side Hmono. unfold process_end.
  destruct (nearest_end_crossing st l sub r k side);
    [now apply apply_end_at_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_both_ends_preserves_vertical_monotonicity :
  forall st l sub r side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_both_ends_on_side st l sub r side)).
Proof.
  intros st l sub r side Hmono.
  unfold process_both_ends_on_side.
  destruct (nearest_end_crossing st l sub r HeadEnd side) as [ph |];
  destruct (nearest_end_crossing st l sub r LastEnd side) as [pl |].
  - destruct (crossing_closer_dec side ph pl).
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - exact Hmono.
Qed.

Lemma build_classify_state_vertically_monotone :
  forall l sub r,
    vertically_monotone_region
      (state_region (build_classify_state l sub r)).
Proof.
  intros l sub r. unfold build_classify_state.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply simple_state_vertically_monotone.
Qed.

Lemma classify_same_x_monotone :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify l sub r q) (classify l sub r p).
Proof.
  intros l sub r p q Hx Hy.
  exact (build_classify_state_vertically_monotone l sub r p q Hx Hy).
Qed.

(* 補正後の Fix は元の単純分類でも Fix なので、同じ x の Fix 点より
   真に上（下）の非 Fix 点は最終分類でも Up（Down）になる。 *)
Lemma classify_above_fixed_is_up :
  forall l sub r p q,
    fst p = fst q ->
    snd q < snd p ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegUp.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_same_x_monotone l sub r q p
                ltac:(now symmetry) Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - reflexivity.
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
Qed.

Lemma classify_below_fixed_is_down :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegDown.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_same_x_monotone l sub r p q Hx Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
  - reflexivity.
Qed.

(* sub 固定性は、四つの end/side 場合に分けた補正非発火補題から従う。 *)
Lemma classified_sub_fixed_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix.
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole p Hp.
  eapply classify_sub_fixed_from_end_patch_safety; eauto.
  now apply (end_patches_do_not_force_on_sub
               l sub r Hne Hconn Hmono Hsparse Hwhole p Hp).
Qed.

(* sub と同じ x の点そのものの分類は、sub の固定性と鉛直単調性だけで
   決まる。セグメント両端への伝播は別の幾何補題で扱う。 *)
Lemma classify_above_sub_at_x :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    above_sub_at_x sub p ->
    classify l sub r p = RegUp.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole
    [q [Hq [Hx Hy]]].
  eapply classify_above_fixed_is_up with (q := q); eauto.
  - now apply (classified_sub_fixed_from_construction
                 l sub r Hne Hconn Hmono Hsparse Hwhole).
  - assert (Hheight : simple_height sub (fst p) = snd q).
    { rewrite Hx. now apply simple_height_on_sub. }
    unfold simple_classify_state, classify_at_height; simpl.
    rewrite Hheight.
    destruct (Rlt_dec (snd p) (snd q)); [lra |].
    destruct (Rlt_dec (snd q) (snd p)); [discriminate | lra].
Qed.

Lemma classify_below_sub_at_x :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    below_sub_at_x sub p ->
    classify l sub r p = RegDown.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole
    [q [Hq [Hx Hy]]].
  eapply classify_below_fixed_is_down with (q := q); eauto.
  - now apply (classified_sub_fixed_from_construction
                 l sub r Hne Hconn Hmono Hsparse Hwhole).
  - assert (Hheight : simple_height sub (fst p) = snd q).
    { rewrite Hx. now apply simple_height_on_sub. }
    unfold simple_classify_state, classify_at_height; simpl.
    rewrite Hheight.
    destruct (Rlt_dec (snd p) (snd q)); [discriminate |].
    destruct (Rlt_dec (snd q) (snd p)); [lra | lra].
Qed.

(* 各セグメントと現在の境界の交差順序。primitive の8場合に帰着するが、
   更新済み境界を横切る場合の中間値議論を残す。 *)
Lemma classified_segment_endpoints_monotone_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg,
      In seg (l ++ sub ++ r) ->
      (snd (init seg) < snd (term seg) ->
        region_at_or_above
          (classify l sub r (term seg)) (classify l sub r (init seg)))
      /\
      (snd (term seg) < snd (init seg) ->
        region_at_or_above
          (classify l sub r (init seg)) (classify l sub r (term seg))).
Admitted.

(* 非隣接長方形の上下分離を分類順序へ移す部分。 *)
Lemma classified_nonadjacent_endpoint_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      region_at_or_above (classify l sub r pt) (classify l sub r ps).
Admitted.

(* sub の同じ x に点を持つ非隣接セグメントについて、疎性から長方形の
   上下どちら側に全端点があるかを確定する部分。 *)
Lemma classified_segment_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init seg) = RegUp
         /\ classify l sub r (term seg) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init seg) = RegDown
         /\ classify l sub r (term seg) = RegDown).
Admitted.

(* strict 延長線が sub の x 範囲へ入る場合の先頭基点分類。 *)
Lemma classified_head_extension_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_extension_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 同じ x にある先頭・末尾延長線の上下順序。 *)
Lemma classified_head_last_extension_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))).
Admitted.

(* 先頭延長線と一セグメントの交差順序。 *)
Lemma classified_head_segment_crossing_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_segment_crossing_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 先頭補正表の8 primitive 場合から、異領域となる場合を傾き保存可能な
   四形に限定する部分。 *)
Lemma classified_head_slope_case_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l))).
Admitted.

(* 末尾補正表の双対。 *)
Lemma classified_last_slope_case_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r))).
Admitted.

(* 蓋でない左境界の完全下側にある非隣接端点は上へ動かさない。
   現行の境界パッチ構成に固有の幾何学的検証は、再接続側と分離しておく。 *)
Lemma classified_below_terminal_not_up_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    l <> [] ->
    ~ terminal_lid l ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (last_segment l) ->
      ry1 (rect_of [t]) < ry0 (rect_of [last_segment l]) ->
      endpoint_of_seg t p ->
      classify l sub r p <> RegUp.
Admitted.

(* 右境界についての双対。 *)
Lemma classified_below_initial_not_up_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    r <> [] ->
    ~ initial_lid r ->
    forall t p,
      In t (nonadjacent_sides l r) ->
      segment_x_ranges_overlap t (hd_segment r) ->
      ry1 (rect_of [t]) < ry0 (rect_of [hd_segment r]) ->
      endpoint_of_seg t p ->
      classify l sub r p <> RegUp.
Admitted.
