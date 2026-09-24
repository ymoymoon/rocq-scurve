Require Export Sparse.SegmentListGeometry.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import SegmentsTranslation.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
(* ================================================================= *)
(* 長方形と sparse *)
(* ================================================================= *)

Lemma Rmin_opp : forall a b, Rmin (- a) (- b) = - Rmax a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

Lemma Rmax_opp : forall a b, Rmax (- a) (- b) = - Rmin a b.
Proof. intros. unfold Rmin, Rmax. destruct (Rle_dec (-a) (-b)), (Rle_dec a b); lra. Qed.

(* 部分列の始点と終点を対角線にもつ長方形。
   1セグメントの長方形には rect_of [s] を用いる。 *)
Definition rect_of (sub : list Segment) : Rect :=
  let q0 := init (hd_segment sub) in
  let q3 := term (last_segment sub) in
  mkRect (Rmin (fst q0) (fst q3)) (Rmin (snd q0) (snd q3))
         (Rmax (fst q0) (fst q3)) (Rmax (snd q0) (snd q3)).

Definition rect_height (Rc : Rect) : R := ry1 Rc - ry0 Rc.

(* 境界を含む閉長方形。疎性では、境界上だけの接触も排除する。 *)
Definition in_closed_rect (Rc : Rect) (p : Point) : Prop :=
  rx0 Rc <= fst p <= rx1 Rc /\ ry0 Rc <= snd p <= ry1 Rc.

(* 旧名は互換性のため残すが、意味は閉長方形への所属そのもの。 *)
Definition in_rect_or_endpoints_at (old : list Segment) (p : Point) : Prop :=
  in_closed_rect (rect_of old) p.

Definition in_segment_rect_or_endpoints (s : Segment) (p : Point) : Prop :=
  in_closed_rect (rect_of [s]) p.

(* new の全ての点が old の閉長方形内にある。 *)
Definition in_rect_or_endpoints (old new : list Segment) : Prop :=
  forall p, onSegmentlist new p ->
    in_rect_or_endpoints_at old p.

(* [Segment.v] の基本契約を、閉長方形の表現へ読み替える。 *)
Lemma segment_in_rect_or_endpoints :
  forall s p, onSegment s p -> in_segment_rect_or_endpoints s p.
Proof.
  intros s p Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; split; [apply Rmin_l | apply Rmax_l | apply Rmin_l | apply Rmax_l].
  - unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    split; split; [apply Rmin_r | apply Rmax_r | apply Rmin_r | apply Rmax_r].
  - unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    unfold in_segment_rect_or_endpoints, in_closed_rect, rect_of; simpl.
    change
      (Rmin (fst (init s)) (fst (term s)) < fst p <
         Rmax (fst (init s)) (fst (term s)) /\
       Rmin (snd (init s)) (snd (term s)) < snd p <
         Rmax (snd (init s)) (snd (term s))) in Hinside.
    destruct Hinside as [[Hx0 Hx1] [Hy0 Hy1]].
    split; split; apply Rlt_le; assumption.
Qed.

(* 全体の始点・終点そのものを除いた両端延長線。 *)
Definition onHead_extend_strict (ls : list Segment) (p : Point) : Prop :=
  exists t, t < 0 /\ point (hd_segment ls) t = p.

Definition onLast_extend_strict (ls : list Segment) (p : Point) : Prop :=
  exists t, 1 < t /\ point (last_segment ls) t = p.

(* sub と隣接する最後の l と先頭の r を除いた外側セグメント。 *)
Definition nonadjacent_sides (l r : list Segment) : list Segment :=
  removelast l ++ tl r.

Lemma nonadjacent_sides_map : forall (f : Segment -> Segment) l r,
  nonadjacent_sides (map f l) (map f r) = map f (nonadjacent_sides l r).
Proof.
  intros f l r. unfold nonadjacent_sides. rewrite map_app.
  assert (Hremove : removelast (map f l) = map f (removelast l)).
  { induction l using rev_ind; [reflexivity|].
    rewrite map_app. simpl. rewrite !removelast_last. reflexivity. }
  rewrite Hremove. destruct r; reflexivity.
Qed.

Lemma in_removelast_in : forall (A : Type) (x : A) xs,
  In x (removelast xs) -> In x xs.
Proof.
  intros A x xs. induction xs as [|a xs IH]; simpl; intros H; [contradiction|].
  destruct xs as [|b xs]; simpl in H |- *; [contradiction|].
  destruct H as [<- | H]; [now left | right; now apply IH].
Qed.

Lemma nonadjacent_sides_extend_right : forall l middle r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides l (middle ++ r)).
Proof.
  intros l middle r s. unfold nonadjacent_sides.
  rewrite !in_app_iff. intros [Hl | Hr]; [now left | right].
  destruct middle as [|a middle]; [exact Hr |].
  simpl. rewrite in_app_iff. right.
  destruct r as [|b r]; simpl in Hr |- *; [contradiction | now right].
Qed.

Lemma nonadjacent_sides_extend_left : forall l middle r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides (l ++ middle) r).
Proof.
  intros l middle r s. unfold nonadjacent_sides.
  rewrite !in_app_iff. intros [Hl | Hr]; [left | now right].
  destruct middle as [|a middle]; [now rewrite app_nil_r |].
  rewrite removelast_app by discriminate.
  rewrite in_app_iff. left. now apply in_removelast_in.
Qed.

(* strict 延長線と非隣接セグメントは、sub の閉長方形を避ける。
   隣接セグメントと sub の共有端点は、埋め込みの連結性側で扱う。 *)
Definition sparse_around (l sub r : list Segment) : Prop :=
  (forall p,
     (onHead_extend_strict (l ++ sub ++ r) p
      \/ onLast_extend_strict (l ++ sub ++ r) p) ->
     ~ in_rect_or_endpoints_at sub p)
  /\ (forall s p,
        In s (nonadjacent_sides l r) ->
        in_segment_rect_or_endpoints s p ->
        ~ in_rect_or_endpoints_at sub p).

(* ls の各セグメント出現の長方形について疎である。
   値が等しいセグメントが複数あっても、リスト中の位置を区別する。 *)
Definition sparse_embedding (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    sparse_around l [s] r.

(* 全域で疎であり、さらに指定した部分列 sub の周りでも疎である。 *)
Definition sparse (l sub r : list Segment) : Prop :=
  let ls := l ++ sub ++ r in
  sparse_embedding ls /\ sparse_around l sub r.

(* 各セグメントに対し、非隣接セグメントの閉端点長方形を分離する。 *)
Definition segment_rectangles_separated (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall t, In t (nonadjacent_sides l r) ->
    forall p,
      in_segment_rect_or_endpoints t p ->
      ~ in_rect_or_endpoints_at [s] p.

Definition extensions_avoid_segment_rectangles (ls : list Segment) : Prop :=
  forall l s r,
    ls = l ++ [s] ++ r ->
    forall p,
      (onHead_extend_strict ls p \/ onLast_extend_strict ls p) ->
      ~ in_rect_or_endpoints_at [s] p.

(* 矩形・延長線・端点についての局所的な分離条件から全域疎性を組み立てる。 *)
Lemma geometric_sparse_embedding :
  forall ls,
    segment_rectangles_separated ls ->
    extensions_avoid_segment_rectangles ls ->
    sparse_embedding ls.
Proof.
  intros ls Hrect Hext l s r Heq.
  split.
  - intros p [Hhead | Hlast].
    + apply (Hext l s r Heq p). left. rewrite Heq. exact Hhead.
    + apply (Hext l s r Heq p). right. rewrite Heq. exact Hlast.
  - intros t p Ht Hp. eapply Hrect; eauto.
Qed.

(* 先頭延長線と末尾延長線が互いに交わらない。 *)
Definition extensions_disjoint (ls : list Segment) : Prop :=
  forall p,
    onHead_extend ls p ->
    onLast_extend ls p ->
    False.

Lemma extend_head_from_repr : forall ls t s,
  ls <> [] ->
  nth_error ls (extend_index ls t) = Some s ->
  extend ls t = point s (extend_param ls t) ->
  extend_index ls t = 0%nat ->
  extend_param ls t <= 0 ->
  onHead_extend ls (extend ls t).
Proof.
  intros ls t s Hne Hnth Hrepr Hindex Hparam.
  assert (Hs : hd_segment ls = s).
  { destruct ls as [|a ls]; [contradiction|].
    unfold hd_segment. simpl.
    rewrite Hindex in Hnth. simpl in Hnth. now injection Hnth. }
  unfold onHead_extend, onHead. exists (extend_param ls t).
  split; [exact Hparam|]. now rewrite Hs, <- Hrepr.
Qed.

Lemma extend_last_from_repr : forall ls t s,
  ls <> [] ->
  nth_error ls (extend_index ls t) = Some s ->
  extend ls t = point s (extend_param ls t) ->
  S (extend_index ls t) = length ls ->
  1 < extend_param ls t ->
  onLast_extend ls (extend ls t).
Proof.
  intros ls t s Hne Hnth Hrepr Hindex Hparam.
  assert (Hs : s = last_segment ls).
  { unfold last_segment.
    assert (K : extend_index ls t = (length ls - 1)%nat) by lia.
    rewrite K in Hnth.
    pose proof (@nth_error_last Segment ls default_segment Hne) as Hlast.
    rewrite Hnth in Hlast. now injection Hlast. }
  unfold onLast_extend, onLast. exists (extend_param ls t).
  split; [lra|]. now rewrite <- Hs, <- Hrepr.
Qed.

Lemma same_extend_piece_no_collision : forall ls t1 t2 s1 s2,
  ls <> [] ->
  nth_error ls (extend_index ls t1) = Some s1 ->
  nth_error ls (extend_index ls t2) = Some s2 ->
  extend_index ls t1 = extend_index ls t2 ->
  point s1 (extend_param ls t1) = point s2 (extend_param ls t2) ->
  t1 = t2.
Proof.
  intros ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hindex Heq.
  assert (Hs : s1 = s2).
  { rewrite <- (nth_error_nth_eq ls (extend_index ls t1) s1 default_segment Hnth1).
    rewrite Hindex.
    now rewrite (nth_error_nth_eq ls (extend_index ls t2) s2 default_segment Hnth2). }
  subst s2.
  apply (extend_same_piece_injective ls t1 t2); [exact Hne | exact Hindex |].
  now apply (point_injective s1).
Qed.

Lemma on_segment_term_from_x : forall s p,
  onSegment s p -> fst p = fst (term s) -> p = term s.
Proof.
  intros s p [t [[Ht0 Ht1] <-]] Hx.
  assert (Ht : t = 1).
  { destruct (Req_dec t 1) as [-> | Hneq]; [reflexivity |].
    assert (Hlt : t < 1) by lra.
    destruct (x_strictly_monotone_seg s) as [Hinc | Hdec].
    - pose proof (Hinc t 1 ltac:(lra)) as Hstrict.
      unfold term in Hx. lra.
    - pose proof (Hdec t 1 ltac:(lra)) as Hstrict.
      unfold term in Hx. lra. }
  subst t. reflexivity.
Qed.

Lemma on_segment_term_from_y : forall s p,
  onSegment s p -> snd p = snd (term s) -> p = term s.
Proof.
  intros s p [t [[Ht0 Ht1] <-]] Hy.
  assert (Ht : t = 1).
  { destruct (Req_dec t 1) as [-> | Hneq]; [reflexivity |].
    assert (Hlt : t < 1) by lra.
    destruct (y_strictly_monotone_seg s) as [Hinc | Hdec].
    - pose proof (Hinc t 1 ltac:(lra)) as Hstrict.
      unfold term in Hy. lra.
    - pose proof (Hdec t 1 ltac:(lra)) as Hstrict.
      unfold term in Hy. lra. }
  subst t. reflexivity.
Qed.

(* 直接連結された二セグメントは共有端点以外では交わらない。 *)
Lemma adjacent_not_intersect_except_junction :
  forall ps1 ps2 s1 s2 p,
    dc ps1 ps2 ->
    embed ps1 s1 ->
    embed ps2 s2 ->
    term s1 = init s2 ->
    onSegment s1 p ->
    onSegment s2 p ->
    p = term s1.
Proof.
  intros ps1 ps2 s1 s2 [x y] Hdc Hembed1 Hembed2 Hjoin Hp1 Hp2.
  pose proof (f_equal fst Hjoin) as Hjoinx.
  pose proof (f_equal snd Hjoin) as Hjoiny.
  destruct Hdc as [v h c | h | h | h | h].
  - destruct h.
    + pose proof (e_onseg_relation s1 v c x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 v (i_c c) x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 v c x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 v (i_c c) x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - destruct h.
    + pose proof (e_onseg_relation s1 n cx x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 s cx x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 n cx x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 s cx x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - destruct h.
    + pose proof (e_onseg_relation s1 s cc x y Hembed1 Hp1) as [_ Hx1].
      pose proof (e_onseg_relation s2 n cc x y Hembed2 Hp2) as [Hx2 _].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [exact Hx1 | now rewrite Hjoinx].
    + pose proof (w_onseg_relation s1 s cc x y Hembed1 Hp1) as [Hx1 _].
      pose proof (w_onseg_relation s2 n cc x y Hembed2 Hp2) as [_ Hx2].
      apply on_segment_term_from_x; [exact Hp1 |]. simpl.
      apply Rle_antisym; [now rewrite Hjoinx | exact Hx1].
  - pose proof (n_onseg_relation s1 h cc x y Hembed1 Hp1) as [_ Hy1].
    pose proof (n_onseg_relation s2 (i_h h) cx x y Hembed2 Hp2) as [Hy2 _].
    apply on_segment_term_from_y; [exact Hp1 |]. simpl.
    apply Rle_antisym; [exact Hy1 | now rewrite Hjoiny].
  - pose proof (s_onseg_relation s1 h cx x y Hembed1 Hp1) as [Hy1 _].
    pose proof (s_onseg_relation s2 (i_h h) cc x y Hembed2 Hp2) as [_ Hy2].
    apply on_segment_term_from_y; [exact Hp1 |]. simpl.
    apply Rle_antisym; [now rewrite Hjoiny | exact Hy1].
Qed.

Lemma embed_scurve_nth_embed : forall sc ls,
  embed_scurve sc ls ->
  forall i s, nth_error ls i = Some s ->
  exists ps, nth_error (proj1_sig sc) i = Some ps /\ embed ps s.
Proof.
  intros sc ls Hembed.
  induction Hembed as
    [| ps seg0 Hps | ps lp A s1 s2 rest Hps Htail IH Hjoin];
    intros i seg Hnth.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-. exists ps. split; [reflexivity | exact Hps].
    + destruct i; discriminate.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-. exists ps. split; [reflexivity | exact Hps].
    + destruct (IH i seg Hnth) as [q [Hq Hqs]].
      exists q. split; [exact Hq | exact Hqs].
Qed.

Lemma is_scurve_adjacent_dc : forall ps i ps1 ps2,
  is_scurve ps ->
  nth_error ps i = Some ps1 ->
  nth_error ps (S i) = Some ps2 ->
  dc ps1 ps2.
Proof.
  intros ps i ps1 ps2 Hcurve. revert i ps1 ps2.
  induction Hcurve as [|p ps Hcurve IH Hhead]; intros i ps1 ps2 H1 H2.
  - destruct i; discriminate.
  - destruct i as [|i].
    + simpl in H1, H2. injection H1 as <-.
      destruct ps as [|q qs]; [discriminate|].
      simpl in H2. injection H2 as <-.
      inversion Hhead; subst. assumption.
    + simpl in H1, H2. eapply IH; eauto.
Qed.

Lemma embed_scurve_adjacent_data : forall sc ls i s1 s2,
  embed_scurve sc ls ->
  nth_error ls i = Some s1 ->
  nth_error ls (S i) = Some s2 ->
  exists ps1 ps2,
    embed ps1 s1 /\ embed ps2 s2 /\ dc ps1 ps2 /\ term s1 = init s2.
Proof.
  intros sc ls i s1 s2 Hembed H1 H2.
  destruct (embed_scurve_nth_embed sc ls Hembed i s1 H1)
    as [ps1 [Hp1 Hembed1]].
  destruct (embed_scurve_nth_embed sc ls Hembed (S i) s2 H2)
    as [ps2 [Hp2 Hembed2]].
  exists ps1, ps2. repeat split; try assumption.
  - eapply is_scurve_adjacent_dc; eauto. exact (proj2_sig sc).
  - eapply embed_scurve_connected; eauto.
Qed.

Lemma nonadjacent_sides_prefix : forall a l r s,
  In s (nonadjacent_sides l r) ->
  In s (nonadjacent_sides (a :: l) r).
Proof.
  intros a l r s. unfold nonadjacent_sides.
  destruct l as [|b l]; [simpl; tauto |].
  intros H. rewrite in_app_iff in H. rewrite in_app_iff.
  destruct H as [H | H].
  - left. simpl. now right.
  - now right.
Qed.

(* 添字が二つ以上離れた要素は、中心要素の非隣接部分に現れる。 *)
Lemma nth_error_far_in_nonadjacent_sides : forall ls i j s t,
  nth_error ls i = Some s ->
  nth_error ls j = Some t ->
  (S i < j \/ S j < i)%nat ->
  exists l r,
    ls = l ++ [s] ++ r /\ In t (nonadjacent_sides l r).
Proof.
  induction ls as [|a ls IH]; intros i j s t Hi Hj Hfar.
  - destruct i; discriminate.
  - destruct i as [|i], j as [|j].
    + lia.
    + simpl in Hi. injection Hi as <-.
      destruct j as [|j]; [lia|].
      simpl in Hj. destruct ls as [|b ls]; [discriminate|].
      simpl in Hj. exists [], (b :: ls). split; [reflexivity|].
      simpl. now apply nth_error_In in Hj.
    + simpl in Hj. injection Hj as <-.
      destruct i as [|i]; [lia|].
      simpl in Hi.
      destruct (@nth_error_split Segment ls (S i) s Hi)
        as [l [r [Hls Hlen]]].
      destruct l as [|b l]; [discriminate|].
      exists (a :: b :: l), r. split.
      * simpl. now rewrite Hls.
      * unfold nonadjacent_sides. rewrite in_app_iff. left. simpl. tauto.
    + simpl in Hi, Hj.
      destruct (IH i j s t Hi Hj ltac:(lia)) as [l [r [Hls Hin]]].
      exists (a :: l), r. split.
      * simpl. now rewrite Hls.
      * now apply nonadjacent_sides_prefix.
Qed.

(* 後のセグメントの始点以外の点は、それ以前のセグメント上に戻らない。 *)
Lemma later_body_point_not_on_earlier_segment :
  forall sc ls earlier later s_earlier s_later u,
    embed_scurve sc ls ->
    sparse_embedding ls ->
    nth_error ls earlier = Some s_earlier ->
    nth_error ls later = Some s_later ->
    (earlier < later)%nat ->
    0 < u <= 1 ->
    onSegment s_earlier (point s_later u) ->
    False.
Proof.
  intros sc ls earlier later s_earlier s_later u
    Hembed Hsparse Hearlier Hlater Hlt Hu HonEarlier.
  assert (HonLater : onSegment s_later (point s_later u)).
  { exists u. split; [lra | reflexivity]. }
  destruct (Nat.eq_dec later (S earlier)) as [Hadj | Hfar].
  - subst later.
    destruct (embed_scurve_adjacent_data
                sc ls earlier s_earlier s_later
                Hembed Hearlier Hlater)
      as [ps1 [ps2 [Hembed1 [Hembed2 [Hdc Hjoin]]]]].
    pose proof (adjacent_not_intersect_except_junction
                  ps1 ps2 s_earlier s_later (point s_later u)
                  Hdc Hembed1 Hembed2 Hjoin HonEarlier HonLater) as Hp.
    assert (Hzero : u = 0).
    { apply (point_injective s_later u 0).
      change (point s_later u = init s_later).
      now rewrite Hp. }
    lra.
  - assert (Hfar' : (S earlier < later)%nat) by lia.
    destruct (nth_error_far_in_nonadjacent_sides
                ls later earlier s_later s_earlier
                Hlater Hearlier ltac:(right; exact Hfar'))
      as [l [r [Hsplit Hin]]].
    destruct (Hsparse l s_later r Hsplit) as [_ Hrect].
    pose proof (Hrect s_earlier (point s_later u) Hin
                  (segment_in_rect_or_endpoints
                     s_earlier (point s_later u) HonEarlier)) as Havoid.
    apply Havoid. change (in_segment_rect_or_endpoints s_later (point s_later u)).
    exact (segment_in_rect_or_endpoints s_later (point s_later u) HonLater).
Qed.

Lemma sparse_body_collision_impossible : forall ls tb to sb so,
  ls <> [] ->
  (exists ds, embed_listDir ds ls) ->
  sparse_embedding ls ->
  nth_error ls (extend_index ls tb) = Some sb ->
  nth_error ls (extend_index ls to) = Some so ->
  extend_index ls tb <> extend_index ls to ->
  0 < extend_param ls tb <= 1 ->
  extend ls tb = point sb (extend_param ls tb) ->
  extend ls to = point so (extend_param ls to) ->
  extend ls tb = extend ls to ->
  False.
(* 非隣接なら sparse の長方形分離、隣接なら PrimitiveSegment
   埋め込みの方向条件から、異なる piece の衝突を除く。 *)
Proof.
  intros ls tb to sb so Hne [ds [sc [_ Hembed]]] Hsparse
    Hnthb Hntho Hindices Hbodyb Hreprb Hrepro Hcollision.
  set (ib := extend_index ls tb) in *.
  set (io := extend_index ls to) in *.
  set (ub := extend_param ls tb) in *.
  set (uo := extend_param ls to) in *.
  assert (Hpoints : point sb ub = point so uo).
  { rewrite <- Hreprb, <- Hrepro. exact Hcollision. }
  assert (Honb : onSegment sb (point sb ub)).
  { exists ub. split; [split; lra | reflexivity]. }
  assert (Hboxb : in_rect_or_endpoints_at [sb] (point sb ub)).
  { change (in_segment_rect_or_endpoints sb (point sb ub)).
    now apply segment_in_rect_or_endpoints. }
  destruct (extend_param_region ls to Hne)
    as [Hbodyo | [[Hio0 Huo] | [Hiolast Huo]]].
  - assert (Hono : onSegment so (point so uo)).
    { exists uo. split.
      - split; [now apply Rlt_le | exact (proj2 Hbodyo)].
      - reflexivity. }
    destruct (Nat.lt_trichotomy ib io) as [Hlt | [Heq | Hgt]].
    + eapply (later_body_point_not_on_earlier_segment
                sc ls ib io sb so uo Hembed Hsparse
                Hnthb Hntho Hlt Hbodyo).
      rewrite <- Hpoints. exact Honb.
    + now apply Hindices.
    + eapply (later_body_point_not_on_earlier_segment
                sc ls io ib so sb ub Hembed Hsparse
                Hntho Hnthb Hgt Hbodyb).
      rewrite Hpoints. exact Hono.
  - change (io = 0%nat) in Hio0.
    change (uo <= 0) in Huo.
    destruct (Rlt_dec uo 0) as [Huostrict | Huozero].
    + destruct (@nth_error_split Segment ls ib sb Hnthb)
        as [l [r [Hsplit _]]].
      destruct (Hsparse l sb r Hsplit) as [Hextend _].
      assert (Hwhole : l ++ [sb] ++ r = ls).
      { change (l ++ sb :: r = ls). now symmetry. }
      apply (Hextend (point sb ub)).
      * left. rewrite Hwhole. unfold onHead_extend_strict.
        assert (Hso : so = hd_segment ls).
        { rewrite Hio0 in Hntho. unfold hd_segment. symmetry.
          eapply nth_error_hd; exact Hntho. }
        exists uo. split; [exact Huostrict |].
        rewrite <- Hso, <- Hpoints. reflexivity.
      * exact Hboxb.
    + assert (Huo0 : uo = 0) by lra.
      assert (Hlt : (io < ib)%nat) by lia.
      eapply (later_body_point_not_on_earlier_segment
                sc ls io ib so sb ub Hembed Hsparse
                Hntho Hnthb Hlt Hbodyb).
      rewrite Hpoints, Huo0. apply onInit.
  - change (S io = length ls) in Hiolast.
    change (1 < uo) in Huo.
    destruct (@nth_error_split Segment ls ib sb Hnthb)
      as [l [r [Hsplit _]]].
    destruct (Hsparse l sb r Hsplit) as [Hextend _].
    assert (Hwhole : l ++ [sb] ++ r = ls).
    { change (l ++ sb :: r = ls). now symmetry. }
    apply (Hextend (point sb ub)).
    + right. rewrite Hwhole. unfold onLast_extend_strict.
      assert (Hso : so = last_segment ls).
      { unfold last_segment.
        assert (K : io = (length ls - 1)%nat) by lia.
        rewrite K in Hntho.
        pose proof (@nth_error_last Segment ls default_segment Hne) as Hlast.
        rewrite Hntho in Hlast. now injection Hlast. }
      exists uo. split; [exact Huo |].
      rewrite <- Hso, <- Hpoints. reflexivity.
    + exact Hboxb.
Qed.

Lemma sparse_extensions_open :
  forall ds ls,
    ls <> [] ->
    embed_listDir ds ls ->
    sparse_embedding ls ->
    extensions_disjoint ls ->
    ~ close ls.
Proof.
  intros ds ls Hne Hembed Hsparse Hdisjoint [t1 [t2 [Hneq Heq]]].
  destruct (extend_repr ls t1 Hne) as [s1 [Hnth1 Hrepr1]].
  destruct (extend_repr ls t2 Hne) as [s2 [Hnth2 Hrepr2]].
  assert (Hpoint : point s1 (extend_param ls t1) =
                   point s2 (extend_param ls t2)).
  { now rewrite <- Hrepr1, <- Hrepr2. }
  destruct (extend_param_region ls t1 Hne) as [Hbody1 | [Hhead1 | Hlast1]];
  destruct (extend_param_region ls t2 Hne) as [Hbody2 | [Hhead2 | Hlast2]].
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t1 t2 s1 s2
                Hne (ex_intro _ ds Hembed) Hsparse Hnth1 Hnth2 Hi Hbody1 Hrepr1 Hrepr2 Heq).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne (ex_intro _ ds Hembed) Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
  - apply Hneq. eapply same_extend_piece_no_collision; eauto; lia.
  - apply (Hdisjoint (extend ls t1)).
    + destruct Hhead1 as [Hi1 Hp1].
      exact (extend_head_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
    + rewrite Heq. destruct Hlast2 as [Hi2 Hp2].
      exact (extend_last_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
  - destruct (Nat.eq_dec (extend_index ls t1) (extend_index ls t2)) as [Hi|Hi].
    + apply Hneq. exact (same_extend_piece_no_collision ls t1 t2 s1 s2 Hne Hnth1 Hnth2 Hi Hpoint).
    + eapply (sparse_body_collision_impossible ls t2 t1 s2 s1
                Hne (ex_intro _ ds Hembed) Hsparse Hnth2 Hnth1 ltac:(congruence) Hbody2
                Hrepr2 Hrepr1 ltac:(congruence)).
  - apply (Hdisjoint (extend ls t2)).
    + destruct Hhead2 as [Hi2 Hp2].
      exact (extend_head_from_repr ls t2 s2 Hne Hnth2 Hrepr2 Hi2 Hp2).
    + rewrite <- Heq. destruct Hlast1 as [Hi1 Hp1].
      exact (extend_last_from_repr ls t1 s1 Hne Hnth1 Hrepr1 Hi1 Hp1).
  - apply Hneq. eapply same_extend_piece_no_collision; eauto; lia.
Qed.

Definition rot_rect (g : Rot) (Rc : Rect) : Rect :=
  match g with
  | R0   => Rc
  | R90  => mkRect (- ry1 Rc) (rx0 Rc) (- ry0 Rc) (rx1 Rc)
  | R180 => mkRect (- rx1 Rc) (- ry1 Rc) (- rx0 Rc) (- ry0 Rc)
  | R270 => mkRect (ry0 Rc) (- rx1 Rc) (ry1 Rc) (- rx0 Rc)
  end.

Lemma in_rect_rot :
  forall g Rc p, in_rect (rot_rect g Rc) (rot_pt g p) <-> in_rect Rc p.
Proof.
  intros g Rc [x y]. destruct g; unfold in_rect, rot_rect; simpl; split; intros; lra.
Qed.

Lemma rect_of_rot :
  forall g sub, sub <> [] -> rect_of (rot_segs g sub) = rot_rect g (rect_of sub).
Proof.
  intros g sub H. unfold rect_of, rot_segs.
  rewrite (hd_map_nonnil _ _ H), (last_map_nonnil _ _ H).
  unfold init, term. rewrite !rot_seg_point.
  destruct g; simpl; unfold rot_rect; simpl;
    rewrite ?Rmin_opp, ?Rmax_opp; reflexivity.
Qed.

Lemma rot_sparse_embedding :
  forall g ls,
    sparse_embedding ls ->
    sparse_embedding (rot_segs g ls).
Admitted.

Lemma rot_extensions_disjoint :
  forall g ls,
    extensions_disjoint ls ->
    extensions_disjoint (rot_segs g ls).
Admitted.
