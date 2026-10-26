Require Export Sparse.ClassifyGeometry.
From Stdlib Require Import Lra Psatz Field.
Import ListNotations.

(* 分類値そのものが端点の符号付き変位。倍率は証明の内部だけで使う。 *)
Definition EndpointClassifier : Type := Point -> R.

Definition move_point (k : EndpointClassifier) (p : Point) : Point :=
  (fst p, snd p + k p).

Definition scale_classifier (h : R) (k : EndpointClassifier) : EndpointClassifier :=
  fun p => h * k p.

Definition low_value (f : Point -> R) (s : Segment) : R :=
  match V_of (primitive_segment s) with
  | n => f (init s) | s => f (term s)
  end.

Definition high_value (f : Point -> R) (s : Segment) : R :=
  match V_of (primitive_segment s) with
  | n => f (term s) | s => f (init s)
  end.

Definition segment_x_range (s : Segment) (x : R) : Prop :=
  Rmin (init_x s) (term_x s) <= x <= Rmax (init_x s) (term_x s).

Definition segment_x_parameter (s : Segment) (x : R) : R :=
  (x - init_x s) / (term_x s - init_x s).

Definition chord_value (f : Point -> R) (s : Segment) (x : R) : R :=
  (1 - segment_x_parameter s x) * f (init s) +
  segment_x_parameter s x * f (term s).

Definition lower_value (f : Point -> R) (s : Segment) (x : R) : R :=
  match C_of (primitive_segment s) with
  | cx => chord_value f s x | cc => low_value f s
  end.

Definition upper_value (f : Point -> R) (s : Segment) (x : R) : R :=
  match C_of (primitive_segment s) with
  | cx => high_value f s | cc => chord_value f s x
  end.

Definition triangle_lower := lower_value (@snd R R).
Definition triangle_upper := upper_value (@snd R R).
Definition lower_displacement := lower_value.
Definition upper_displacement := upper_value.

Definition endpoint_displacements_ordered (k : EndpointClassifier) (s : Segment) : Prop :=
  low_value k s <= high_value k s.

Definition sub_x_left (sub : list Segment) (s : Segment) : R :=
  Rmax (rx0 (rect_of sub)) (rx0 (rect_of [s])).
Definition sub_x_right (sub : list Segment) (s : Segment) : R :=
  Rmin (rx1 (rect_of sub)) (rx1 (rect_of [s])).

Definition sub_overlap_endpoint (sub : list Segment) (s : Segment) (x : R) : Prop :=
  sub_x_left sub s <= sub_x_right sub s /\
  (x = sub_x_left sub s \/ x = sub_x_right sub s).

Lemma move_point_fst : forall k p, fst (move_point k p) = fst p.
Proof. reflexivity. Qed.

Lemma move_point_zero : forall k p, k p = 0 -> move_point k p = p.
Proof. intros k [x y] H. unfold move_point; simpl in *.
  rewrite H, Rplus_0_r. reflexivity. Qed.

Lemma low_high_y_bounds : forall seg,
  Rmin (init_y seg) (term_y seg) = low_value (@snd R R) seg /\
  Rmax (init_y seg) (term_y seg) = high_value (@snd R R) seg.
Proof.
  intro seg. pose proof (primitive_segment_embed seg) as H.
  destruct (primitive_segment seg) as [[v h] c] eqn:E.
  unfold low_value, high_value. rewrite E. destruct v; simpl.
  - pose proof (n_end_relation seg h c H).
    unfold init_y, term_y. rewrite Rmin_left, Rmax_right by lra. auto.
  - pose proof (s_end_relation seg h c H).
    unfold init_y, term_y. rewrite Rmin_right, Rmax_left by lra. auto.
Qed.

Lemma segment_x_parameter_between : forall seg x,
  segment_x_range seg x -> 0 <= segment_x_parameter seg x <= 1.
Proof.
  intros seg x Hx.
  assert (Hd : term_x seg - init_x seg <> 0).
  { pose proof (neq_init_term_x seg). lra. }
  assert (Hm : segment_x_parameter seg x * (term_x seg - init_x seg) =
                 x - init_x seg).
  { unfold segment_x_parameter. field. exact Hd. }
  unfold segment_x_range in Hx.
  destruct (Rle_dec (init_x seg) (term_x seg)).
  - rewrite Rmin_left, Rmax_right in Hx by assumption. split; nra.
  - rewrite Rmin_right, Rmax_left in Hx by lra. split; nra.
Qed.

Lemma chord_value_between : forall f seg x,
  endpoint_displacements_ordered f seg ->
  segment_x_range seg x ->
  low_value f seg <= chord_value f seg x <= high_value f seg.
Proof.
  intros f seg x Horder Hx.
  pose proof (segment_x_parameter_between seg x Hx).
  unfold endpoint_displacements_ordered, low_value, high_value in Horder |- *.
  unfold chord_value.
  destruct (V_of (primitive_segment seg)); simpl in *; split; nra.
Qed.

Lemma endpoint_y_ordered : forall seg,
  endpoint_displacements_ordered (@snd R R) seg.
Proof.
  intro seg. destruct (low_high_y_bounds seg) as [H0 H1].
  unfold endpoint_displacements_ordered. rewrite <- H0, <- H1.
  eapply Rle_trans; [apply Rmin_l | apply Rmax_l].
Qed.

Lemma chord_side_value : forall seg x y,
  chord_side seg (x,y) =
  (term_x seg - init_x seg)^2 * (y - chord_value (@snd R R) seg x).
Proof.
  intros. assert (Hd : term_x seg - init_x seg <> 0).
  { pose proof (neq_init_term_x seg). lra. }
  unfold chord_side, chord_value, segment_x_parameter.
  change ((term_x seg - init_x seg) *
    ((term_x seg - init_x seg) * (y - init_y seg) -
      (term_y seg - init_y seg) * (x - init_x seg)) =
    (term_x seg - init_x seg)^2 *
    (y - ((1 - (x-init_x seg)/(term_x seg-init_x seg))*init_y seg +
      (x-init_x seg)/(term_x seg-init_x seg)*term_y seg))).
  field. exact Hd.
Qed.

(* 既存の閉三角形と、PDF の上下の境界値による表現は一致する。 *)
Lemma in_triangle_iff_fibre : forall seg x y,
  in_segment_triangle seg (x,y) <->
  segment_x_range seg x /\ triangle_lower seg x <= y <= triangle_upper seg x.
Proof.
  intros seg x y.
  pose proof (low_high_y_bounds seg) as [Hlow Hhigh].
  pose proof (chord_side_value seg x y) as Hside.
  assert (Hsq : 0 < (term_x seg - init_x seg)^2).
  { pose proof (neq_init_term_x seg). nra. }
  unfold in_segment_triangle, in_segment_rect_or_endpoints, in_closed_rect.
  change ((segment_x_range seg x /\
     Rmin (init_y seg) (term_y seg) <= y <= Rmax (init_y seg) (term_y seg)) /\
     match C_of (primitive_segment seg) with
     | cx => 0 <= chord_side seg (x,y)
     | cc => chord_side seg (x,y) <= 0 end <->
     segment_x_range seg x /\ triangle_lower seg x <= y <= triangle_upper seg x).
  rewrite Hlow, Hhigh.
  unfold triangle_lower, triangle_upper, lower_value, upper_value.
  destruct (C_of (primitive_segment seg)); split.
  - intros [[Hx Hy] Hc].
    pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx).
    split; [exact Hx |]. split; nra.
  - intros [Hx Hy].
    pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx).
    split; [split; [exact Hx |]; nra | nra].
  - intros [[Hx Hy] Hc].
    pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx).
    split; [exact Hx |]. split; nra.
  - intros [Hx Hy].
    pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx).
    split; [split; [exact Hx |]; nra | nra].
Qed.

Lemma lower_value_add : forall f g seg x,
  lower_value (fun p => f p + g p) seg x =
  lower_value f seg x + lower_value g seg x.
Proof.
  intros. unfold lower_value, chord_value, low_value.
  destruct (C_of (primitive_segment seg)), (V_of (primitive_segment seg)); simpl; ring.
Qed.

Lemma upper_value_add : forall f g seg x,
  upper_value (fun p => f p + g p) seg x =
  upper_value f seg x + upper_value g seg x.
Proof.
  intros. unfold upper_value, chord_value, high_value.
  destruct (C_of (primitive_segment seg)), (V_of (primitive_segment seg)); simpl; ring.
Qed.

Lemma lower_value_scale : forall h k seg x,
  lower_value (scale_classifier h k) seg x = h * lower_value k seg x.
Proof.
  intros. unfold lower_value, chord_value, low_value, scale_classifier.
  destruct (C_of (primitive_segment seg)), (V_of (primitive_segment seg)); simpl; ring.
Qed.

Lemma upper_value_scale : forall h k seg x,
  upper_value (scale_classifier h k) seg x = h * upper_value k seg x.
Proof.
  intros. unfold upper_value, chord_value, high_value, scale_classifier.
  destruct (C_of (primitive_segment seg)), (V_of (primitive_segment seg)); simpl; ring.
Qed.

Definition affine_in_x (f : R -> R) : Prop :=
  exists a b, forall x, f x = a*x+b.

Lemma lower_value_affine : forall f seg, affine_in_x (lower_value f seg).
Proof.
  intros f seg. unfold lower_value.
  destruct (C_of (primitive_segment seg)).
  - exists ((f (term seg)-f (init seg))/(term_x seg-init_x seg)),
      (f (init seg)-init_x seg*((f (term seg)-f (init seg))/(term_x seg-init_x seg))).
    intros. unfold chord_value, segment_x_parameter, Rdiv. ring.
  - exists 0, (low_value f seg). intros; ring.
Qed.

Lemma upper_value_affine : forall f seg, affine_in_x (upper_value f seg).
Proof.
  intros f seg. unfold upper_value.
  destruct (C_of (primitive_segment seg)).
  - exists 0, (high_value f seg). intros; ring.
  - exists ((f (term seg)-f (init seg))/(term_x seg-init_x seg)),
      (f (init seg)-init_x seg*((f (term seg)-f (init seg))/(term_x seg-init_x seg))).
    intros. unfold chord_value, segment_x_parameter, Rdiv. ring.
Qed.

Lemma affine_add : forall f g,
  affine_in_x f -> affine_in_x g -> affine_in_x (fun x => f x+g x).
Proof.
  intros f g [a [b Hf]] [c [d Hg]]. exists (a+c), (b+d).
  intros; rewrite Hf,Hg; ring.
Qed.

Lemma affine_scale : forall h f,
  affine_in_x f -> affine_in_x (fun x => h*f x).
Proof.
  intros h f [a [b Hf]]. exists (h*a),(h*b).
  intros; rewrite Hf; ring.
Qed.

Lemma affine_above_on_interval : forall f lo hi c x,
  affine_in_x f -> lo <= x <= hi ->
  c < f lo -> c < f hi -> c < f x.
Proof.
  intros f lo hi c x [a [b Hf]] Hx Hlo Hhi.
  rewrite Hf in *. destruct (Rle_dec 0 a); nra.
Qed.

Lemma affine_below_on_interval : forall f lo hi c x,
  affine_in_x f -> lo <= x <= hi ->
  f lo < c -> f hi < c -> f x < c.
Proof.
  intros f lo hi c x [a [b Hf]] Hx Hlo Hhi.
  rewrite Hf in *. destruct (Rle_dec 0 a); nra.
Qed.

Lemma common_x_bounds : forall sub seg x,
  segment_x_range seg x /\ in_sub_x_range sub (x,0) <->
  sub_x_left sub seg <= x <= sub_x_right sub seg.
Proof.
  intros. unfold sub_x_left, sub_x_right, in_sub_x_range, segment_x_range.
  change ((Rmin (init_x seg) (term_x seg) <= x <= Rmax (init_x seg) (term_x seg) /\
     rx0 (rect_of sub) <= x <= rx1 (rect_of sub)) <->
    Rmax (rx0 (rect_of sub)) (Rmin (init_x seg) (term_x seg)) <= x <=
    Rmin (rx1 (rect_of sub)) (Rmax (init_x seg) (term_x seg))).
  unfold Rmin,Rmax; repeat destruct Rle_dec; simpl in *; split; intros; repeat split; lra.
Qed.

Lemma triangle_bounds_ordered : forall seg x,
  segment_x_range seg x -> triangle_lower seg x <= triangle_upper seg x.
Proof.
  intros seg x Hx.
  pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx) as H.
  unfold triangle_lower, triangle_upper, lower_value, upper_value.
  destruct (C_of (primitive_segment seg)); lra.
Qed.

Lemma segment_point_at_x : forall seg x,
  segment_x_range seg x ->
  exists y, onSegment seg (x,y) /\ triangle_lower seg x <= y <= triangle_upper seg x.
Proof.
  intros seg x Hx.
  destruct (segment_has_point_at_x seg x Hx) as [[a b] [Hp He]].
  simpl in He. subst a.
  exists b. split; [exact Hp |].
  pose proof (segment_in_endpoint_triangle seg (x,b) Hp) as Htri.
  apply in_triangle_iff_fibre in Htri. exact (proj2 Htri).
Qed.

Lemma chord_endpoint_x : forall seg x q,
  endpoint_of_seg seg q ->
  chord_value (@snd R R) seg x = snd q -> x=fst q.
Proof.
  intros seg x q Hq He.
  assert (Hd : term_x seg-init_x seg<>0) by (pose proof (neq_init_term_x seg); lra).
  assert (Hy : term_y seg-init_y seg<>0) by (pose proof (neq_init_term_y seg); lra).
  assert (Hm : chord_value (@snd R R) seg x*(term_x seg-init_x seg) =
    init_y seg*(term_x seg-init_x seg)+(x-init_x seg)*(term_y seg-init_y seg)).
  { unfold chord_value,segment_x_parameter. change
      (((1-(x-init_x seg)/(term_x seg-init_x seg))*init_y seg+
      (x-init_x seg)/(term_x seg-init_x seg)*term_y seg)*(term_x seg-init_x seg)=
      init_y seg*(term_x seg-init_x seg)+(x-init_x seg)*(term_y seg-init_y seg)).
    field. exact Hd. }
  destruct Hq as [-> | ->]; unfold init_x,term_x,init_y,term_y in *; rewrite He in Hm.
  - assert (Hprod : (x-fst (init seg))*(snd (term seg)-snd (init seg))=0) by nra.
    apply Rmult_integral in Hprod. destruct Hprod; lra.
  - assert (Hprod : (x-fst (term seg))*(snd (term seg)-snd (init seg))=0) by nra.
    apply Rmult_integral in Hprod. destruct Hprod; lra.
Qed.

(* cc の最高点、cx の最低点は、それぞれ対応する端点だけである。 *)
Lemma triangle_exposed_endpoint : forall seg p q,
  endpoint_of_seg seg q -> in_segment_triangle seg p ->
  ((C_of (primitive_segment seg)=cc /\
     high_value (@snd R R) seg<=snd p /\ snd q=high_value (@snd R R) seg) \/
   (C_of (primitive_segment seg)=cx /\
     snd p<=low_value (@snd R R) seg /\ snd q=low_value (@snd R R) seg)) ->
  p=q.
Proof.
  intros seg [x y] [xq yq] Hq Hp Hside.
  apply in_triangle_iff_fibre in Hp. destruct Hp as [Hx Hy].
  pose proof (chord_value_between (@snd R R) seg x (endpoint_y_ordered seg) Hx) as Hch.
  unfold triangle_lower,triangle_upper,lower_value,upper_value in Hy.
  simpl in Hside.
  assert (He : chord_value (@snd R R) seg x=yq /\ y=yq).
  { destruct Hside as [[Hc Hbounds] | [Hc Hbounds]]; rewrite Hc in Hy; simpl in *; split; lra. }
  destruct He as [Hc Hyq].
  pose proof (chord_endpoint_x seg x (xq,yq) Hq Hc) as Hxq. simpl in Hxq.
  now subst.
Qed.

Lemma east_triangle_exposed_init : forall seg p,
  (embed (n,e,cc) seg \/ embed (s,e,cx) seg) ->
  in_segment_triangle seg p -> fst p<=init_x seg -> p=init seg.
Proof.
  intros seg [x y] Htype Hp Hleft.
  apply in_triangle_iff_fibre in Hp. destruct Hp as [Hx Hy].
  assert (Hright : init_x seg<term_x seg).
  { destruct Htype as [H | H]; eapply e_end_relation; exact H. }
  unfold segment_x_range in Hx. rewrite Rmin_left,Rmax_right in Hx by lra.
  simpl in Hleft. assert (Hx0 : x=init_x seg) by lra. subst x.
  assert (H0 : segment_x_parameter seg (init_x seg)=0).
  { unfold segment_x_parameter,Rdiv. ring. }
  assert (Hch : chord_value (@snd R R) seg (init_x seg)=init_y seg).
  { unfold chord_value. rewrite H0. unfold init_y. ring. }
  assert (Hy0 : y=init_y seg).
  { destruct Htype as [He | He].
    - assert (Hpc : primitive_segment seg=(n,e,cc)).
      { eapply embed_unique; [apply primitive_segment_embed | exact He]. }
      unfold triangle_lower,triangle_upper,lower_value,upper_value,low_value,high_value in Hy.
      rewrite Hpc in Hy.
      change (init_y seg<=y<=chord_value (@snd R R) seg (init_x seg)) in Hy.
      rewrite Hch in Hy. lra.
    - assert (Hpc : primitive_segment seg=(s,e,cx)).
      { eapply embed_unique; [apply primitive_segment_embed | exact He]. }
      unfold triangle_lower,triangle_upper,lower_value,upper_value,low_value,high_value in Hy.
      rewrite Hpc in Hy.
      change (chord_value (@snd R R) seg (init_x seg)<=y<=init_y seg) in Hy.
      rewrite Hch in Hy. lra. }
  unfold init_x,init_y in *. destruct (init seg). simpl in *. now subst.
Qed.
