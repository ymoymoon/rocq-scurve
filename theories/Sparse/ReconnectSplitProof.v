Require Export Sparse.ReconnectSeparation.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

(* [reconnect_split] で通常再接続から実際に置換され得る二つの位置。
   左の末尾蓋と右の先頭蓋以外では、安全版と通常版は同じ曲線である。 *)
Definition reconnect_split_lid_index
    (l sub r : list Segment) (i : nat) : Prop :=
  (terminal_lid l /\ i = (length l - 1)%nat)
  \/ (initial_lid r /\ i = (length l + length sub)%nat).

(* 安全版の出現から、同じ添字にある元セグメントと通常再接続版を取る。
   ここでは長さ保存しか使わず、曲線の幾何には触れない。 *)
Lemma reconnect_split_nth_witnesses :
  forall l sub r h i safe,
    nth_error (reconnect_split l sub r h) i = Some safe ->
    exists old ordinary,
      nth_error (l ++ sub ++ r) i = Some old
      /\ nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary.
Proof.
  intros l sub r h i safe Hsafe.
  destruct (nth_error_exists_at_equal_length
              (l ++ sub ++ r) (reconnect_split l sub r h) i safe)
    as [old Hold].
  { symmetry. apply reconnect_split_safe_length. }
  { exact Hsafe. }
  destruct (nth_error_exists_at_equal_length
              (ordinary_reconnect_split l sub r h)
              (reconnect_split l sub r h) i safe)
    as [ordinary Hordinary].
  { rewrite ordinary_reconnect_split_length,
      reconnect_split_safe_length. reflexivity. }
  { exact Hsafe. }
  now exists old, ordinary.
Qed.

(* 蓋位置でなければ、[reconnect_split] は通常再接続の要素をそのまま使う。
   これは [reconnect_left]/[reconnect_right] のリスト操作だけから従う。 *)
Lemma nth_error_removelast_before_last :
  forall (A : Type) (xs : list A) i,
    (S i < length xs)%nat ->
    nth_error (removelast xs) i = nth_error xs i.
Proof.
  intros A xs. induction xs as [|a xs IH]; intros i Hi; [simpl in Hi; lia |].
  destruct xs as [|b xs].
  - simpl in Hi. lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl. apply IH. simpl. now apply Nat.succ_lt_mono in Hi.
Qed.

Lemma reconnect_split_nth_eq_ordinary_unless_lid :
  forall l sub r h i ordinary safe,
    ~ reconnect_split_lid_index l sub r i ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary ->
    nth_error (reconnect_split l sub r h) i = Some safe ->
    safe = ordinary.
Proof.
  intros l sub r h i ordinary safe HnotLid Hordinary Hsafe.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (HordinaryL :
        nth_error (reconnect_segs l sub r h l) i = Some ordinary).
    { rewrite <- Hordinary. unfold ordinary_reconnect_split.
      symmetry. apply nth_error_app1.
      now rewrite reconnect_segs_length. }
    assert (HsafeL : nth_error (reconnect_left l sub r h) i = Some safe).
    { rewrite <- Hsafe. unfold reconnect_split.
      symmetry. apply nth_error_app1.
      now rewrite reconnect_left_length. }
    destruct (excluded_middle_informative (terminal_lid l))
      as [Hterminal | Hterminal].
    + rewrite reconnect_left_terminal_eq in HsafeL by exact Hterminal.
      assert (Hinot : i <> (length l - 1)%nat).
      { intro Hi. apply HnotLid. left. now split. }
      assert (Hbefore : (S i < length l)%nat) by lia.
      assert (HremoveLen :
          length (removelast (reconnect_segs l sub r h l)) =
            (length l - 1)%nat).
      { pose proof (removelast_length_nonempty
                      Segment (reconnect_segs l sub r h l)) as Hlen.
        assert (Hmap : reconnect_segs l sub r h l <> []).
        { intro Hnil. apply (proj1 Hterminal).
          apply length_zero_iff_nil.
          pose proof (f_equal (@length Segment) Hnil) as Hzero.
          now rewrite reconnect_segs_length in Hzero. }
        specialize (Hlen Hmap). rewrite reconnect_segs_length in Hlen. lia. }
      rewrite nth_error_app1 in HsafeL by (rewrite HremoveLen; lia).
      rewrite (nth_error_removelast_before_last
                 Segment (reconnect_segs l sub r h l) i) in HsafeL
        by now rewrite reconnect_segs_length.
      congruence.
    + rewrite reconnect_left_nonterminal_eq in HsafeL by exact Hterminal.
      congruence.
  - set (k := (i - length l)%nat).
    assert (HordinaryTail :
        nth_error (sub ++ reconnect_segs l sub r h r) k = Some ordinary).
    { unfold k. unfold ordinary_reconnect_split in Hordinary.
      rewrite nth_error_app2 in Hordinary
        by (rewrite reconnect_segs_length; lia).
      now rewrite reconnect_segs_length in Hordinary. }
    assert (HsafeTail :
        nth_error (sub ++ reconnect_right l sub r h) k = Some safe).
    { unfold k. unfold reconnect_split in Hsafe.
      rewrite nth_error_app2 in Hsafe by (rewrite reconnect_left_length; lia).
      now rewrite reconnect_left_length in Hsafe. }
    destruct (Nat.lt_ge_cases k (length sub)) as [Hksub | Hksub].
    + rewrite nth_error_app1 in HordinaryTail by exact Hksub.
      rewrite nth_error_app1 in HsafeTail by exact Hksub.
      congruence.
    + set (q := (k - length sub)%nat).
      assert (HordinaryR :
          nth_error (reconnect_segs l sub r h r) q = Some ordinary).
      { unfold q. rewrite nth_error_app2 in HordinaryTail by lia.
        exact HordinaryTail. }
      assert (HsafeR : nth_error (reconnect_right l sub r h) q = Some safe).
      { unfold q. rewrite nth_error_app2 in HsafeTail by lia. exact HsafeTail. }
      destruct (excluded_middle_informative (initial_lid r))
        as [Hinitial | Hinitial].
      * rewrite reconnect_right_initial_eq in HsafeR by exact Hinitial.
        assert (Hqnot : q <> 0%nat).
        { intro Hq. apply HnotLid. right. split; [exact Hinitial |].
          unfold q, k in Hq. lia. }
        destruct q as [|q]; [contradiction |].
        simpl in HsafeR.
        destruct r as [|a r']; [exfalso; apply (proj1 Hinitial); reflexivity |].
        simpl in HordinaryR, HsafeR. congruence.
      * rewrite reconnect_right_noninitial_eq in HsafeR by exact Hinitial.
        congruence.
Qed.

(* 左蓋が有効なら、安全版の左部分の末尾添字には選択した蓋が現れる。 *)
Lemma reconnect_split_terminal_lid_nth :
  forall l sub r h,
    terminal_lid l ->
    nth_error (reconnect_split l sub r h) (length l - 1) =
      Some (choose_terminal_lid l sub r h).
Proof.
  intros l sub r h Hlid.
  destruct Hlid as [Hl Hwest].
  unfold reconnect_split.
  rewrite nth_error_app1.
  2: rewrite reconnect_left_length; destruct l; [contradiction | simpl; lia].
  rewrite reconnect_left_terminal_eq by now split.
  assert (Hmap : reconnect_segs l sub r h l <> []).
  { intro Hnil. apply Hl. apply length_zero_iff_nil.
    pose proof (f_equal (@length Segment) Hnil) as Hlen.
    now rewrite reconnect_segs_length in Hlen. }
  assert (Hremove :
      length (removelast (reconnect_segs l sub r h l)) = (length l - 1)%nat).
  { pose proof (removelast_length_nonempty
                  Segment (reconnect_segs l sub r h l) Hmap) as Hlen.
    rewrite reconnect_segs_length in Hlen. lia. }
  rewrite nth_error_app2 by (rewrite Hremove; lia).
  rewrite Hremove. replace (length l - 1 - (length l - 1))%nat with 0%nat by lia.
  reflexivity.
Qed.

(* 左蓋から二つ以上離れた通常版の出現は、左蓋の blocker 列に入る。 *)
Lemma ordinary_far_from_terminal_lid_in_blockers :
  forall l sub r h j ordinary,
    terminal_lid l ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary ->
    (S (length l - 1) < j \/ S j < length l - 1)%nat ->
    In ordinary (terminal_lid_blockers l sub r h).
Proof.
  intros l sub r h j ordinary [Hl Hwest] Hnth Hfar.
  assert (Hlpos : (0 < length l)%nat).
  { destruct l; [contradiction | simpl; lia]. }
  unfold ordinary_reconnect_split in Hnth.
  unfold terminal_lid_blockers, nonadjacent_sides.
  rewrite in_app_iff.
  destruct Hfar as [Hright | Hleft].
  - right.
    rewrite nth_error_app2 in Hnth
      by (rewrite reconnect_segs_length; lia).
    rewrite reconnect_segs_length in Hnth.
    set (k := (j - length l)%nat) in *.
    assert (Hk : (0 < k)%nat) by (unfold k; lia).
    destruct k as [|k]; [lia |].
    destruct (sub ++ reconnect_segs l sub r h r) as [|a tail] eqn:Htail.
    { simpl in Hnth. discriminate. }
    simpl in Hnth |- *.
    now apply nth_error_In in Hnth.
  - left.
    assert (HnthL :
        nth_error (reconnect_segs l sub r h l) j = Some ordinary).
    { rewrite nth_error_app1 in Hnth
        by (rewrite reconnect_segs_length; lia).
      exact Hnth. }
    assert (Hmap : reconnect_segs l sub r h l <> []).
    { intro Hnil. apply Hl. apply length_zero_iff_nil.
      pose proof (f_equal (@length Segment) Hnil) as Hzero.
      now rewrite reconnect_segs_length in Hzero. }
    assert (HremoveLen :
        length (removelast (reconnect_segs l sub r h l)) =
          (length l - 1)%nat).
    { pose proof (removelast_length_nonempty
                    Segment (reconnect_segs l sub r h l) Hmap) as Hlen.
      rewrite reconnect_segs_length in Hlen. lia. }
    assert (HnthRemove :
        nth_error (removelast (reconnect_segs l sub r h l)) j =
          Some ordinary).
    { rewrite nth_error_removelast_before_last.
      - exact HnthL.
      - rewrite reconnect_segs_length. lia. }
    apply nth_error_In with (n := j).
    rewrite nth_error_removelast_before_last.
    + exact HnthRemove.
    + now rewrite HremoveLen.
Qed.

(* 右蓋が有効なら、全体で [length l + length sub] の位置に現れる。 *)
Lemma reconnect_split_initial_lid_nth :
  forall l sub r h,
    initial_lid r ->
    nth_error (reconnect_split l sub r h) (length l + length sub) =
      Some (choose_initial_lid l sub r h).
Proof.
  intros l sub r h Hlid.
  destruct Hlid as [Hr Hwest].
  unfold reconnect_split.
  rewrite nth_error_app2 by (rewrite reconnect_left_length; lia).
  rewrite reconnect_left_length.
  replace (length l + length sub - length l)%nat with (length sub) by lia.
  rewrite nth_error_app2 by lia.
  replace (length sub - length sub)%nat with 0%nat by lia.
  rewrite reconnect_right_initial_eq by now split.
  reflexivity.
Qed.

(* 右蓋から二つ以上離れた通常版の出現は、右蓋の blocker 列に入る。 *)
Lemma ordinary_far_from_initial_lid_in_blockers :
  forall l sub r h j ordinary,
    initial_lid r ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary ->
    (S (length l + length sub) < j
     \/ S j < length l + length sub)%nat ->
    In ordinary (initial_lid_blockers l sub r h).
Proof.
  intros l sub r h j ordinary [Hr Hwest] Hnth Hfar.
  unfold ordinary_reconnect_split in Hnth.
  rewrite app_assoc in Hnth.
  unfold initial_lid_blockers, nonadjacent_sides.
  rewrite in_app_iff.
  destruct Hfar as [Hright | Hleft].
  - right.
    rewrite nth_error_app2 in Hnth.
    2: rewrite length_app, reconnect_segs_length; lia.
    rewrite length_app, reconnect_segs_length in Hnth.
    set (k := (j - (length l + length sub))%nat) in *.
    assert (Hk : (1 < k)%nat) by (unfold k; lia).
    destruct k as [|[|k]]; [lia | lia |].
    destruct (reconnect_segs l sub r h r) as [|a [|b tail]] eqn:HrightList.
    { simpl in Hnth. discriminate. }
    { simpl in Hnth. discriminate. }
    simpl in Hnth |- *.
    now apply nth_error_In in Hnth.
  - left.
    assert (HnthPrefix :
        nth_error (reconnect_segs l sub r h l ++ sub) j = Some ordinary).
    { rewrite nth_error_app1 in Hnth.
      - exact Hnth.
      - rewrite length_app, reconnect_segs_length. lia. }
    apply nth_error_In with (n := j).
    rewrite nth_error_removelast_before_last.
    + exact HnthPrefix.
    + rewrite length_app, reconnect_segs_length. exact Hleft.
Qed.

(* 左蓋は、その添字から二つ以上離れた安全版セグメントの長方形を
   blocker として避ける。この枝では蓋自身の長方形分離を要求しない。 *)
Lemma reconnect_split_terminal_lid_avoids_far_body :
  forall ds l sub r h i j lid other p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    terminal_lid l ->
    i = (length l - 1)%nat ->
    nth_error (reconnect_split l sub r h) i = Some lid ->
    nth_error (reconnect_split l sub r h) j = Some other ->
    (S i < j \/ S j < i)%nat ->
    onSegment lid p ->
    onSegment other p ->
    False.
Proof.
  intros ds l sub r h i j lid other p Hsub Hconn Hmono Hh Hsparse
    Hembed Hext Hlid Hi HlidNth HotherNth Hfar HlidPoint HotherPoint.
  subst i.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  destruct (reconnect_split_nth_witnesses l sub r h j other HotherNth)
    as [old [ordinary [Hold Hordinary]]].
  assert (Hbox : same_segment_box ordinary other).
  { exact (proj1 (ordinary_safe_nth_same_box
                    l sub r h j old ordinary other Hsub Hconn Hmono Hh
                    Hsparse Hwhole (ex_intro _ ds Hembed) Hext Hrec
                    Hold Hordinary HotherNth)). }
  assert (Hchosen : lid = choose_terminal_lid l sub r h).
  { pose proof (reconnect_split_terminal_lid_nth l sub r h Hlid) as Hnth.
    rewrite HlidNth in Hnth. now injection Hnth. }
  subst lid.
  pose proof (choose_terminal_lid_spec
                l sub r h Hsub Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hlid) as Hspec.
  destruct Hspec as [_ [_ Havoid]].
  eapply (Havoid ordinary p).
  - eapply ordinary_far_from_terminal_lid_in_blockers; eauto.
  - apply (same_segment_box_contains other ordinary p).
    + destruct Hbox as [Hinit Hterm]. split; symmetry; assumption.
    + now apply segment_in_rect_or_endpoints.
  - exact HlidPoint.
Qed.

(* 右蓋についての双対。選択した蓋の曲線本体が、非隣接な安全版の
   端点長方形を避けることを blocker 仕様から取り出す。 *)
Lemma reconnect_split_initial_lid_avoids_far_body :
  forall ds l sub r h i j lid other p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    initial_lid r ->
    i = (length l + length sub)%nat ->
    nth_error (reconnect_split l sub r h) i = Some lid ->
    nth_error (reconnect_split l sub r h) j = Some other ->
    (S i < j \/ S j < i)%nat ->
    onSegment lid p ->
    onSegment other p ->
    False.
Proof.
  intros ds l sub r h i j lid other p Hsub Hconn Hmono Hh Hsparse
    Hembed Hext Hlid Hi HlidNth HotherNth Hfar HlidPoint HotherPoint.
  subst i.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  destruct (reconnect_split_nth_witnesses l sub r h j other HotherNth)
    as [old [ordinary [Hold Hordinary]]].
  assert (Hbox : same_segment_box ordinary other).
  { exact (proj1 (ordinary_safe_nth_same_box
                    l sub r h j old ordinary other Hsub Hconn Hmono Hh
                    Hsparse Hwhole (ex_intro _ ds Hembed) Hext Hrec
                    Hold Hordinary HotherNth)). }
  assert (Hchosen : lid = choose_initial_lid l sub r h).
  { pose proof (reconnect_split_initial_lid_nth l sub r h Hlid) as Hnth.
    rewrite HlidNth in Hnth. now injection Hnth. }
  subst lid.
  pose proof (choose_initial_lid_spec
                l sub r h Hsub Hconn Hmono Hh Hsparse Hwhole
                (ex_intro _ ds Hembed) Hext Hlid) as Hspec.
  destruct Hspec as [_ [_ Havoid]].
  eapply (Havoid ordinary p).
  - eapply ordinary_far_from_initial_lid_in_blockers; eauto.
  - apply (same_segment_box_contains other ordinary p).
    + destruct Hbox as [Hinit Hterm]. split; symmetry; assumption.
    + now apply segment_in_rect_or_endpoints.
  - exact HlidPoint.
Qed.

(* 元の sparse 列では、二つ以上離れた出現の閉端点長方形は
   水平または垂直のいずれかに厳密分離している。 *)
Lemma sparse_far_rectangles_axis_separated :
  forall ls i j s t,
    sparse_embedding ls ->
    nth_error ls i = Some s ->
    nth_error ls j = Some t ->
    (S i < j \/ S j < i)%nat ->
    endpoint_rectangles_axis_separated s t.
Proof.
  intros ls i j s t Hsparse Hs Ht Hfar.
  destruct (nth_error_far_in_nonadjacent_sides ls i j s t Hs Ht Hfar)
    as [before [after [Hsplit Hin]]].
  apply rectangles_avoid_implies_axis_separated.
  intros p Htp.
  exact ((proj2 (Hsparse before s after Hsplit)) t p Hin Htp).
Qed.

(* 三分割列の一出現を、左外部・左接続・sub・右接続・右外部の
   五種類へ、値ではなく添字を保ったまま分類する。 *)
Inductive split_occurrence
    (l sub r : list Segment) (i : nat) (seg : Segment) : Prop :=
| SplitOccLeftOuter :
    (i < length l - 1)%nat ->
    nth_error l i = Some seg ->
    split_occurrence l sub r i seg
| SplitOccLeftBoundary :
    l <> [] ->
    i = (length l - 1)%nat ->
    seg = last_segment l ->
    split_occurrence l sub r i seg
| SplitOccSub :
    forall k,
      (k < length sub)%nat ->
      i = (length l + k)%nat ->
      nth_error sub k = Some seg ->
      split_occurrence l sub r i seg
| SplitOccRightBoundary :
    r <> [] ->
    i = (length l + length sub)%nat ->
    seg = hd_segment r ->
    split_occurrence l sub r i seg
| SplitOccRightOuter :
    forall k,
      (0 < k)%nat ->
      i = (length l + length sub + k)%nat ->
      nth_error r k = Some seg ->
      split_occurrence l sub r i seg.

Lemma nth_error_split_occurrence :
  forall l sub r i seg,
    nth_error (l ++ sub ++ r) i = Some seg ->
    split_occurrence l sub r i seg.
Proof.
  intros l sub r i seg Hnth.
  destruct (Nat.lt_ge_cases i (length l)) as [Hil | Hil].
  - assert (HnthL : nth_error l i = Some seg).
    { rewrite nth_error_app1 in Hnth by exact Hil. exact Hnth. }
    destruct (Nat.eq_dec i (length l - 1)%nat) as [Hi | Hi].
    + assert (Hlne : l <> []).
      { intro Hnil. rewrite Hnil in HnthL. destruct i; discriminate. }
      apply SplitOccLeftBoundary.
      * exact Hlne.
      * exact Hi.
      * subst i.
        assert (Hlast :
            nth_error l (length l - 1) = Some (last_segment l)).
        { unfold last_segment. now apply nth_error_last. }
        rewrite HnthL in Hlast. now injection Hlast.
    + apply SplitOccLeftOuter; [lia | exact HnthL].
  - set (k := (i - length l)%nat).
    assert (HnthTail : nth_error (sub ++ r) k = Some seg).
    { unfold k. rewrite nth_error_app2 in Hnth by lia. exact Hnth. }
    destruct (Nat.lt_ge_cases k (length sub)) as [Hks | Hks].
    + apply (SplitOccSub l sub r i seg k); [exact Hks | unfold k; lia |].
      rewrite nth_error_app1 in HnthTail by exact Hks. exact HnthTail.
    + set (q := (k - length sub)%nat).
      assert (HnthR : nth_error r q = Some seg).
      { unfold q. rewrite nth_error_app2 in HnthTail by lia. exact HnthTail. }
      assert (Hik : i = (length l + k)%nat) by (unfold k; lia).
      assert (Hkq : k = (length sub + q)%nat) by (unfold q; lia).
      destruct q as [|q].
      * assert (Hrne : r <> []).
        { intro Hnil. rewrite Hnil in HnthR. discriminate. }
        apply SplitOccRightBoundary.
        -- exact Hrne.
        -- lia.
        -- destruct r as [|a r']; [contradiction |].
           simpl in HnthR. injection HnthR as <-. reflexivity.
      * apply (SplitOccRightOuter l sub r i seg (S q)).
        -- lia.
        -- lia.
        -- exact HnthR.
Qed.

(* sub の一セグメントの端点は、全体の x 範囲と y-bbox に入る。 *)
Lemma sub_member_endpoint_bounds :
  forall sub t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    In t sub ->
    (rx0 (rect_of sub) <= fst (init t) <= rx1 (rect_of sub)
     /\ ry0 (bbox_of sub) <= snd (init t) <= ry1 (bbox_of sub))
    /\
    (rx0 (rect_of sub) <= fst (term t) <= rx1 (rect_of sub)
     /\ ry0 (bbox_of sub) <= snd (term t) <= ry1 (bbox_of sub)).
Proof.
  intros sub t Hsub Hconn Hmono Ht.
  assert (HinitOn : onSegmentlist sub (init t)).
  { exists t. split; [exact Ht | apply onInit]. }
  assert (HtermOn : onSegmentlist sub (term t)).
  { exists t. split; [exact Ht | apply onTerm]. }
  pose proof (x_monotone_sub_point_in_x_range
                sub (init t) Hsub Hconn Hmono HinitOn) as Hix.
  pose proof (x_monotone_sub_point_in_x_range
                sub (term t) Hsub Hconn Hmono HtermOn) as Htx.
  pose proof (bbox_of_bounds sub (init t) HinitOn) as Hiy.
  pose proof (bbox_of_bounds sub (term t) HtermOn) as Hty.
  unfold in_sub_x_range in Hix, Htx.
  exact (conj (conj Hix Hiy) (conj Htx Hty)).
Qed.

(* sub 全体から上下左右に離れた端点長方形は、sub の各セグメントの
   端点長方形とも同じ軸方向に厳密分離する。 *)
Lemma endpoint_box_separated_from_sub_separates_member :
  forall sub outside inside,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    In inside sub ->
    endpoint_box_separated_from_sub sub (init outside) (term outside) ->
    endpoint_rectangles_axis_separated outside inside.
Proof.
  intros sub outside inside Hsub Hconn Hmono Hinside Hsep.
  destruct (sub_member_endpoint_bounds
              sub inside Hsub Hconn Hmono Hinside)
    as [[[Hix0 Hix1] [Hiy0 Hiy1]] [[Htx0 Htx1] [Hty0 Hty1]]].
  unfold endpoint_rectangles_axis_separated.
  destruct Hsep as [Habove | [Hbelow | [Hleft | Hright]]].
  - right; right; left.
    unfold both_above_of_sub in Habove. destruct Habove as [Ha Hb].
    change (Rmax (snd (init inside)) (snd (term inside)) <
            Rmin (snd (init outside)) (snd (term outside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - right; right; right.
    unfold both_below_of_sub in Hbelow. destruct Hbelow as [Ha Hb].
    change (Rmax (snd (init outside)) (snd (term outside)) <
            Rmin (snd (init inside)) (snd (term inside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - right; left.
    unfold both_left_of_sub in Hleft. destruct Hleft as [Ha Hb].
    change (Rmax (fst (init outside)) (fst (term outside)) <
            Rmin (fst (init inside)) (fst (term inside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
  - left.
    unfold both_right_of_sub in Hright. destruct Hright as [Ha Hb].
    change (Rmax (fst (init inside)) (fst (term inside)) <
            Rmin (fst (init outside)) (fst (term outside))).
    apply Rmax_lub_lt; apply Rmin_glb_lt; lra.
Qed.

Definition split_boundary_occurrence
    (l sub r : list Segment) (i : nat) (seg : Segment) : Prop :=
  (l <> [] /\ i = (length l - 1)%nat /\ seg = last_segment l)
  \/ (r <> [] /\ i = (length l + length sub)%nat /\ seg = hd_segment r).

(* 境界出現でなければ、五分解の残りは sub 内か左右の非隣接部分である。 *)
Lemma split_occurrence_nonboundary :
  forall l sub r i seg,
    split_occurrence l sub r i seg ->
    ~ split_boundary_occurrence l sub r i seg ->
    In seg (nonadjacent_sides l r) \/ In seg sub.
Proof.
  intros l sub r i seg Hocc Hnot.
  destruct Hocc as
    [Hbefore HnthL | Hl Hi -> | k Hks Hi HnthS |
     Hr Hi -> | k Hk Hi HnthR].
  - left. unfold nonadjacent_sides. rewrite in_app_iff. left.
    apply nth_error_In with (n := i).
    rewrite nth_error_removelast_before_last.
    + exact HnthL.
    + lia.
  - exfalso. apply Hnot. left. repeat split; assumption.
  - right. now apply nth_error_In in HnthS.
  - exfalso. apply Hnot. right. repeat split; assumption.
  - left. unfold nonadjacent_sides. rewrite in_app_iff. right.
    destruct r as [|a r']; [destruct k; discriminate |].
    destruct k as [|k]; [lia |].
    simpl in HnthR |- *.
    now apply nth_error_In in HnthR.
Qed.

Lemma endpoint_rectangles_axis_separated_sym : forall s t,
  endpoint_rectangles_axis_separated s t ->
  endpoint_rectangles_axis_separated t s.
Proof.
  intros s t Hsep. unfold endpoint_rectangles_axis_separated in *. tauto.
Qed.

Lemma same_boxes_preserve_axis_separation : forall old_s old_t new_s new_t,
  same_segment_box old_s new_s ->
  same_segment_box old_t new_t ->
  endpoint_rectangles_axis_separated old_s old_t ->
  endpoint_rectangles_axis_separated new_s new_t.
Proof.
  intros old_s old_t new_s new_t Hs Ht Hsep.
  unfold endpoint_rectangles_axis_separated in *.
  rewrite <- (same_segment_box_rect old_s new_s Hs).
  rewrite <- (same_segment_box_rect old_t new_t Ht).
  exact Hsep.
Qed.

(* sub のセグメントは端点が固定されるため、通常再接続版でも同じ
   端点長方形を持つ。 *)
Lemma ordinary_sub_member_same_box :
  forall l sub r h old ordinary,
    In old sub ->
    init ordinary = operate_point l sub r h (init old) ->
    term ordinary = operate_point l sub r h (term old) ->
    same_segment_box old ordinary.
Proof.
  intros l sub r h old ordinary Hold Hinit Hterm.
  unfold same_segment_box. split.
  - rewrite Hinit, operate_sub_endpoint; [reflexivity |].
    exists old. split; [exact Hold | now left].
  - rewrite Hterm, operate_sub_endpoint; [reflexivity |].
    exists old. split; [exact Hold | now right].
Qed.

(* 非隣接外部セグメントの通常再接続長方形は、sub のどの一セグメント
   の長方形とも軸方向に分離する。 *)
Lemma ordinary_nonadjacent_vs_sub_member_separated :
  forall l sub r h old outside inside,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    In old (nonadjacent_sides l r) ->
    In inside sub ->
    init outside = operate_point l sub r h (init old) ->
    term outside = operate_point l sub r h (term old) ->
    endpoint_rectangles_axis_separated outside inside.
Proof.
  intros l sub r h old outside inside Hsub Hconn Hmono Hh Hsparse Hwhole
    Hembedded Hext Hold Hinside Hinit Hterm.
  apply endpoint_box_separated_from_sub_separates_member
    with (sub := sub); try assumption.
  rewrite Hinit, Hterm.
  eapply operated_nonadjacent_endpoints_separated; eauto.
Qed.

(* 左右の接続境界を含まない場合は、外部同士・外部と sub・sub 同士の
   三種類だけであり、既存の端点順序保存と固定性から分離が従う。 *)
Lemma ordinary_nonboundary_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    ~ split_boundary_occurrence l sub r i old_s ->
    ~ split_boundary_occurrence l sub r j old_t ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar HnotS HnotT.
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h i old_s ordinary_s Hsub Hconn Hmono Hsparse
                Hwhole (ex_intro _ ds Hembed) Hrec HoldS HordinaryS)
    as [_ [HinitS HtermS]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j old_t ordinary_t Hsub Hconn Hmono Hsparse
                Hwhole (ex_intro _ ds Hembed) Hrec HoldT HordinaryT)
    as [_ [HinitT HtermT]].
  pose proof (split_occurrence_nonboundary
                l sub r i old_s
                (nth_error_split_occurrence l sub r i old_s HoldS) HnotS)
    as [HoutsideS | HinsideS];
  pose proof (split_occurrence_nonboundary
                l sub r j old_t
                (nth_error_split_occurrence l sub r j old_t HoldT) HnotT)
    as [HoutsideT | HinsideT].
  - pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) i j old_s old_t
                  Hsparse HoldS HoldT Hfar) as HoldSep.
    eapply (operated_endpoint_rectangles_axis_separated
              l sub r h i j old_s old_t ordinary_s ordinary_t
              Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hext
              (proj1 Hh) HoldS HoldT Hfar HinitS HtermS HinitT HtermT).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_s (init old_s) Hsparse HoutsideS (or_introl eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_s (term old_s) Hsparse HoutsideS (or_intror eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_t (init old_t) Hsparse HoutsideT (or_introl eq_refl)).
    + exact (nonadjacent_endpoint_not_on_sub
               l sub r old_t (term old_t) Hsparse HoutsideT (or_intror eq_refl)).
    + exact HoldSep.
  - eapply (same_boxes_preserve_axis_separation
              ordinary_s old_t ordinary_s ordinary_t).
    + split; reflexivity.
    + eapply ordinary_sub_member_same_box; eauto.
    + exact (ordinary_nonadjacent_vs_sub_member_separated
               l sub r h old_s ordinary_s old_t Hsub Hconn Hmono Hh Hsparse
               Hwhole (ex_intro _ ds Hembed) Hext HoutsideS HinsideT
               HinitS HtermS).
  - eapply (same_boxes_preserve_axis_separation
              old_s ordinary_t ordinary_s ordinary_t).
    + eapply ordinary_sub_member_same_box; eauto.
    + split; reflexivity.
    + apply endpoint_rectangles_axis_separated_sym.
      exact (ordinary_nonadjacent_vs_sub_member_separated
               l sub r h old_t ordinary_t old_s Hsub Hconn Hmono Hh Hsparse
               Hwhole (ex_intro _ ds Hembed) Hext HoutsideT HinsideS
               HinitT HtermT).
  - exact (same_boxes_preserve_axis_separation
             old_s old_t ordinary_s ordinary_t
             (ordinary_sub_member_same_box
                l sub r h old_s ordinary_s HinsideS HinitS HtermS)
             (ordinary_sub_member_same_box
                l sub r h old_t ordinary_t HinsideT HinitT HtermT)
             (sparse_far_rectangles_axis_separated
                (l ++ sub ++ r) i j old_s old_t
                Hsparse HoldS HoldT Hfar)).
Qed.

(* 非隣接出現の二端点について、上側の端点が sub 上でなければ、
   分類順序と正の移動量が元の厳密な上下順序を保存する。 *)
Lemma operate_preserves_far_endpoint_vertical_order :
  forall l sub r h i j s t ps pt,
    sub <> [] ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    (exists ds, embed_listDir ds (l ++ sub ++ r)) ->
    extensions_disjoint (l ++ sub ++ r) ->
    0 < h ->
    nth_error (l ++ sub ++ r) i = Some s ->
    nth_error (l ++ sub ++ r) j = Some t ->
    (S i < j \/ S j < i)%nat ->
    segment_x_ranges_overlap s t ->
    endpoint_of_seg s ps ->
    endpoint_of_seg t pt ->
    ~ onSegmentlist sub pt ->
    snd ps < snd pt ->
    snd (operate_point l sub r h ps) < snd (operate_point l sub r h pt).
Proof.
  intros l sub r h i j s t ps pt Hsub Hmono Hsparse Hembed Hext Hh
    Hs Ht Hfar Hoverlap Hps Hpt HptNotSub Hy.
  unfold operate_point.
  eapply shift_preserves_strict_vertical_order; [exact Hh | exact Hy |].
  exact (classified_nonadjacent_endpoint_order
           l sub r
           (classify_spec l sub r Hsub Hmono Hsparse Hembed Hext)
           i j s t ps pt Hs Ht Hfar Hoverlap Hps Hpt
           HptNotSub (Rlt_le _ _ Hy)).
Qed.

Lemma nth_error_sub_in_split : forall (l sub r : list Segment) k s,
  nth_error sub k = Some s ->
  nth_error (l ++ sub ++ r) (length l + k) = Some s.
Proof.
  intros l sub r k s Hnth.
  assert (Hk : (k < length sub)%nat) by now apply nth_error_lt in Hnth.
  rewrite app_assoc.
  rewrite nth_error_app1 by (rewrite length_app; lia).
  rewrite nth_error_app2 by lia.
  replace (length l + k - length l)%nat with k by lia.
  exact Hnth.
Qed.

Lemma nth_error_left_boundary_in_split : forall (l sub r : list Segment),
  l <> [] ->
  nth_error (l ++ sub ++ r) (length l - 1) = Some (last_segment l).
Proof.
  intros l sub r Hl.
  rewrite app_assoc.
  rewrite nth_error_app1.
  2: rewrite length_app; destruct l; [contradiction | simpl; lia].
  rewrite nth_error_app1 by (destruct l; [contradiction | simpl; lia]).
  unfold last_segment. now apply nth_error_last.
Qed.

Lemma nth_error_right_boundary_in_split : forall (l sub r : list Segment),
  r <> [] ->
  nth_error (l ++ sub ++ r) (length l + length sub) = Some (hd_segment r).
Proof.
  intros l sub r Hr.
  rewrite app_assoc.
  rewrite nth_error_app2 by (rewrite length_app; lia).
  rewrite length_app.
  replace (length l + length sub - (length l + length sub))%nat with 0%nat by lia.
  destruct r; [contradiction | reflexivity].
Qed.

(* 左接続セグメントの外側端点は、隣接時には [dc]、それ以外では
   closed sparse により sub 上へ戻れない。 *)
Lemma terminal_outer_endpoint_not_on_sub :
  forall ds l sub r,
    l <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    ~ onSegmentlist sub (init (last_segment l)).
Proof.
  intros ds l sub r Hl Hsparse Hembed [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  subst sub.
  assert (HtSub : nth_error (sl ++ t :: sr) (length sl) = Some t).
  { rewrite nth_error_app2 by lia.
    replace (length sl - length sl)%nat with 0%nat by lia. reflexivity. }
  assert (HtWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l + length sl) = Some t).
  { now apply nth_error_sub_in_split. }
  assert (HbWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l - 1) =
        Some (last_segment l)).
  { now apply nth_error_left_boundary_in_split. }
  destruct sl as [|a sl'].
  - simpl in HtWhole, HbWhole, Hembed, Hsparse, Hon.
    replace (length l + 0)%nat with (length l) in HtWhole by lia.
    assert (Hnext : S (length l - 1) = length l) by
      (destruct l; [contradiction | simpl; lia]).
    destruct Hembed as [sc [_ Hcurve]].
    destruct (embed_scurve_adjacent_data
                sc (l ++ (t :: sr) ++ r) (length l - 1)
                (last_segment l) t Hcurve HbWhole)
      as [psb [pst [HembB [HembT [Hdc Hjoin]]]]].
    { rewrite Hnext. exact HtWhole. }
    pose proof (adjacent_not_intersect_except_junction
                  psb pst (last_segment l) t (init (last_segment l))
                  Hdc HembB HembT Hjoin (onInit _) Hon) as Heq.
    exact (neq_init_term (last_segment l) Heq).
  - assert (Hfar : (S (length l - 1) < length l + length (a :: sl'))%nat).
    { destruct l; [contradiction | simpl; lia]. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ ((a :: sl') ++ t :: sr) ++ r)
                (length l + length (a :: sl')) (length l - 1)
                t (last_segment l) HtWhole HbWhole (or_intror Hfar))
      as [before [after [Hsplit Hin]]].
    pose proof (Hsparse before t after Hsplit) as [_ Hrect].
    eapply (Hrect (last_segment l) (init (last_segment l)) Hin).
    + apply segment_in_rect_or_endpoints, onInit.
    + change (in_segment_rect_or_endpoints t (init (last_segment l))).
      now apply segment_in_rect_or_endpoints.
Qed.

(* 右接続セグメントについての双対。 *)
Lemma initial_outer_endpoint_not_on_sub :
  forall ds l sub r,
    r <> [] ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    ~ onSegmentlist sub (term (hd_segment r)).
Proof.
  intros ds l sub r Hr Hsparse Hembed [t [Ht Hon]].
  destruct (in_app_app sub t Ht) as [sl [sr Hsub]].
  subst sub.
  assert (HtSub : nth_error (sl ++ t :: sr) (length sl) = Some t).
  { rewrite nth_error_app2 by lia.
    replace (length sl - length sl)%nat with 0%nat by lia. reflexivity. }
  assert (HtWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r) (length l + length sl) = Some t).
  { now apply nth_error_sub_in_split. }
  assert (HbWhole :
      nth_error (l ++ (sl ++ t :: sr) ++ r)
        (length l + length (sl ++ t :: sr)) = Some (hd_segment r)).
  { now apply nth_error_right_boundary_in_split. }
  destruct sr using rev_ind.
  - assert (Hnext :
        (S (length l + length sl) = length l + length (sl ++ [t]))%nat) by
      (rewrite length_app; simpl; lia).
    destruct Hembed as [sc [_ Hcurve]].
    destruct (embed_scurve_adjacent_data
                sc (l ++ (sl ++ [t]) ++ r) (length l + length sl)
                t (hd_segment r) Hcurve HtWhole)
      as [pst [psb [HembT [HembB [Hdc Hjoin]]]]].
    { rewrite Hnext. exact HbWhole. }
    pose proof (adjacent_not_intersect_except_junction
                  pst psb t (hd_segment r) (term (hd_segment r))
                  Hdc HembT HembB Hjoin Hon (onTerm _)) as Heq.
    apply (neq_init_term (hd_segment r)).
    rewrite <- Hjoin, <- Heq. reflexivity.
  - assert (Hfar :
        (S (length l + length sl) <
         length l + length (sl ++ t :: (sr ++ [x])))%nat).
    { rewrite (length_app sl (t :: (sr ++ [x]))).
      simpl. rewrite (length_app sr [x]). simpl. lia. }
    destruct (nth_error_far_in_nonadjacent_sides
                (l ++ (sl ++ t :: (sr ++ [x])) ++ r)
                (length l + length sl)
                (length l + length (sl ++ t :: (sr ++ [x])))
                t (hd_segment r) HtWhole HbWhole (or_introl Hfar))
      as [before [after [Hsplit Hin]]].
    pose proof (Hsparse before t after Hsplit) as [_ Hrect].
    eapply (Hrect (hd_segment r) (term (hd_segment r)) Hin).
    + apply segment_in_rect_or_endpoints, onTerm.
    + change (in_segment_rect_or_endpoints t (term (hd_segment r))).
      now apply segment_in_rect_or_endpoints.
Qed.

Lemma split_left_outer_in_nonadjacent : forall (l sub r : list Segment) i s,
  (i < length l - 1)%nat ->
  nth_error l i = Some s ->
  In s (nonadjacent_sides l r).
Proof.
  intros l sub r i s Hi Hnth.
  unfold nonadjacent_sides. rewrite in_app_iff. left.
  apply nth_error_In with (n := i).
  rewrite nth_error_removelast_before_last; [exact Hnth | lia].
Qed.

Lemma split_right_outer_in_nonadjacent : forall (l sub r : list Segment) k s,
  (0 < k)%nat ->
  nth_error r k = Some s ->
  In s (nonadjacent_sides l r).
Proof.
  intros l sub r k s Hk Hnth.
  unfold nonadjacent_sides. rewrite in_app_iff. right.
  destruct r as [|a r']; [destruct k; discriminate |].
  destruct k as [|k]; [lia |].
  simpl in Hnth |- *. now apply nth_error_In in Hnth.
Qed.

(* x 単調で連結な列では、先頭以外のセグメント始点は全体始点より右にある。 *)
Lemma x_monotone_nth_init_after_head : forall sub k s,
  connected sub ->
  x_monotone_segs sub ->
  nth_error sub k = Some s ->
  (0 < k)%nat ->
  fst (init (hd_segment sub)) < fst (init s).
Proof.
  induction sub as [|a tail IH]; intros k s Hconn Hmono Hnth Hk.
  { destruct k; discriminate. }
  destruct k as [|k]; [lia |].
  destruct tail as [|b tail']; [destruct k; discriminate |].
  simpl in Hnth.
  assert (Hab : term a = init b).
  { apply (Hconn 0%nat a b); reflexivity. }
  pose proof (Hmono a ltac:(now left)) as Ha.
  destruct k as [|k].
  - simpl in Hnth. injection Hnth as <-. simpl.
    change (fst (init a) < fst (term a)) in Ha.
    rewrite Hab in Ha. exact Ha.
  - assert (HconnTail : connected (b :: tail')).
    { intros n u v Hu Hv. apply (Hconn (S n) u v); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail')).
    { intros u Hu. apply Hmono. now right. }
    pose proof (IH (S k) s HconnTail HmonoTail Hnth ltac:(lia)) as Htail.
    simpl in Htail |- *.
    change (fst (init a) < fst (term a)) in Ha.
    rewrite Hab in Ha. lra.
Qed.

(* 末尾以外のセグメント終点は全体終点より左にある。 *)
Lemma x_monotone_nth_term_before_last : forall sub k s,
  connected sub ->
  x_monotone_segs sub ->
  nth_error sub k = Some s ->
  (k < length sub - 1)%nat ->
  fst (term s) < fst (term (last_segment sub)).
Proof.
  induction sub as [|a tail IH]; intros k s Hconn Hmono Hnth Hk.
  { destruct k; discriminate. }
  destruct tail as [|b tail']; [simpl in Hk; lia |].
  assert (Hab : term a = init b).
  { apply (Hconn 0%nat a b); reflexivity. }
  assert (HconnTail : connected (b :: tail')).
  { intros n u v Hu Hv. apply (Hconn (S n) u v); simpl; assumption. }
  assert (HmonoTail : x_monotone_segs (b :: tail')).
  { intros u Hu. apply Hmono. now right. }
  assert (Hlast : last_segment (a :: b :: tail') = last_segment (b :: tail')).
  { change (last_segment ([a] ++ b :: tail') = last_segment (b :: tail')).
    apply last_app_nonnil. discriminate. }
  destruct k as [|k].
  - simpl in Hnth. injection Hnth as <-. rewrite Hlast.
    pose proof (connected_x_monotone_endpoints
                  (b :: tail') ltac:(discriminate) HconnTail HmonoTail) as Htail.
    simpl in Htail. rewrite Hab. exact Htail.
  - simpl in Hnth. rewrite Hlast.
    apply (IH k s HconnTail HmonoTail Hnth).
    simpl in Hk |- *. lia.
Qed.

Lemma ordinary_terminal_boundary_far_rectangles_separated :
  forall ds l sub r h j other ordinary_b ordinary_o,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    l <> [] ->
    nth_error (l ++ sub ++ r) j = Some other ->
    nth_error (ordinary_reconnect_split l sub r h) (length l - 1) =
      Some ordinary_b ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_o ->
    (S (length l - 1) < j \/ S j < length l - 1)%nat ->
    ~ reconnect_split_lid_index l sub r (length l - 1) ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_b ordinary_o.
Proof.
  intros ds l sub r h j other ordinary_b ordinary_o
    Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
    Hother HordinaryB HordinaryO Hfar HnotLidB HnotLidO.
  set (b := last_segment l).
  assert (Hb : nth_error (l ++ sub ++ r) (length l - 1) = Some b).
  { unfold b. now apply nth_error_left_boundary_in_split. }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h (length l - 1) b ordinary_b
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hb HordinaryB) as [_ [HinitB HtermB]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j other ordinary_o
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hother HordinaryO) as [_ [HinitO HtermO]].
  assert (HnotTerminal : ~ terminal_lid l).
  { intro Hlid. apply HnotLidB. left. now split. }
  assert (HeastB : fst (init b) < fst (term b)).
  { destruct (total_order_T (fst (init b)) (fst (term b)))
      as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
    - exfalso. apply (neq_init_term_x b). exact Heq.
    - exfalso. apply HnotTerminal. split; [exact Hl | exact Hgt]. }
  assert (Htail : sub ++ r <> []).
  { destruct sub; [contradiction | discriminate]. }
  destruct (embed_listDir_app_boundary_data ds l (sub ++ r) Hl Htail Hembed)
    as [psb [pst [HembB [HembT [Hdc Hjoin0]]]]].
  assert (Hhd : hd_segment (sub ++ r) = hd_segment sub).
  { symmetry. unfold hd_segment. now apply hd_app. }
  assert (Hjoin : term b = init (hd_segment sub)).
  { unfold b. now rewrite <- Hhd. }
  assert (Hfixed : operate_point l sub r h (term b) = term b).
  { apply operate_sub_endpoint. rewrite Hjoin.
    exists (hd_segment sub). split.
    - destruct sub; [contradiction | now left].
    - now left. }
  assert (HouterNotSub : ~ onSegmentlist sub (init b)).
  { unfold b. eapply terminal_outer_endpoint_not_on_sub; eauto. }
  assert (Hexternal :
      forall k t t',
        nth_error (l ++ sub ++ r) k = Some t ->
        nth_error (ordinary_reconnect_split l sub r h) k = Some t' ->
        (S (length l - 1) < k \/ S k < length l - 1)%nat ->
        In t (nonadjacent_sides l r) ->
        endpoint_rectangles_axis_separated ordinary_b t').
  { intros k t t' Ht Ht' Hfar' Hin.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h k t t' Hsub Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec Ht Ht') as [_ [HinitT HtermT]].
    pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) (length l - 1) k b t
                  Hsparse Hb Ht Hfar') as Hsep.
    assert (HtInitNotSub : ~ onSegmentlist sub (init t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (init t) Hsparse Hin (or_introl eq_refl)). }
    assert (HtTermNotSub : ~ onSegmentlist sub (term t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (term t) Hsparse Hin (or_intror eq_refl)). }
    unfold endpoint_rectangles_axis_separated in Hsep |- *.
    destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [b]))) as [Hx | Hx].
    - left. change (Rmax (fst (init t')) (fst (term t')) <
                         Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
      change (Rmax (fst (init t)) (fst (term t)) <
              Rmin (fst (init b)) (fst (term b))) in Hx.
      rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx.
    - destruct (classic (rx1 (rect_of [b]) < rx0 (rect_of [t]))) as [Hx' | Hx'].
      + right; left.
        change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
                       Rmin (fst (init t')) (fst (term t'))).
        change (Rmax (fst (init b)) (fst (term b)) <
                Rmin (fst (init t)) (fst (term t))) in Hx'.
        rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx'.
      + assert (Hoverlap : segment_x_ranges_overlap b t).
        { unfold segment_x_ranges_overlap. apply conj; apply Rnot_lt_le; assumption. }
        destruct Hsep as [Hbad | [Hbad' | [HtBelow | HbBelow]]];
          try contradiction.
        * right; right; left.
          change (Rmax (snd (init t)) (snd (term t)) <
                  Rmin (snd (init b)) (snd (term b))) in HtBelow.
          change (Rmax (snd (init t')) (snd (term t')) <
                  Rmin (snd (init ordinary_b)) (snd (term ordinary_b))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfarRev : (S k < length l - 1 \/ S (length l - 1) < k)%nat)
            by tauto.
          assert (HoverlapRev : segment_x_ranges_overlap t b).
          { unfold segment_x_ranges_overlap in *. tauto. }
          assert (HtoOuter : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (init b))).
          { intros p Hp.
            assert (Hy : snd p < snd (init b)).
            { destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t)));
                pose proof (Rmin_l (snd (init b)) (snd (term b))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h k (length l - 1) t b p (init b)
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Ht Hb HfarRev HoverlapRev Hp
                     (or_introl eq_refl) HouterNotSub Hy). }
          assert (HtoFixed : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (term b))).
          { intros p Hp.
            assert (HpWhole : endpoint_of (l ++ sub ++ r) p).
            { exists t. split; [now apply nth_error_In in Ht | exact Hp]. }
            assert (HpBelow : snd p < ry0 (rect_of [b])).
            { change (snd p < Rmin (snd (init b)) (snd (term b))).
              destruct Hp as [-> | ->];
              pose proof (Rmax_l (snd (init t)) (snd (term t)));
              pose proof (Rmax_r (snd (init t)) (snd (term t))); lra. }
            pose proof (operated_endpoint_below_terminal_stays_below
                          l sub r h p Hsub Hmono Hsparse
                          (ex_intro _ ds Hembed) Hext (Rlt_le _ _ (proj1 Hh))
                          Hl HnotTerminal HpWhole HpBelow) as Hop.
            change (snd (operate_point l sub r h p) <
                    Rmin (snd (init b)) (snd (term b))) in Hop.
            rewrite Hfixed. eapply Rlt_le_trans; [exact Hop | apply Rmin_r]. }
          apply Rmax_lub_lt; apply Rmin_glb_lt.
          -- apply HtoOuter. now left.
          -- apply HtoFixed. now left.
          -- apply HtoOuter. now right.
          -- apply HtoFixed. now right.
        * right; right; right.
          change (Rmax (snd (init b)) (snd (term b)) <
                  Rmin (snd (init t)) (snd (term t))) in HbBelow.
          change (Rmax (snd (init ordinary_b)) (snd (term ordinary_b)) <
                  Rmin (snd (init t')) (snd (term t'))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfromBoundary : forall pb pt,
              endpoint_of_seg b pb -> endpoint_of_seg t pt ->
              snd (operate_point l sub r h pb) <
              snd (operate_point l sub r h pt)).
          { intros pb pt Hpb Hpt.
            assert (HptNotSub : ~ onSegmentlist sub pt).
            { destruct Hpt as [-> | ->]; assumption. }
            assert (Hy : snd pb < snd pt).
            { destruct Hpb as [-> | ->]; destruct Hpt as [-> | ->];
                pose proof (Rmax_l (snd (init b)) (snd (term b)));
                pose proof (Rmax_r (snd (init b)) (snd (term b)));
                pose proof (Rmin_l (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h (length l - 1) k b t pb pt
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Hb Ht Hfar' Hoverlap Hpb Hpt HptNotSub Hy). }
          apply Rmax_lub_lt; apply Rmin_glb_lt;
            apply HfromBoundary; [now left | now left | now left | now right |
                                  now right | now left | now right | now right]. }
  destruct (nth_error_split_occurrence l sub r j other Hother) as
    [Hleft HnthLeft | Hl' Hj -> | k Hks Hj HnthSub |
     Hr Hj -> | k Hk Hj HnthRight].
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_left_outer_in_nonadjacent with (i := j).
  - exfalso. subst j. lia.
  - assert (Hkpos : (0 < k)%nat) by (subst j; destruct Hfar; lia).
    assert (Hafter : fst (init (hd_segment sub)) < fst (init other)).
    { eapply x_monotone_nth_init_after_head; eauto. }
    right; left.
    change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
            Rmin (fst (init ordinary_o)) (fst (term ordinary_o))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (Hmono other (nth_error_In _ _ HnthSub)) as HeastO.
    change (fst (init other) < fst (term other)) in HeastO.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - assert (HnotInitial : ~ initial_lid r).
    { intro Hlid. apply HnotLidO. right. now split. }
    assert (HeastO : fst (init (hd_segment r)) < fst (term (hd_segment r))).
    { destruct (total_order_T
                  (fst (init (hd_segment r))) (fst (term (hd_segment r))))
        as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
      - exfalso. apply (neq_init_term_x (hd_segment r)). exact Heq.
      - exfalso. apply HnotInitial. split; assumption. }
    assert (Hprefix : l ++ sub <> []).
    { intro Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
    assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
    { rewrite <- app_assoc. exact Hembed. }
    destruct (embed_listDir_app_boundary_data ds (l ++ sub) r Hprefix Hr Hembed')
      as [pss [psr [HembS [HembR [HdcR HjoinR0]]]]].
    assert (Hlast : last_segment (l ++ sub) = last_segment sub).
    { now apply last_app_nonnil. }
    assert (HjoinR : term (last_segment sub) = init (hd_segment r)).
    { now rewrite <- Hlast. }
    pose proof (connected_x_monotone_endpoints sub Hsub Hconn Hmono) as HsubX.
    right; left.
    change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
            Rmin (fst (init ordinary_o)) (fst (term ordinary_o))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (f_equal fst Hjoin) as HjoinX.
    pose proof (f_equal fst HjoinR) as HjoinRX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_right_outer_in_nonadjacent with (k := k).
Qed.

Lemma ordinary_initial_boundary_far_rectangles_separated :
  forall ds l sub r h j other ordinary_b ordinary_o,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    r <> [] ->
    nth_error (l ++ sub ++ r) j = Some other ->
    nth_error (ordinary_reconnect_split l sub r h)
      (length l + length sub) = Some ordinary_b ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_o ->
    (S (length l + length sub) < j
     \/ S j < length l + length sub)%nat ->
    ~ reconnect_split_lid_index l sub r (length l + length sub) ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_b ordinary_o.
Proof.
  intros ds l sub r h j other ordinary_b ordinary_o
    Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
    Hother HordinaryB HordinaryO Hfar HnotLidB HnotLidO.
  set (b := hd_segment r).
  assert (Hb :
      nth_error (l ++ sub ++ r) (length l + length sub) = Some b).
  { unfold b. now apply nth_error_right_boundary_in_split. }
  assert (Hwhole : connected (l ++ sub ++ r)).
  { exact (embed_listDir_connected ds (l ++ sub ++ r) Hembed). }
  assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
  { eapply operate_endpoints_reconnectable; eauto. }
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h (length l + length sub) b ordinary_b
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hb HordinaryB) as [_ [HinitB HtermB]].
  pose proof (ordinary_reconnect_split_nth_spec
                l sub r h j other ordinary_o
                Hsub Hconn Hmono Hsparse Hwhole (ex_intro _ ds Hembed) Hrec
                Hother HordinaryO) as [_ [HinitO HtermO]].
  assert (HnotInitial : ~ initial_lid r).
  { intro Hlid. apply HnotLidB. right. now split. }
  assert (HeastB : fst (init b) < fst (term b)).
  { destruct (total_order_T (fst (init b)) (fst (term b)))
      as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
    - exfalso. apply (neq_init_term_x b). exact Heq.
    - exfalso. apply HnotInitial. split; [exact Hr | exact Hgt]. }
  assert (Hprefix : l ++ sub <> []).
  { intro Hnil. apply app_eq_nil in Hnil as [_ Hnil]. contradiction. }
  assert (Hembed' : embed_listDir ds ((l ++ sub) ++ r)).
  { rewrite <- app_assoc. exact Hembed. }
  destruct (embed_listDir_app_boundary_data ds (l ++ sub) r Hprefix Hr Hembed')
    as [pst [psb [HembT [HembB [Hdc Hjoin0]]]]].
  assert (Hlast : last_segment (l ++ sub) = last_segment sub).
  { now apply last_app_nonnil. }
  assert (Hjoin : term (last_segment sub) = init b).
  { unfold b. now rewrite <- Hlast. }
  assert (Hfixed : operate_point l sub r h (init b) = init b).
  { apply operate_sub_endpoint. rewrite <- Hjoin.
    exists (last_segment sub). split.
    - apply last_In. exact Hsub.
    - now right. }
  assert (HouterNotSub : ~ onSegmentlist sub (term b)).
  { unfold b. eapply initial_outer_endpoint_not_on_sub; eauto. }
  assert (Hexternal :
      forall k t t',
        nth_error (l ++ sub ++ r) k = Some t ->
        nth_error (ordinary_reconnect_split l sub r h) k = Some t' ->
        (S (length l + length sub) < k
         \/ S k < length l + length sub)%nat ->
        In t (nonadjacent_sides l r) ->
        endpoint_rectangles_axis_separated ordinary_b t').
  { intros k t t' Ht Ht' Hfar' Hin.
    pose proof (ordinary_reconnect_split_nth_spec
                  l sub r h k t t' Hsub Hconn Hmono Hsparse Hwhole
                  (ex_intro _ ds Hembed) Hrec Ht Ht') as [_ [HinitT HtermT]].
    pose proof (sparse_far_rectangles_axis_separated
                  (l ++ sub ++ r) (length l + length sub) k b t
                  Hsparse Hb Ht Hfar') as Hsep.
    assert (HtInitNotSub : ~ onSegmentlist sub (init t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (init t) Hsparse Hin (or_introl eq_refl)). }
    assert (HtTermNotSub : ~ onSegmentlist sub (term t)).
    { exact (nonadjacent_endpoint_not_on_sub
               l sub r t (term t) Hsparse Hin (or_intror eq_refl)). }
    unfold endpoint_rectangles_axis_separated in Hsep |- *.
    destruct (classic (rx1 (rect_of [t]) < rx0 (rect_of [b]))) as [Hx | Hx].
    - left. change (Rmax (fst (init t')) (fst (term t')) <
                         Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
      change (Rmax (fst (init t)) (fst (term t)) <
              Rmin (fst (init b)) (fst (term b))) in Hx.
      rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx.
    - destruct (classic (rx1 (rect_of [b]) < rx0 (rect_of [t]))) as [Hx' | Hx'].
      + right; left.
        change (Rmax (fst (init ordinary_b)) (fst (term ordinary_b)) <
                       Rmin (fst (init t')) (fst (term t'))).
        change (Rmax (fst (init b)) (fst (term b)) <
                Rmin (fst (init t)) (fst (term t))) in Hx'.
        rewrite HinitB, HtermB, HinitT, HtermT, !operate_point_fst. exact Hx'.
      + assert (Hoverlap : segment_x_ranges_overlap b t).
        { unfold segment_x_ranges_overlap. apply conj; apply Rnot_lt_le; assumption. }
        destruct Hsep as [Hbad | [Hbad' | [HtBelow | HbBelow]]];
          try contradiction.
        * right; right; left.
          change (Rmax (snd (init t)) (snd (term t)) <
                  Rmin (snd (init b)) (snd (term b))) in HtBelow.
          change (Rmax (snd (init t')) (snd (term t')) <
                  Rmin (snd (init ordinary_b)) (snd (term ordinary_b))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfarRev :
              (S k < length l + length sub
               \/ S (length l + length sub) < k)%nat) by tauto.
          assert (HoverlapRev : segment_x_ranges_overlap t b).
          { unfold segment_x_ranges_overlap in *. tauto. }
          assert (HtoOuter : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (term b))).
          { intros p Hp.
            assert (Hy : snd p < snd (term b)).
            { destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init b)) (snd (term b))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h k (length l + length sub) t b p (term b)
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Ht Hb HfarRev HoverlapRev Hp
                     (or_intror eq_refl) HouterNotSub Hy). }
          assert (HtoFixed : forall p,
              endpoint_of_seg t p ->
              snd (operate_point l sub r h p) <
              snd (operate_point l sub r h (init b))).
          { intros p Hp.
            assert (HpWhole : endpoint_of (l ++ sub ++ r) p).
            { exists t. split; [now apply nth_error_In in Ht | exact Hp]. }
            assert (HpBelow : snd p < ry0 (rect_of [b])).
            { change (snd p < Rmin (snd (init b)) (snd (term b))).
              destruct Hp as [-> | ->];
                pose proof (Rmax_l (snd (init t)) (snd (term t)));
                pose proof (Rmax_r (snd (init t)) (snd (term t))); lra. }
            pose proof (operated_endpoint_below_initial_stays_below
                          l sub r h p Hsub Hmono Hsparse
                          (ex_intro _ ds Hembed) Hext (Rlt_le _ _ (proj1 Hh))
                          Hr HnotInitial HpWhole HpBelow) as Hop.
            change (snd (operate_point l sub r h p) <
                    Rmin (snd (init b)) (snd (term b))) in Hop.
            rewrite Hfixed. eapply Rlt_le_trans; [exact Hop | apply Rmin_l]. }
          apply Rmax_lub_lt; apply Rmin_glb_lt.
          -- apply HtoFixed. now left.
          -- apply HtoOuter. now left.
          -- apply HtoFixed. now right.
          -- apply HtoOuter. now right.
        * right; right; right.
          change (Rmax (snd (init b)) (snd (term b)) <
                  Rmin (snd (init t)) (snd (term t))) in HbBelow.
          change (Rmax (snd (init ordinary_b)) (snd (term ordinary_b)) <
                  Rmin (snd (init t')) (snd (term t'))).
          rewrite HinitB, HtermB, HinitT, HtermT.
          assert (HfromBoundary : forall pb pt,
              endpoint_of_seg b pb -> endpoint_of_seg t pt ->
              snd (operate_point l sub r h pb) <
              snd (operate_point l sub r h pt)).
          { intros pb pt Hpb Hpt.
            assert (HptNotSub : ~ onSegmentlist sub pt).
            { destruct Hpt as [-> | ->]; assumption. }
            assert (Hy : snd pb < snd pt).
            { destruct Hpb as [-> | ->]; destruct Hpt as [-> | ->];
                pose proof (Rmax_l (snd (init b)) (snd (term b)));
                pose proof (Rmax_r (snd (init b)) (snd (term b)));
                pose proof (Rmin_l (snd (init t)) (snd (term t)));
                pose proof (Rmin_r (snd (init t)) (snd (term t))); lra. }
            exact (operate_preserves_far_endpoint_vertical_order
                     l sub r h (length l + length sub) k b t pb pt
                     Hsub Hmono Hsparse (ex_intro _ ds Hembed) Hext
                     (proj1 Hh) Hb Ht Hfar' Hoverlap Hpb Hpt HptNotSub Hy). }
          apply Rmax_lub_lt; apply Rmin_glb_lt;
            apply HfromBoundary; [now left | now left | now left | now right |
                                  now right | now left | now right | now right]. }
  destruct (nth_error_split_occurrence l sub r j other Hother) as
    [Hleft HnthLeft | Hl Hj -> | k Hks Hj HnthSub |
     Hr' Hj -> | k Hk Hj HnthRight].
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_left_outer_in_nonadjacent with (i := j).
  - assert (HnotTerminal : ~ terminal_lid l).
    { intro Hlid. apply HnotLidO. left. now split. }
    assert (HeastO : fst (init (last_segment l)) < fst (term (last_segment l))).
    { destruct (total_order_T
                  (fst (init (last_segment l))) (fst (term (last_segment l))))
        as [[Hlt | Heq] | Hgt]; [exact Hlt | |].
      - exfalso. apply (neq_init_term_x (last_segment l)). exact Heq.
      - exfalso. apply HnotTerminal. split; assumption. }
    assert (Htail : sub ++ r <> []).
    { destruct sub; [contradiction | discriminate]. }
    destruct (embed_listDir_app_boundary_data ds l (sub ++ r) Hl Htail Hembed)
      as [psl [pss [HembL [HembS [HdcL HjoinL0]]]]].
    assert (Hhd : hd_segment (sub ++ r) = hd_segment sub).
    { symmetry. unfold hd_segment. now apply hd_app. }
    assert (HjoinL : term (last_segment l) = init (hd_segment sub)).
    { now rewrite <- Hhd. }
    pose proof (connected_x_monotone_endpoints sub Hsub Hconn Hmono) as HsubX.
    left.
    change (Rmax (fst (init ordinary_o)) (fst (term ordinary_o)) <
            Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (f_equal fst HjoinL) as HjoinLX.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - assert (HkBefore : (k < length sub - 1)%nat).
    { subst j. destruct Hfar; lia. }
    assert (Hbefore : fst (term other) < fst (term (last_segment sub))).
    { eapply x_monotone_nth_term_before_last; eauto. }
    left.
    change (Rmax (fst (init ordinary_o)) (fst (term ordinary_o)) <
            Rmin (fst (init ordinary_b)) (fst (term ordinary_b))).
    rewrite HinitB, HtermB, HinitO, HtermO, !operate_point_fst.
    pose proof (Hmono other (nth_error_In _ _ HnthSub)) as HeastO.
    change (fst (init other) < fst (term other)) in HeastO.
    pose proof (f_equal fst Hjoin) as HjoinX.
    rewrite Rmax_right, Rmin_left by lra. lra.
  - exfalso. subst j. lia.
  - apply (Hexternal j other ordinary_o Hother HordinaryO Hfar).
    now apply split_right_outer_in_nonadjacent with (k := k).
Qed.

(* 残る本質的な枝：sub に隣接する非蓋セグメントと、二つ以上離れた
   出現との垂直分離を、固定接続点を含めて保存する。 *)
Lemma ordinary_boundary_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    (split_boundary_occurrence l sub r i old_s
     \/ split_boundary_occurrence l sub r j old_t) ->
    ~ reconnect_split_lid_index l sub r i ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar Hboundary HnotLidS HnotLidT.
  destruct Hboundary as [HboundaryS | HboundaryT].
  - destruct HboundaryS as [[Hl [Hi Hs]] | [Hr [Hi Hs]]].
    + subst i old_s.
      exact (ordinary_terminal_boundary_far_rectangles_separated
               ds l sub r h j old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
               HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT).
    + subst i old_s.
      exact (ordinary_initial_boundary_far_rectangles_separated
               ds l sub r h j old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
               HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT).
  - apply endpoint_rectangles_axis_separated_sym.
    destruct HboundaryT as [[Hl [Hj Ht]] | [Hr [Hj Ht]]].
    + subst j old_t.
      exact (ordinary_terminal_boundary_far_rectangles_separated
               ds l sub r h i old_s ordinary_t ordinary_s
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hl
               HoldS HordinaryT HordinaryS ltac:(tauto) HnotLidT HnotLidS).
    + subst j old_t.
      exact (ordinary_initial_boundary_far_rectangles_separated
               ds l sub r h i old_s ordinary_t ordinary_s
               Hsub Hconn Hmono Hh Hsparse Hembed Hext Hr
               HoldS HordinaryT HordinaryS ltac:(tauto) HnotLidT HnotLidS).
Qed.

(* 蓋でない二出現では、元の sparse な長方形分離を端点操作後へ運ぶ。
   水平分離、sub 内、sub 隣接境界、外部端点の各場合分けをここに集約する。 *)
Lemma ordinary_nonlid_far_rectangles_separated :
  forall ds l sub r h i j old_s old_t ordinary_s ordinary_t,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nth_error (l ++ sub ++ r) i = Some old_s ->
    nth_error (l ++ sub ++ r) j = Some old_t ->
    nth_error (ordinary_reconnect_split l sub r h) i = Some ordinary_s ->
    nth_error (ordinary_reconnect_split l sub r h) j = Some ordinary_t ->
    (S i < j \/ S j < i)%nat ->
    ~ reconnect_split_lid_index l sub r i ->
    ~ reconnect_split_lid_index l sub r j ->
    endpoint_rectangles_axis_separated ordinary_s ordinary_t.
Proof.
  intros ds l sub r h i j old_s old_t ordinary_s ordinary_t
    Hsub Hconn Hmono Hh Hsparse Hembed Hext
    HoldS HoldT HordinaryS HordinaryT Hfar HnotLidS HnotLidT.
  destruct (classic (split_boundary_occurrence l sub r i old_s))
    as [HboundaryS | HboundaryS].
  - exact (ordinary_boundary_far_rectangles_separated
             ds l sub r h i j old_s old_t ordinary_s ordinary_t
             Hsub Hconn Hmono Hh Hsparse Hembed Hext
             HoldS HoldT HordinaryS HordinaryT Hfar
             (or_introl HboundaryS) HnotLidS HnotLidT).
  - destruct (classic (split_boundary_occurrence l sub r j old_t))
      as [HboundaryT | HboundaryT].
    + exact (ordinary_boundary_far_rectangles_separated
               ds l sub r h i j old_s old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext
               HoldS HoldT HordinaryS HordinaryT Hfar
               (or_intror HboundaryT) HnotLidS HnotLidT).
    + exact (ordinary_nonboundary_far_rectangles_separated
               ds l sub r h i j old_s old_t ordinary_s ordinary_t
               Hsub Hconn Hmono Hh Hsparse Hembed Hext
               HoldS HoldT HordinaryS HordinaryT Hfar
               HboundaryS HboundaryT).
Qed.

(* 戻る蓋は safe reconnect の blocker 回避、通常セグメントは分類順序を
   用いて処理する。全域の長方形 sparse ではなく曲線本体だけを排除する。 *)
Lemma reconnect_split_nonadjacent_bodies_disjoint :
  forall ds l sub r h,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    nonadjacent_bodies_disjoint (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hsub Hconn Hmono Hh Hsparse Hembed Hext.
  unfold nonadjacent_bodies_disjoint.
  intros i j s t p Hs Ht Hfar Hsp Htp.
  destruct (classic (reconnect_split_lid_index l sub r i)) as [Hi | Hi].
  - destruct Hi as [[Hlid Hi] | [Hlid Hi]].
    + eapply reconnect_split_terminal_lid_avoids_far_body; eauto.
    + eapply reconnect_split_initial_lid_avoids_far_body; eauto.
  - destruct (classic (reconnect_split_lid_index l sub r j)) as [Hj | Hj].
    + destruct Hj as [[Hlid Hj] | [Hlid Hj]].
      * eapply (reconnect_split_terminal_lid_avoids_far_body
                  ds l sub r h j i t s p); eauto; lia.
      * eapply (reconnect_split_initial_lid_avoids_far_body
                  ds l sub r h j i t s p); eauto; lia.
    + destruct (reconnect_split_nth_witnesses l sub r h i s Hs)
        as [old_s [ordinary_s [Hold_s Hordinary_s]]].
      destruct (reconnect_split_nth_witnesses l sub r h j t Ht)
        as [old_t [ordinary_t [Hold_t Hordinary_t]]].
      assert (Hsafe_s : s = ordinary_s).
      { exact (reconnect_split_nth_eq_ordinary_unless_lid
                 l sub r h i ordinary_s s Hi Hordinary_s Hs). }
      assert (Hsafe_t : t = ordinary_t).
      { exact (reconnect_split_nth_eq_ordinary_unless_lid
                 l sub r h j ordinary_t t Hj Hordinary_t Ht). }
      subst s t.
      pose proof (ordinary_nonlid_far_rectangles_separated
                    ds l sub r h i j old_s old_t ordinary_s ordinary_t
                    Hsub Hconn Hmono Hh Hsparse Hembed Hext
                    Hold_s Hold_t Hordinary_s Hordinary_t Hfar Hi Hj)
        as Hseparated.
      apply (axis_separated_boxes_avoid
               ordinary_s ordinary_t Hseparated p).
      * now apply segment_in_rect_or_endpoints.
      * now apply segment_in_rect_or_endpoints.
Qed.

(* 具体的な再接続列について、本体・延長線の三種類の衝突を排除して
   開性を得る。初期 sparse 性は各衝突証明書を作る前段でのみ使う。 *)
Lemma reconnect_preserves_open :
  forall l sub r h,
    sub <> [] ->
    positive_bodies_disjoint (reconnect_split l sub r h) ->
    extensions_avoid_positive_bodies (reconnect_split l sub r h) ->
    extensions_disjoint (reconnect_split l sub r h) ->
    ~ close (reconnect_split l sub r h).
Proof.
  intros l sub r h Hsub Hbody Hextbody Hext.
  apply separated_bodies_extensions_open; try assumption.
  intros Hnil.
  unfold reconnect_split in Hnil.
  apply app_eq_nil in Hnil as [_ Hsubr].
  apply app_eq_nil in Hsubr as [Hsubnil _].
  now apply Hsub.
Qed.

(* 再接続後に残す不変量は、sub 周りの局所 sparse 性と開性だけである。 *)
Lemma reconnect_gives_sparse_around_and_open :
  forall ds l sub r h,
    connected (l ++ sub ++ r) ->
    well_split l sub r ->
    h_large h sub ->
    sparse_embedding (l ++ sub ++ r) ->
    embed_listDir ds (l ++ sub ++ r) ->
    extensions_disjoint (l ++ sub ++ r) ->
    sparse_around
      (reconnect_left l sub r h)
      sub
      (reconnect_right l sub r h)
    /\ ~ close (reconnect_split l sub r h).
Proof.
  intros ds l sub r h Hwhole Hws Hh Hsparse Hembed Hext.
  destruct Hws as [Hne [Hmono HsubOpen]].
  assert (Hconn : connected sub).
  { eapply connected_middle. exact Hwhole. }
  split.
  - apply (reconnect_gives_safe_sparse_around
             ds l sub r h Hwhole).
    + repeat split; assumption.
    + exact Hh.
    + exact Hsparse.
    + exact Hembed.
    + exact Hext.
  - assert (Hrec : all_reconnectable l sub r h (l ++ sub ++ r)).
    { exact (operate_endpoints_reconnectable
               l sub r h Hne Hconn Hmono Hh Hsparse Hwhole
               (ex_intro _ ds Hembed) Hext). }
    assert (HsafeEmbed : embed_listDir ds (reconnect_split l sub r h)).
    { eapply reconnect_split_safe_preserves_embed; eauto. }
    assert (Hfar : nonadjacent_bodies_disjoint (reconnect_split l sub r h)).
    { eapply reconnect_split_nonadjacent_bodies_disjoint; eauto. }
    apply (separated_reconnected_curve_open
             ds (reconnect_split l sub r h)).
    + intro Hnil.
      unfold reconnect_split in Hnil.
      apply app_eq_nil in Hnil as [_ Htail].
      apply app_eq_nil in Htail as [Hsub _].
      contradiction.
    + exact HsafeEmbed.
    + exact Hfar.
    + eapply reconnect_split_extensions_avoid_positive_bodies; eauto.
    + eapply reconnect_split_extensions_disjoint; eauto.
Qed.
