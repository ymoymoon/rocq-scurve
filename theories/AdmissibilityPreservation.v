Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.


Parameter default_primitive_segment : PrimitiveSegment.
Parameter slope_init : Segment -> R. (* 傾きを想定しているが，埋め込みの延長線を一意に定義するものであればよい？ *)
Parameter slope_term : Segment -> R.

(* list Segment を使用する際は，embed_scurve によって何かしらの埋め込みであることを確認する．
		そうでない場合，リスト内の全セグメントが連結していることを確認しなければならない．
		この先「２次元曲線」のような定義を作成した場合，定義の変更とともにこのコメントは削除する． *)

Definition embed_listDir (ld: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ld
	/\ embed_scurve sc ls.

(* TODO: 空リストは含まない．（含めるなら，後の定理の必要な部分に not nil 制約を入れる．）繋がっていることも保証． *)
Parameter is_one_way_embedding : list Segment -> Prop
(* Embed.all_same_h 使えそう *).
Definition one_way_embedding := {ls : list Segment | is_one_way_embedding ls}.

(* 単方向 scurve *)
Definition is_one_way_scurve (sc : scurve) : Prop :=
	exists ls, embed_scurve sc ls /\ is_one_way_embedding ls.
Definition is_one_way_listDir (ld: list Direction) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ld /\ is_one_way_scurve sc.
(* おそらく帰納的に定義することもできる．後者は回転数２以下と同値？
		必要があれば証明 *)

(* 単方向曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition in_rect_from_diagonal a b rr := rectangular_from_diagonal a b rr.
Definition in_rect (ls: one_way_embedding) rr := 
	in_rect_from_diagonal (init (hd default_segment (proj1_sig ls))) (term (last (proj1_sig ls) default_segment)) rr.

(* 疎：単方向曲線 sub_ls の周囲に全然関係ないセグメントが侵入してこない *)
Definition is_sparse_embedding (sc : scurve) (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists l r, ls = l ++ (proj1_sig sub_ls) ++ r
	/\ embed_scurve sc ls
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.
		(* 下のコメントは，その後曲線を移動させて矩形の縦長横長を操る（ことで端点が絡んでも簡約して端の傾きを保存できるようにする）ことが想定されている．
				人工的かつそのあと曲線の移動が挟まるはずなので，ここで定義を複雑にするより，他の Lemma でうまいことしたい． *)
		(* /\ (l = [] -> (* sub_ls が端点を含む場合，延長線上にも関係ないセグメントが近づかないことを要請 *)
				let X1 := head_seg sub_ls default_segment in 
				let width := (term_x X1) - (init_x X1) in (* 矩形の横幅 *)
				let length := (term_y X1) - (init_y X1) in (* 矩形の縦幅 *)
				forall p, onHeadSegment X1 p -> 
					let rect := rectangular_from_diagonal ((fst p)-width, (snd p)-length) p in (* 矩形 *)
					forall q, 
					(exists seg, onExtendSegment ls seg q /\ ~ onHeadSegment X1 q) 
					-> ~ rect q) *)

Definition sparse (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists sc, is_sparse_embedding sc sub_ls ls.

Definition is_sparse_embedding_listDir (ld: list Direction) (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists sc, scurve_to_direction sc = ld
	/\ is_sparse_embedding sc sub_ls ls.



Lemma P_is_oneway : is_one_way_listDir [Plus].
Proof. (* ここは one_way_listDir の定義さえできれば示せる？ *)
Admitted.

Lemma embedding_P_is_oneway : forall seg, 
	embed_listDir [Plus] [seg] -> is_one_way_embedding [seg].
Proof.
Admitted.

Lemma PMP_is_oneway : is_one_way_listDir [Plus; Minus; Plus].
Proof.
Admitted.

Lemma embedding_one_to_one_listDir : forall d ls, 
	embed_listDir [d] ls -> exists seg, ls = [seg].
Proof. Admitted.

Lemma divide_embedding_listDir : forall ld1 ld2 ls,
	embed_listDir (ld1 ++ ld2) ls
	-> exists ls1 ls2, ls = ls1 ++ ls2 (* ここから init ls2 = term ls1 のようなことは導けるはず *)
	/\ embed_listDir ld1 ls1
	/\ embed_listDir ld2 ls2.
Proof. Admitted.

(* 許容可能ならば，その中の単方向な sub_ds 周りで疎な開埋め込みが存在する．
 		さらに sub_ls の始点と終点とそれぞれでの傾きを（sub_ls の向きを考慮した上で）自由に選んでも良い，
		としたらのちに端点での傾きを保存するために役立つ？ *)
Lemma embed_sparsely (dl dr : list Direction) (sub_ds : list Direction) :
	AdmissibleDirs (dl ++ sub_ds ++ dr)
	-> is_one_way_listDir sub_ds
	-> exists l r sub_ls, 
		embed_listDir (dl ++ sub_ds ++ dr) (l ++ (proj1_sig sub_ls) ++ r)
		/\ ~ close (l ++ (proj1_sig sub_ls) ++ r)
		/\ sparse sub_ls (l ++ (proj1_sig sub_ls) ++ r).
Proof. Admitted.

(* 矩形の中にピッタリ収まる1つのセグメントが描ける．端点での傾きは保存されない *)
Lemma embed_in_rectangle : forall (ls : one_way_embedding) (d: Direction), 
	exists seg : Segment, 
		(exists p: PrimitiveSegment, embed p seg /\ orn p = d)
		/\ (forall rr, onSegment seg rr -> in_rect ls rr) 
		/\ init seg = init (hd default_segment (proj1_sig ls)) 
		/\ term seg = term (last (proj1_sig ls) default_segment).
Proof. Admitted.

(* 端点を含まない sub_ls の周りが疎な開埋め込みにおいて，sub_ls をその領域に収まるセグメント列に置き換えても開のまま *)
(* TODO: 端点で傾きが保存できていたら，端点を含む場合でも成立するはず *)
Lemma seg_in_rectangle_keep_openness : forall sub_ls l ls r rs seg,
	~ close ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> sparse sub_ls ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> (forall rr, onSegment seg rr -> in_rect sub_ls rr) 
		/\ init seg = init (hd default_segment (proj1_sig sub_ls)) 
		/\ term seg = term (last (proj1_sig sub_ls) default_segment)
	-> ~ close ((l :: ls) ++ [seg] ++ (r :: rs)).
Proof. Admitted.


(* [+-+ => +] での簡約で，簡約元が許容可能なら簡約先も許容可能 *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	intros l r admds. destruct l as [ | l' l].
	- (* 端点を含む簡約 *) admit.
	- destruct r as [ | r' r].
		+ (* 端点を含む簡約 *) admit.
		+ (* 簡約にかかわった部分の両端に別のセグメントが存在する場合 *)
			unfold AdmissibleDirs. intros ps Hps. unfold admissible.
			pose proof PMP_is_oneway as PMP_is_oneway.
			apply (embed_sparsely _ _ _ admds) in PMP_is_oneway as 
				[lsl [lsr [sub_ls [Hl [Hr [HPMP [Hopen Hsparse]]]]]]].
			destruct (embed_in_rectangle sub_ls Plus) as 
				[seg [[p [embed_p qrn_p]] [Hin_rect [Hinit Hterm]]]].
			exists (lsl ++ [seg] ++ lsr). split.
			* (* 簡約後の向き列の埋め込みになっていること *) admit.
			* (* その埋め込みが開であること *) admit.
			(* apply seg_in_rectangle_keep_openness. *)
Admitted.

(* Plus (の向きを持つ Primitive Segment) の埋め込みを，[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる
	TODO：端点での傾きも保存できること．また，もっと一般的に *)
Lemma P_to_PMP : forall (seg : Segment) (H: embed_listDir [Plus] [seg]),
	exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		/\ (forall rr, (onSegment seg1 rr \/ onSegment seg2 rr \/ onSegment seg3 rr)
				-> in_rect (exist _ [seg] (embedding_P_is_oneway seg H)) rr) (* seg が張る矩形の内部で分割できている *)
		/\ init seg1 = init seg
		/\ term seg3 = term seg.
Proof. Admitted.


(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
	unfold AdmissibleDirs. unfold admissible. intros l r admds sc Hsc.
	assert (H: exists ps, hd default_primitive_segment (proj1_sig ps) = hd default_primitive_segment (proj1_sig sc) 
	/\ scurve_to_direction ps = l ++ [Plus] ++ r). {
		admit. (* sc と同じ X1 を持ち，簡約部分で２つの PSeg が取れた scurve *)
	}
	destruct H as [ps [Htl Hps]]. specialize admds with ps. 
	pose proof (admds Hps) as [ls' [Hembed Hopen]]; clear admds.
	assert (H: embed_listDir (l ++ [Plus] ++ r) ls'). {
		unfold embed_listDir. exists ps. split; assumption.
	}
	apply divide_embedding_listDir in H as [ls1 [ls2' [Hls' [Hls1 Hls2']]]].
	apply divide_embedding_listDir in Hls2' as [ls2 [ls3 [Hls2' [Hls2 Hls3]]]].
	pose proof (embedding_one_to_one_listDir Plus ls2 Hls2) as [segP HP]; subst.
	pose proof (P_to_PMP segP Hls2) as [seg1 [seg2 [seg3 [HPMP [Hin_rect [Hinit Hterm]]]]]].
	exists (ls1 ++ [seg1; seg2; seg3] ++ ls3). (* 欲しかった埋め込み *) 
	split.
	- (* 埋め込みになっていること *) (* 頑張れば行けそう *) admit.
	- (* その埋め込みが開であること *) 
	(* 端点を含んでいなければ apply seg_in_rectangle_keep_openness. *)
Admitted.

