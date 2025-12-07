Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.


(* scurve に直してから埋め込む．そうしないなら，連結していない Seg 列を省けるように． *)
Definition embed_listDir (ld: list Direction) (ls: list Segment) : Prop :=
	exists sc: scurve, scurve_to_direction sc = ld
	/\ embed_scurve sc ls.

(* TODO: 空リストは含まない．含めるなら，後の定理の必要な部分に not nil 制約を入れる *)
Parameter is_one_way_embedding : list Segment -> Prop
(* Embed.all_same_h 使えそう *).
Definition one_way_embedding := {ls : list Segment | is_one_way_embedding ls}.

(* 単方向 scurve *)
Definition one_way_scurve (sc : scurve) : Prop :=
	exists ls, embed_scurve sc ls /\ is_one_way_embedding ls.
Definition one_way_listDir (ld: list Direction) : Prop :=
	exists ls, embed_listDir ld ls /\ is_one_way_embedding ls.

(* 単方向曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition rectangular_region (ls : one_way_embedding) : (R * R -> Prop) :=
	rectangular_from_diagonal (init (hd default_segment (proj1_sig ls))) (term (last (proj1_sig ls) default_segment)).
Definition in_rect ls rr := rectangular_region ls rr.

(* 疎：単方向曲線 sub_ls の周囲に全然関係ないセグメントが侵入してこない *)
Definition sparse (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	exists l r, ls = l ++ (proj1_sig sub_ls) ++ r
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.
		(* /\ (l = [] -> (* sub_ls が端点を含む場合，延長線上にも関係ないセグメントが近づかないことを要請 *)
				let X1 := head_seg sub_ls default_segment in 
				let width := (term_x X1) - (init_x X1) in (* 矩形の横幅 *)
				let length := (term_y X1) - (init_y X1) in (* 矩形の縦幅 *)
				forall p, onHeadSegment X1 p -> 
					let rect := rectangular_from_diagonal ((fst p)-width, (snd p)-length) p in (* 矩形 *)
					forall q, 
					(exists seg, onExtendSegment ls seg q /\ ~ onHeadSegment X1 q) 
					-> ~ rect q) *)


Lemma P_is_oneway : one_way_listDir [Plus].
Proof. (* ここは one_way_listDir の定義さえできれば示せる？ *)
Admitted.

Lemma embedding_P_is_oneway : forall seg, 
	embed_listDir [Plus] [seg] -> is_one_way_embedding [seg].
Proof.
Admitted.

Lemma PMP_is_oneway : one_way_listDir [Plus; Minus; Plus].
Proof.
Admitted.

(* 許容可能ならば，疎な開埋め込みが存在する *)
Lemma embed_sparsely (dl dr : list Direction) (sub_ds : list Direction) :
	AdmissibleDirs (dl ++ sub_ds ++ dr)
	-> one_way_listDir sub_ds
	-> exists l r sub_ls, 
		embed_listDir dl l 
		/\ embed_listDir dr r 
		/\ embed_listDir sub_ds (proj1_sig sub_ls)
		/\ ~ close (l ++ (proj1_sig sub_ls) ++ r)
		/\ sparse sub_ls (l ++ (proj1_sig sub_ls) ++ r).
Proof. Admitted.

(* 矩形の中にピッタリ収まる1つのセグメントが描ける *)
Lemma embed_in_rectangle : forall (ls : one_way_embedding), 
	exists seg : Segment, 
		(forall rr, onSegment seg rr -> in_rect ls rr) 
		/\ init seg = init (hd default_segment (proj1_sig ls)) 
		/\ term seg = term (last (proj1_sig ls) default_segment).
Proof. Admitted.

(* 端点を含まない sub_ls の周りが疎な開埋め込みにおいて，sub_ls をその領域に収まるセグメントに置き換えても開のまま *)
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
	intros l r admds. destruct l as [ | l'].
	- (* 端点を含む簡約 *) admit.
	- destruct r as [ | r'].
		+ (* 端点を含む簡約 *) admit.
		+ (* 簡約にかかわった部分の両端に別のセグメントが存在する場合 *)
			unfold AdmissibleDirs. intros ps Hps. unfold admissible.
			pose proof PMP_is_oneway as PMP_is_oneway.
			apply (embed_sparsely _ _ _ admds) in PMP_is_oneway as 
				[ll [lr [sub_ls [Hl [Hr [HPMP [Hopen Hsparse]]]]]]].
			destruct (embed_in_rectangle sub_ls) as 
				[seg [Hin_rect [Hinit Hterm]]].
			exists (ll ++ [seg] ++ lr). split.
			* (* 簡約後の向き列の埋め込みになっていること *) admit.
			* (* その埋め込みが開であること *) admit.
			(* apply seg_in_rectangle_keep_openness. *)
Admitted.

(* Plus (の向きを持つ Primitive Segment)の埋め込みを，[Plus; Minus; Plus] の埋め込みとなる３つに矩形内で分割できる
	もっと一般的にしたい *)
Lemma P_to_PMP : forall seg : Segment,
	embed_listDir [Plus] [seg]
	-> exists seg1 seg2 seg3,
		embed_listDir [Plus; Minus; Plus] [seg1; seg2; seg3] (* この内部で seg1-3 が連結していることは示されてほしい *)
		(* /\ forall rr, (exists s:Segment, onExtendSegment [seg1; seg2; seg3] s rr 
			-> in_rect (exist _ _ [seg] embedding_P_is_oneway) rr) (* 矩形の内部で分割できている *) *)
		/\ init seg1 = init seg
		/\ term seg3 = term seg.

(* [+-+ => +] での簡約で，簡約先が許容可能ならもともと許容可能 *)
Lemma AdmissibleDirs_r1_Plus_inv: forall l r,
  AdmissibleDirs (l ++ [Plus] ++ r) -> AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r).
Proof.
	unfold AdmissibleDirs. unfold admissible. intros l r admds sc Hsc.
	(* admds を， sc と同じ X1 を持ち，簡約部分で２つの PSeg が取れた scurve で具体化する *)
	(* すると admds から，上の scurve の許容可能性の証拠 ls を得る *)
	(* この ls の内部に２つの Segment を，P_to_PMP によって追加すれば，欲しい埋め込みが得られる *)
	(* その埋め込みが開であることは，seg_in_rectangle_keep_openness より *)
Admitted.