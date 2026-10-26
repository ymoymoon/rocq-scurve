Require Export Sparse.Classify.
Import ListNotations.

(* 端点変位から得られる再接続。元と同じ primitive を要求する。 *)
Record reconnect_segment (k : EndpointClassifier) (old new : Segment) : Prop := {
  reconnect_init : init new = move_point k (init old);
  reconnect_term : term new = move_point k (term old);
  reconnect_primitive : primitive_segment new = primitive_segment old
}.

Definition reconnect_list (k : EndpointClassifier) :=
  Forall2 (reconnect_segment k).

(* h を引数に持たない再接続関係。先頭・末尾には必要な片側傾きを指定する。 *)
Record reconnect_split (k : EndpointClassifier) (l sub r l' r' : list Segment) : Prop := {
  reconnect_left : reconnect_list k l l';
  reconnect_right : reconnect_list k r r';
  reconnect_head_slope : l <> [] ->
    slope_init (hd_segment l') = slope_init (hd_segment l);
  reconnect_last_slope : r <> [] ->
    slope_term (last_segment r') = slope_term (last_segment r)
}.

Definition reconnect_one (k : EndpointClassifier) (seg : Segment)
    (H : endpoint_displacements_ordered k seg) : Segment :=
  make_seg (move_point k (init seg)) (move_point k (term seg)) (orn_seg seg)
    (moved_endpoints_reconnectable k seg H).
