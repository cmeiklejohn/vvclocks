(*
  Ported from Basho's riak_core vclock module.
  https://github.com/basho/riak_core/blob/develop/src/vclock.erl

  Christopher Meiklejohn, 10/06/2013
  christopher.meiklejohn@gmail.com
*) 

Require Import Coq.FSets.FMaps.
Require Import Coq.FSets.FSets.
Require Import Coq.Arith.Arith.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.MSets.MSetList.

Module UOT_to_OrderedTypeLegacy (UOT:OrderedType) <:
  (IsEqOrig UOT) <: OrderedType.OrderedType.

  Definition t := UOT.t.
  Definition lt := UOT.lt.
  Definition eq := UOT.eq.
  Definition eq_refl := let (r, _, _) := UOT.eq_equiv in r.
  Definition eq_sym := let (_, s, _) := UOT.eq_equiv in s.
  Definition eq_trans := let (_, _, t) := UOT.eq_equiv in t.

  Lemma lt_trans : forall x y z : t, UOT.lt x y -> UOT.lt y z -> UOT.lt x z.
  Proof. destruct UOT.lt_strorder as [i t]. apply t. Qed.

  Lemma lt_not_eq : forall x y : t, UOT.lt x y -> ~ UOT.eq x y.
  Proof. destruct UOT.lt_strorder as [i t]. intros. intro. rewrite H0 in *.
         exact (i y H). Qed.

  Definition compare (x y : t) : OrderedType.Compare UOT.lt UOT.eq x y :=
    match (CompareSpec2Type (UOT.compare_spec x y)) with
      | CompLtT l => OrderedType.LT l
      | CompEqT e => OrderedType.EQ e
      | CompGtT g => OrderedType.GT g
    end.

  Definition eq_dec := UOT.eq_dec.
  Definition eq_equiv := UOT.eq_equiv.
  Definition lt_strorder := UOT.lt_strorder.
  Definition lt_compat := UOT.lt_compat.
End UOT_to_OrderedTypeLegacy.

Module Nat_as_Legacy_OT    := UOT_to_OrderedTypeLegacy (Nat_as_OT).
Module VectorClockMap      := FMapWeakList.Make (Nat_as_Legacy_OT).
Module VectorClockMapFacts := FMapFacts.Facts (VectorClockMap).

Module VClock.

Definition VectorClock := VectorClockMap.t nat.

(*
  % @doc Create a brand new vclock.
  -spec fresh() -> vclock().
  fresh() ->
      [].
*)

Definition VClock_fresh : VectorClock := VectorClockMap.empty nat.

(*
  % @doc Compares two VClocks for equality.
  -spec equal(VClockA :: vclock(), VClockB :: vclock()) -> boolean().
  equal(VA,VB) ->
      lists:sort(VA) =:= lists:sort(VB).
*)
Definition VClock_equal (c1 c2 : VectorClock) :=
  VectorClockMap.equal beq_nat c1 c2.

(*
  % @doc Combine all VClocks in the input list into their least possible
  %      common descendant.
  -spec merge(VClocks :: [vclock()]) -> vclock() | [].
  merge([])             -> [];
  merge([SingleVclock]) -> SingleVclock;
  merge([First|Rest])   -> merge(Rest, lists:keysort(1, First)).

  merge([], NClock) -> NClock;
  merge([AClock|VClocks],NClock) ->
      merge(VClocks, merge(lists:keysort(1, AClock), NClock, [])).

  merge([], [], AccClock) -> lists:reverse(AccClock);
  merge([], Left, AccClock) -> lists:reverse(AccClock, Left);
  merge(Left, [], AccClock) -> lists:reverse(AccClock, Left);
  merge(V=[{Node1,{Ctr1,TS1}=CT1}=NCT1|VClock],
        N=[{Node2,{Ctr2,TS2}=CT2}=NCT2|NClock], AccClock) ->
      if Node1 < Node2 ->
              merge(VClock, N, [NCT1|AccClock]);
         Node1 > Node2 ->
              merge(V, NClock, [NCT2|AccClock]);
         true ->
              ({_Ctr,_TS} = CT) = if Ctr1 > Ctr2 -> CT1;
                                     Ctr1 < Ctr2 -> CT2;
                                     true        -> {Ctr1, erlang:max(TS1,TS2)}
                                  end,
              merge(VClock, NClock, [{Node1,CT}|AccClock])
      end.
*)
Definition Clock_merge (n1 n2 : option nat) :=
  match n1, n2 with
    | None, None => None
    | Some n, None => Some n
    | None, Some n => Some n
    | Some n1', Some n2' => Some (max n1' n2')
  end.

Definition VClock_merge c1 c2 := VectorClockMap.map2 Clock_merge c1 c2.

(*
  % @doc Increment VClock at Node.
  -spec increment(Node :: vclock_node(), VClock :: vclock()) -> vclock().
  increment(Node, VClock) ->
      increment(Node, timestamp(), VClock).

  % @doc Increment VClock at Node.
  -spec increment(Node :: vclock_node(), IncTs :: timestamp(),
                  VClock :: vclock()) -> vclock().
  increment(Node, IncTs, VClock) ->
      {{_Ctr, _TS}=C1,NewV} = case lists:keytake(Node, 1, VClock) of
                                  false ->
                                      {{1, IncTs}, VClock};
                                  {value, {_N, {C, _T}}, ModV} ->
                                      {{C + 1, IncTs}, ModV}
                              end,
      [{Node,C1}|NewV].
*)
Definition VClock_increment actor clocks :=
  match VectorClockMap.find actor clocks with
    | None       =>  VectorClockMap.add actor 1 clocks
    | Some count => (VectorClockMap.add actor (S count) clocks)
  end.

(*
  % @doc Return true if Va is a direct descendant of Vb, 
  % else false -- remember, a vclock is its own descendant!
  -spec descends(Va :: vclock()|[], Vb :: vclock()|[]) -> boolean().
  descends(_, []) ->
      % all vclocks descend from the empty vclock
      true;
  descends(Va, Vb) ->
      [{NodeB, {CtrB, _T}}|RestB] = Vb,
      case lists:keyfind(NodeB, 1, Va) of
          false ->
              false;
          {_, {CtrA, _TSA}} ->
              (CtrA >= CtrB) andalso descends(Va,RestB)
          end.
*)
Definition Clock_compare (n1 n2 : option nat) :=
  match n1, n2 with
    | None, None => None
    | Some n, None => Some false
    | None, Some n => Some true
    | Some n1', Some n2' => Some (leb n1' n2')
  end.

Definition Clock_true (n1 n2 : option nat) :=
  match n1, n2 with
    | None, None => None
    | Some n, None => Some true
    | None, Some n => Some true
    | Some n1', Some n2' => Some true
  end.

Definition VClock_descends (c1 c2 : VectorClock) :=
  VectorClockMap.equal eqb
    (VectorClockMap.map2 Clock_compare c2 c1)
    (VectorClockMap.map2 Clock_true c2 c1).

(*
  % @doc Get the timestamp value in a VClock set from Node.
  -spec get_timestamp(Node :: vclock_node(), VClock :: vclock()) -> 
    timestamp() | undefined.
  get_timestamp(Node, VClock) ->
      case lists:keyfind(Node, 1, VClock) of
    {_, {_Ctr, TS}} -> TS;
    false           -> undefined
      end.
*)

(*
  % @doc Possibly shrink the size of a vclock, depending on current age and size.
  -spec prune(V::vclock(), Now::integer(), BucketProps::term()) -> vclock().
  prune(V,Now,BucketProps) ->
      %% This sort need to be deterministic, to avoid spurious merge conflicts later.
      %% We achieve this by using the node ID as secondary key.
      SortV = lists:sort(fun({N1,{_,T1}},{N2,{_,T2}}) -> {T1,N1} < {T2,N2} end, V),
      prune_vclock1(SortV,Now,BucketProps).
  % @private
  prune_vclock1(V,Now,BProps) ->
      case length(V) =< get_property(small_vclock, BProps) of
          true -> V;
          false ->
              {_,{_,HeadTime}} = hd(V),
              case (Now - HeadTime) < get_property(young_vclock,BProps) of
                  true -> V;
                  false -> prune_vclock1(V,Now,BProps,HeadTime)
              end
      end.
  % @private
  prune_vclock1(V,Now,BProps,HeadTime) ->
      % has a precondition that V is longer than small and older than young
      case (length(V) > get_property(big_vclock,BProps)) orelse
           ((Now - HeadTime) > get_property(old_vclock,BProps)) of
          true -> prune_vclock1(tl(V),Now,BProps);
          false -> V
      end.
*)

(*
  % @doc Return the list of all nodes that have ever incremented VClock.
  -spec all_nodes(VClock :: vclock()) -> [vclock_node()].
  all_nodes(VClock) ->
      [X || {X,{_,_}} <- VClock].
*)

(*
  get_property(Key, PairList) ->
      case lists:keyfind(Key, 1, PairList) of
        {_Key, Value} ->
          Value;
        false ->
          undefined
      end.
*)

(*
  % @doc Return a timestamp for a vector clock
  -spec timestamp() -> timestamp().
  timestamp() ->
      %% Same as calendar:datetime_to_gregorian_seconds(erlang:universaltime()),
      %% but significantly faster.
      {MegaSeconds, Seconds, _} = os:timestamp(),
      ?SECONDS_FROM_GREGORIAN_BASE_TO_EPOCH + MegaSeconds*1000000 + Seconds.
*)

(*
  % @doc Get the counter value in VClock set from Node.
  -spec get_counter(Node :: vclock_node(), VClock :: vclock()) -> counter().
  get_counter(Node, VClock) ->
      case lists:keyfind(Node, 1, VClock) of
    {_, {Ctr, _TS}} -> Ctr;
    false           -> 0
      end.
*)

Lemma Clock_merge_comm : forall n1 n2, 
  Clock_merge n1 n2 = Clock_merge n2 n1.
Proof.
  intros. destruct n1; destruct n2; auto.
  simpl. f_equal. apply Max.max_comm.
Qed.

Lemma Clock_merge_idempotent : forall n1, 
  Clock_merge n1 n1 = n1.
Proof.
  intros. destruct n1; auto; simpl.
  f_equal. apply Max.max_idempotent.
Qed.

Lemma Clock_merge_assoc : forall n1 n2 n3, 
  Clock_merge n1 (Clock_merge n2 n3) = Clock_merge (Clock_merge n1 n2) n3.
Proof.
  intros. destruct n1; destruct n2; destruct n3; auto.
  unfold Clock_merge. f_equal. apply Max.max_assoc.
Qed.

Lemma Clock_compare_refl : forall x,
  Clock_compare x x = Clock_true x x.
Proof.
  intros; destruct x; auto. unfold Clock_compare. unfold Clock_true.
  destruct n; auto. f_equal. simpl. rewrite leb_correct; auto.
Qed.

Theorem VectorClock_merge_comm : forall c1 c2,
  VClock_equal (VClock_merge c1 c2) (VClock_merge c2 c1) = true.
Proof.
Admitted.

Theorem VectorClock_merge_idempotent : forall clocks,
  VClock_equal (VClock_merge clocks clocks) clocks = true.
Proof.
Admitted.

Theorem VectorClock_merge_assoc : forall c1 c2 c3,
  VClock_equal
    (VClock_merge c1 (VClock_merge c2 c3))
    (VClock_merge (VClock_merge c1 c2) c3) = true.
Proof.
Admitted.

Theorem VectorClock_descends_idempotent : forall clocks,
  VClock_descends clocks clocks = true.
Proof.
Admitted.

Theorem VectorClock_incr_mono : forall clocks actor,
  VClock_descends (VClock_increment actor clocks) clocks = true.
Proof.
Admitted.

Theorem VectorClock_merge_mono : forall c1 c2,
  VClock_descends (VClock_merge c1 c2) c1 = true.
Proof.
Admitted.

End VClock.

Extraction Language CoreErlang.

Recursive Extraction 
          VClock.VClock_fresh 
          VClock.VClock_equal 
          VClock.VClock_merge 
          VClock.VClock_descends 
          VClock.VClock_increment.
