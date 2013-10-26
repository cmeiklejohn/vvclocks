Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Module VVClock.

Definition vclock := list (nat * nat)%type.

(*
  % @doc Create a brand new vclock.
  -spec fresh() -> vclock().
  fresh() ->
      [].
*)

Definition fresh : vclock := nil.

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

Definition increment (actor : nat) (vclock : vclock) :=
  match (find (fun clock => match clock with
                            | pair x _ => beq_nat actor x
                        end) vclock) with
  | None => 
    cons (pair actor 1) vclock
  | Some (pair x y) => 
    cons (pair x (S y)) (filter
                           (fun clock => match clock with
                                           | pair x _ =>
                                             negb (beq_nat actor x)
                                         end) vclock)
  end.

(*
  % @doc Compares two VClocks for equality.
  -spec equal(VClockA :: vclock(), VClockB :: vclock()) -> boolean().
  equal(VA,VB) ->
      lists:sort(VA) =:= lists:sort(VB).
*)

Definition equal' status_and_vclock clock :=
  match clock, status_and_vclock with
    | pair actor count, 
      pair status vclock => match find
                                    (fun clock => match clock with
                                                    | pair x _ =>
                                                      beq_nat actor x
                                                  end) vclock with
                              | None => pair false vclock
                              | Some (pair _ y) => 
                                pair (andb
                                        status
                                        (beq_nat count y)) vclock
                            end
  end.

Definition equal vc1 vc2 := 
  match fold_left equal' vc1 (pair true vc2) with
    | pair false _ => false
    | pair true _ => match fold_left equal' vc2 (pair true vc1) with
                       | pair false _ => false
                       | pair true _ => true
                     end
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

Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition descends' status_and_vclock clock :=
  match clock, status_and_vclock with
    | pair actor count,
      pair status vclock => match find
                                    (fun clock => match clock with
                                                    | pair x _ =>
                                                      beq_nat actor x
                                                  end)
                                    vclock with
                              | None => pair true vclock
                              | Some (pair _ y) => 
                                pair (andb
                                        status
                                        (ble_nat count y)) vclock
                                                               end
  end.

Definition descends vc1 vc2 := 
  match fold_left descends' vc1 (pair true vc2) with
    | pair false _ =>
      false
    | pair true _ => 
      true
  end.

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

Definition max' vclock clock :=
  match clock with
    | pair actor count =>  match find
                                   (fun clock => match clock with
                                                   | pair x _ => beq_nat actor x
                                                 end) vclock with
                             | None => 
                               cons (pair actor count) vclock
                             | Some (pair _ y) => 
                               cons (pair actor
                                          (max count y))
                                    (filter
                                       (fun clock => match clock with
                                                       | pair x _ =>
                                                         negb (beq_nat actor x)
                                                     end)
                                       vclock)
                           end
  end.

Definition merge vc1 vc2 := fold_left max' vc1 vc2.

End VVClock.

Extraction Language CoreErlang.

Recursive Extraction VVClock.fresh.
