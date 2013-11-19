Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Module VVClock.

(** Type definitions for actors, counts and timestamps. *)
Definition actor := nat.
Definition count := nat.
Definition timestamp := nat.

(** Model clocks as triples. *)
Definition clock := prod actor (prod count timestamp).

(** Model vector clocks at a list of clock triples. *)
Definition vclock := (list clock)%type.

(** Create a new vector clocks. *)
Definition fresh : vclock := nil.

Definition find' (actor : actor) :=
  fun clock : clock => match clock with
                           | pair x _ => beq_nat actor x
                       end.

Definition find'' (actor : actor) :=
  fun clock : clock => match clock with
                           | pair x _ => negb (beq_nat actor x)
                       end.

(** Function to initialize a timestamp with the default value. *)
Definition init_timestamp := O.

(** Function to increment a timestamp from one value to the next. *)
Definition incr_timestamp (timestamp : timestamp) := S timestamp.

(** Function to initialize a counter with the default values. *)
Definition init_count := O.

(** Function to increment the counter from one value to the next. *)
Definition incr_count (count : count) := S count.

(** Increment a vector clock. *)
Definition increment (actor : actor) (vclock : vclock) :=
  match find (find' actor) vclock with
  | None => 
    cons (pair actor (pair init_count init_timestamp)) vclock
  | Some (pair x (pair count timestamp)) => 
    cons (pair x (pair (incr_count count) (incr_timestamp timestamp)))
                       (filter (find' actor) vclock)
  end.

(** Helper fold function for equality comparison betwen two vector clocks. *)
Definition equal' status_and_vclock (clock : clock) :=
  match clock, status_and_vclock with
    | pair actor (pair count timestamp), 
      pair status vclock => match find (find' actor) vclock with
                              | None => 
                                pair false vclock
                              | Some (pair _ (pair y z)) => 
                                pair (andb 
                                        status
                                        (andb
                                           (beq_nat count y)
                                           (beq_nat timestamp z)))
                                        vclock
                            end
  end.

(** Compare equality between two vector clocks. *)
Definition equal (vc1 vc2 : vclock) := 
  match fold_left equal' vc1 (pair true vc2) with
    | pair false _ => 
      false
    | pair true _ => 
      match fold_left equal' vc2 (pair true vc1) with
        | pair false _ => 
          false
        | pair true _ => 
          true
      end
  end.

(** Less than or equal to comparson for natural numbers. *)
Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(** Decends fold helper for determining ordering. *)
Definition descends' status_and_vclock (clock : clock) :=
  match clock, status_and_vclock with
    | pair actor (pair count timestamp),
      pair status vclock => match find (find' actor) vclock with
                              | None => 
                                pair false vclock
                              | Some (pair _ (pair y z)) => 
                                pair (andb
                                        status
                                        (andb
                                           (ble_nat count y)
                                           (ble_nat timestamp z))) vclock
                            end
  end.

(** Determine if one vector clock is a descendent of another. *)
Definition descends (vc1 vc2 : vclock) := 
  match fold_left descends' vc2 (pair true vc1) with
    | pair false _ =>
      false
    | pair true _ => 
      true
  end.

(** Fold helper for the merge function which computes max. *)
Definition max' (vclock : vclock) (clock : clock) :=
  match clock with
    | pair actor (pair count timestamp) => 
      match find (find' actor) vclock with
        | None => 
          cons (pair actor (pair count timestamp)) vclock
        | Some (pair _ (pair y z)) => 
          cons (pair actor (pair (max count y) (max timestamp z)))
               (filter (find'' actor) vclock)
      end
  end.

(** Merge two vector clocks. *)
Definition merge (vc1 vc2 : vclock) := fold_left max' vc1 vc2.

(** Return current count of an actor in a vector clock. *)
Definition get_counter (actor : actor) (vclock : vclock) :=
  match find (find' actor) vclock with
      | None => 
        None
      | Some (pair a (pair count timetsamp)) =>
        Some count
  end.

(** Return current timestamp of an actor in a vector clock. *)
Definition get_timestamp (actor : actor) (vclock : vclock) :=
  match find (find' actor) vclock with
      | None => 
        None
      | Some (pair a (pair count timetsamp)) =>
        Some timestamp
  end.

(** Return all actors who have ever incremented the vector clock. *)
Fixpoint all_nodes (vclock : vclock) :=
  match vclock with
    | nil => 
      nil
    | c :: cs => 
      match c with
        | pair x y => x :: all_nodes cs
      end
  end.

(** Helper for computing greater than. *)
Definition bgt_nat (m n : nat) := negb (ble_nat m n).

(** Vector clock pruning. 

  The general idea here is to support the following axioms:
  1.) If it's small, do nothing.
  2.) Then, if the earliest timestamp is young, do nothing.
  3.) Then, if it's big, and old, prune, and recurse.
  4.) Else, do nothing.

*)
Fixpoint prune'
         (vclock : vclock)
         (small large : nat)
         (young old : timestamp) :=
  match vclock with
    | nil =>
      vclock
    | pair actor (pair count timestamp) :: clocks =>
      match (ble_nat (length vclock) small) with 
        | true => 
          vclock
        | false => 
          match (ble_nat timestamp young) with
            | true => 
              vclock
            | false => 
              match (bgt_nat timestamp old) with
                  | false => 
                    vclock
                  | true => 
                    match (bgt_nat (length vclock) large) with
                        | false =>
                          vclock
                        | true => 
                          prune' clocks small large young old
                    end
              end
          end
      end
  end.

(** Proof that the merge function is idempotent. *)
Theorem merge_idemp : forall vc1, merge vc1 vc1 = vc1.
Proof. Admitted.

(** Proof that the merge function is commutative. *)
Theorem merge_comm : forall vc1 vc2, merge vc1 vc2 = merge vc2 vc1.
Proof. Admitted.

(** Proof that the merge function is associatative. *)
Theorem merge_assoc : forall vc1 vc2 vc3, 
                        merge vc1 (merge vc2 vc3) = merge (merge vc1 vc2) vc3.
Proof. Admitted.

(** Proof that the increment function over vector clocks increments. *)
Theorem vclock_increment : forall (actor : actor) (vclock : vclock),
  descends (increment actor vclock) vclock = true.
Proof. Admitted.

(** Proof that the vector clock preserves an antisymmetric relation. *)
Theorem vclock_antisymmetric : forall (actor : actor) (vclock : vclock),
  descends (increment actor vclock) vclock = 
    negb (descends vclock (increment actor vclock)).
Proof. Admitted.

End VVClock.

Extraction Language CoreErlang.

Recursive Extraction VVClock.
