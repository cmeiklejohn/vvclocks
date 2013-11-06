Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Module VVClock.

Definition actor := nat.
Definition count := nat.
Definition clock := (actor * count)%type.
Definition vclock := list clock%type.

Definition fresh : vclock := nil.

Definition find' (actor : actor) :=
  fun clock : clock => match clock with
                           | pair x _ => beq_nat actor x
                       end.

Definition find'' (actor : actor) :=
  fun clock : clock => match clock with
                           | pair x _ => negb (beq_nat actor x)
                       end.

Definition increment (actor : actor) (vclock : vclock) :=
  match find (find' actor) vclock with
  | None => 
    cons (pair actor 1) vclock
  | Some (pair x y) => 
    cons (pair x (S y)) (filter (find' actor) vclock)
  end.

Definition equal' status_and_vclock (clock : clock) :=
  match clock, status_and_vclock with
    | pair actor count, 
      pair status vclock => match find (find' actor) vclock with
                              | None => 
                                pair false vclock
                              | Some (pair _ y) => 
                                pair (andb
                                        status
                                        (beq_nat count y)) vclock
                            end
  end.

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

Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition descends' status_and_vclock (clock : clock) :=
  match clock, status_and_vclock with
    | pair actor count,
      pair status vclock => match find (find' actor) vclock with
                              | None => 
                                pair false vclock
                              | Some (pair _ y) => 
                                pair (andb
                                        status
                                        (ble_nat count y)) vclock
                                                               end
  end.

Definition descends (vc1 vc2 : vclock) := 
  match fold_left descends' vc2 (pair true vc1) with
    | pair false _ =>
      false
    | pair true _ => 
      true
  end.

Definition max' (vclock : vclock) (clock : clock) :=
  match clock with
    | pair actor count =>  match find (find' actor) vclock with
                             | None => 
                               cons (pair actor count) vclock
                             | Some (pair _ y) => 
                               cons (pair actor (max count y))
                                    (filter (find'' actor) vclock)
                           end
  end.

Definition merge (vc1 vc2 : vclock) := fold_left max' vc1 vc2.

Definition get_counter (actor : actor) (vclock : vclock) :=
  match find (find' actor) vclock with
      | None => 
        None
      | Some (pair a vc) =>
        Some vc
  end.

Fixpoint all_nodes (vclock : vclock) :=
  match vclock with
    | nil => 
      nil
    | c :: cs => 
      match c with
        | pair x y => x :: all_nodes cs
      end
  end.

Theorem merge_idemp : forall vc1, merge vc1 vc1 = vc1.
Proof. Admitted.

Theorem merge_comm : forall vc1 vc2, merge vc1 vc2 = merge vc2 vc1.
Proof. Admitted.

Theorem merge_assoc : forall vc1 vc2 vc3, 
                        merge vc1 (merge vc2 vc3) = merge (merge vc1 vc2) vc3.
Proof. Admitted.

Theorem vclock_increment : forall (actor : actor) (vclock : vclock),
  descends (increment actor vclock) vclock = true.
Proof. Admitted.

Theorem vclock_antisymmetric : forall (actor : actor) (vclock : vclock),
  descends (increment actor vclock) vclock = 
    negb (descends vclock (increment actor vclock)).
Proof. Admitted.

End VVClock.

Extraction Language CoreErlang.

Recursive Extraction VVClock.
