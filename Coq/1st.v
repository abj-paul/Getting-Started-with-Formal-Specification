Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
    

(** Pattern Matching *)
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday friday)).

(** mathematical examlpe / unit test *)
Example test_next_weekday :
  (next_weekday (next_weekday tuesday)) = thursday. 

(** Lets prove the example *)
Proof. simpl. reflexivity. Qed.
