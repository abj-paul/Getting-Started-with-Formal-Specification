Inductive bool : Type :=
| true
| false.

Definition not_bool (x: bool) :=
  match x with
  | true => false
  | false => true
  end.

Definition or_bool (x: bool) (y: bool) :=
  match x with
  | true => true
  | false => y
  end.

Definition and_bool (x: bool) (y: bool) :=
  match x with
  | true => y
  | false => false
  end.

Notation "x && y" := (and_bool x y).
Notation "x || y" := (or_bool x y).
Notation "|- x" := (not_bool x) (at level 70).

Example test_boolean_1:
  (true || false || true) = true.
Proof. simpl. reflexivity. Qed.

Example test_boolean_2:
  (true && false || true) = true.
Proof. simpl. reflexivity. Qed.

Example test_boolean_3:
  |-(true && false || true) = false.
Proof. simpl. reflexivity. Qed.

(** if-else *)
Definition or_bool' (a b : bool) : bool :=
  if a then true
  else b.

Compute (or_bool' true false).

Definition nand_bool (a b : bool) : bool :=
  not_bool(and_bool a b ).

Example test_nand:
  (nand_bool true true) = false.

Proof. simpl. reflexivity. Qed.

