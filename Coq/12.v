(** Check command prints the type of an expression. Every expression in Coq has a type *)
Check true.
Check (negb true) : bool.

(** Even functions have type in Coq *)
Check negb :
        bool -> bool.
