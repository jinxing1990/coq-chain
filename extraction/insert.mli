
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val perm_nil_sort_cons : int -> int list -> int list

val sort_ind_case : int -> int -> int list -> int list -> int list -> int list

val sort_prog_IH : int -> int list -> int list -> int list

val insert_prog : int -> int list -> int list
