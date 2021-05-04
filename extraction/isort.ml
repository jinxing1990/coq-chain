
type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val sort_prog_base : int list **)

let sort_prog_base =
  []

(** val perm_nil_sort_cons : int -> int list -> int list **)

let perm_nil_sort_cons a _ =
  a :: []

(** val sort_ind_case :
    int -> int -> int list -> int list -> int list -> int list **)

let sort_ind_case a a0 l' _ x =
  let s = (<=) a a0 in if s then a :: (a0 :: l') else a0 :: x

(** val sort_prog_IH : int -> int list -> int list -> int list **)

let rec sort_prog_IH a l = function
| [] -> perm_nil_sort_cons a l
| y :: l0 -> let s = sort_prog_IH a l0 l0 in sort_ind_case a y l0 l s

(** val isort_prog : int list -> int list **)

let rec isort_prog = function
| [] -> sort_prog_base
| y :: l0 -> sort_prog_IH y l0 (isort_prog l0)
