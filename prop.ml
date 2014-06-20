(* LIB *)

let unique xs = List.fold_left (fun res x -> if List.mem x res then res else x::res) [] xs (* TODO more efficient *)

(* KERNEL *)

type form =
  Var of string
| Impl of form * form

type thm = Sequent of (form list * form)

let assume a = Sequent([a], a)
let intro_rule a (Sequent(benv, b)) =
    if List.mem a benv
    then Sequent(List.filter (fun x -> a <> x) benv, Impl(a, b))
    else failwith("intro_rule, incomplete environment")
let elim_rule (Sequent(aenv, Impl(a, b))) (Sequent(cenv, c)) =
    if a = c
    then Sequent(unique (List.append aenv cenv), b)
    else failwith("elim_rule, not of form (a -> b, a)")

(* Tests *)

let a = (Var("a"))
let x = elim_rule (intro_rule a (assume a)) (assume a)
