(* LIB *)

let unique xs = List.fold_left (fun res x -> if List.mem x res then res else x::res) [] xs (* TODO more efficient *)
let empty l = (List.length l) = 0
let implode f sep xs =
    if empty xs then ()
    else (f (List.hd xs) ; List.iter (fun x -> print_string sep ; f x) (List.tl xs))
    

(* KERNEL *)

module type LCF_kernel =
    sig
        type form = private
          Var of string
        | Impl of form * form

        type thm
        
        val assume : form -> thm
        val intro_rule : form -> thm -> thm
        val elim_rule : thm -> thm -> thm
        
        val is_var : form -> bool
        val is_impl : form -> bool
        
        val mk_var : string -> form
        val mk_impl : form -> form -> form
        
        val dest_var : form -> string
        val dest_impl : form -> form * form
        
        val hyp : thm -> form list
        val concl : thm -> form
end

module LCF : LCF_kernel = struct

    type form =
          Var of string
        | Impl of form * form

    type thm = Sequent of (form list * form)

    let assume a = Sequent([a], a)
    let intro_rule a (Sequent(benv, b)) =
        if List.mem a benv
        then Sequent(List.filter (fun x -> a <> x) benv, Impl(a, b))
        else failwith("intro_rule, incomplete environment")
    let elim_rule athm (Sequent(cenv, c)) =
        match athm with
            (Sequent(aenv, Impl(a, b))) ->
                if a = c
                then Sequent(unique (List.append aenv cenv), b)
                else failwith("elim_rule, not of form (a -> b, a)")
          | _ -> failwith("elim_rule, not of form (a -> b, a)")
    
    let is_var =
        function
          Var(_)     -> true
        | Impl(_, _) -> false
    
    let is_impl =
        function
          Var(_)     -> false
        | Impl(_, _) -> true
    
    let mk_var str = Var(str)
    let mk_impl a b = Impl(a, b)
    
    let dest_var =
        function
          Impl(_, _) -> failwith "dest_var, is an Impl"
        | Var(str) -> str
    
    let dest_impl =
        function
          Impl(a, b) -> (a, b)
        | Var(_)     -> failwith "dest_impl, is a Var"
    
    let hyp (Sequent(asl, c)) = asl
    let concl (Sequent(asl, c)) = c
end

include LCF

(* PACKAGE FOR GOAL-DIRECTED PROOFS *)

type goal = form list * form
type justification = thm list -> thm
type goalstate = goal list * justification
type tactic = goal -> goalstate

let by (tac : tactic) ((agoals, ajust) : goalstate) =
    if empty agoals then failwith "by: list of subgoals is empty, we're done."
    else let agoal = List.hd agoals in
        let (bgoals, bjust) = tac agoal in
            (List.append bgoals (List.tl agoals), fun thms -> ajust (List.append [(bjust thms)] thms))

(* TACTICS WHICH CORRESPOND TO KERNEL RULES *)

let thm_to_form t = List.fold_right mk_impl (hyp t) (concl t)

let assumption = (
    fun (asl, c) ->
        if List.mem c asl then
           ([], fun _ -> assume c)
        else failwith("assumption, does not contain the conclusion as hypothesis")
    : tactic)

let intro_tac = (
    fun (asl, c) ->
        let (a, b) = dest_impl c in
            ([(List.append asl [a], b)], fun thms ->
                let bthm = List.find (fun thm -> concl thm = b) thms in
                    intro_rule a bthm)
    : tactic)

let elim_tac =
    fun a (asl, c) -> (
        [ (asl, mk_impl a c); (asl, a) ],
        fun thms ->
            let lthm = List.find (fun thm -> concl thm = mk_impl a c) thms in
                let rthm = List.find (fun thm -> concl thm = a) thms in
                    elim_rule lthm rthm)

(* Pretty Printer *)

let rec print_form =
    function x ->
        if is_var x then print_string (dest_var x)
        else match dest_impl x with
           (a, b) -> if is_impl a then (print_string "("; print_form a; print_string ") -> "; print_form b)
                     else print_form a; print_string " -> "; print_form b

let print_thm =
    function t -> 
    if empty (hyp t) then (print_string "|- "; print_form (concl t))
    else (implode print_form ", " (hyp t); print_string " |- "; print_form (concl t))

(* Tests *)

let mk_init =
    (function (asl, c) -> ([(asl, c)], fun thms -> List.find (fun thm -> concl thm = c) thms) : tactic) 

let a = mk_var "a"
let b = mk_var "b"

let gs1 = mk_init ([mk_impl a b; a], b)
let gs2 = mk_init ([], mk_impl a a)

;;

let (_, just) = by assumption (by assumption (by (elim_tac a) gs1)) in
    let t = just [] in
        print_thm t;

print_string "\n"

;;

let (_, just) = by assumption (by intro_tac gs2) in
    let t = just [] in
        print_thm t;

print_string "\n"

;;
