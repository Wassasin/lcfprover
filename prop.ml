(* LIB *)

let unique xs = List.fold_left (fun res x -> if List.mem x res then res else x::res) [] xs (* TODO more efficient *)
let empty l = (List.length l) = 0
let implode f sep xs = if not (empty xs) then (f (List.hd xs) ; List.iter (fun x -> print_string sep ; f x) (List.tl xs))

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
    let intro_rule a (Sequent(benv, b)) = Sequent(List.filter (fun x -> a <> x) benv, Impl(a, b))
    let elim_rule (Sequent(env0, f)) (Sequent(env1, a1)) =
        match f with
            Impl(a0, b) -> if a0 = a1
                then Sequent(unique (List.append env0 env1), b)
                else failwith("elim_rule (a0 -> b, a1), where a0 != a1")
          | _ -> failwith("elim_rule, left hand side not an Impl")
    
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

include LCF (* Include sealed kernel *)

(* Pretty Printer *)

let rec print_form (x : form) = if is_var x
    then print_string (dest_var x)
    else match dest_impl x with
        (a, b) -> if is_impl a
            then (print_string "("; print_form a; print_string ") -> "; print_form b)
            else (print_form a; print_string " -> "; print_form b)

let print_thm (t : thm) = if empty (hyp t)
    then (print_string "|- "; print_form (concl t))
    else (implode print_form ", " (hyp t); print_string " |- "; print_form (concl t))

let print_thm_line t = print_thm t ; print_string "\n"

(* PACKAGE FOR GOAL-DIRECTED PROOFS *)

let goal_to_form (asl, c) = List.fold_right mk_impl asl c
let thm_to_form t = List.fold_right mk_impl (hyp t) (concl t)

type goal = form list * form
type justification = thm list -> thm
type goalstate = goal list * thm
type tactic = goal -> goal list * justification

let by (tac : tactic) ((agoals, athm) : goalstate) =
    if empty agoals then failwith "by: list of subgoals is empty, we're done."
    else let (agoal_asl, _) as agoal = List.hd agoals in
        (* Apply tactic to first goal *)
        let (bgoals, bjust) = tac agoal in
            (* Build theorems out of canonical form of subgoals *)
            let bthms = List.map (
                (* Generate theorems & push assumptions to left hand side of sequent *)
                function (bgoal_asl, _) as bgoal -> List.fold_right (
                        fun assump thm -> elim_rule thm (assume assump)
                    ) (List.rev bgoal_asl) (assume (goal_to_form bgoal))
            ) bgoals in
                (* Use newfound theorems to justify next step *)
                let bthm = bjust bthms in
                    (* Reintroduce assumptions from starting subgoal *)
                    let bthm = List.fold_right intro_rule agoal_asl bthm in
                        (* Create explicit implication from first goal *)
                        let athm = intro_rule (goal_to_form agoal) athm in
                            (* Eliminate first goal with justification from tactic, and finish *)
                            (List.append bgoals (List.tl agoals), elim_rule athm bthm)

(* TACTICS WHICH CORRESPOND TO KERNEL RULES *)

let assumption = (
    fun (asl, c) -> if List.mem c asl
        then ([], fun _ -> assume c)
        else failwith("assumption, does not contain the conclusion as hypothesis")
    : tactic)

let intro_tac = (
    fun (asl, c) ->
        let (a, b) = dest_impl c in
            ([(List.append asl [a], b)], fun thms ->
                let bthm = List.find (fun thm -> concl thm = b) thms in
                    intro_rule a bthm)
    : tactic)

let elim_tac = (
    fun a (asl, c) -> 
        let just = (fun thms ->
            let lthm = List.find (fun thm -> concl thm = mk_impl a c) thms in
                let rthm = List.find (fun thm -> concl thm = a) thms in
                    elim_rule lthm rthm
        ) in
            ([ (asl, mk_impl a c); (asl, a) ], just)
    : form -> tactic)

let mk_init g = ([g], assume (goal_to_form g))

(* INTERACTIVE COMMANDS *)

exception QED

let __history__ = ref []

let p (_ : unit) = let (goals, thm) = List.hd (!__history__) in 
    if empty goals
        then raise QED
        else List.hd goals
let g (f : form) = __history__ := [mk_init ([], f)] ; p ()
let e (t : tactic) = __history__ := List.append [by t (List.hd !__history__)] !__history__ ; p ()
let b (_ : unit) = __history__ := List.tl !__history__ ; p ()

let top_thm (_ : unit) = let (_, thm) = List.hd !__history__ in thm
let e_finish (t : tactic) = try let _ = e t in failwith "did not finish" with QED -> print_thm_line (top_thm ()) ;;

(* Tests *)

let a = mk_var "a"
let c = mk_var "c"

;;

g (mk_impl a a) ;;
e intro_tac ;;
e_finish assumption ;;

g (goal_to_form ([a; mk_impl a c], c)) ;;
e intro_tac ;;
e intro_tac ;;
e (elim_tac a) ;;
e assumption ;;
e_finish assumption ;;
