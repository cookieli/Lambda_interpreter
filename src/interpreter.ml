open Flags
open Core
open Ast

type outcome =
  | Step of Expr.t
  | Val

exception RuntimeError of string

let rec trystep (e : Expr.t) : outcome =
  (* Printf.printf "expr: %s \n" (Expr.to_string e) ; *)
  match e with
  | (Expr.Lam _ | Expr.Num _ | Expr.True | Expr.False | Expr.Pair _ | Expr.Unit
    | Expr.Inject _ | Expr.TyLam _ | Expr.Export _ | Expr.Fold_ _) ->
     (* Printf.printf "in val \n"; *)
     Val

  | Expr.Binop {binop; left; right} ->
     (left, fun left' -> Expr.Binop {left = left'; binop; right}) |-> fun () -> 
     (right, fun right' -> Expr.Binop {left; binop; right = right'}) |-> fun () ->
     let (Expr.Num l, Expr.Num r) = (left, right) in 
       let f = match binop with 
       | Add -> (+)
       | Sub -> (-)
       | Mul -> ( * )
       | Div -> (/)
       in 
       Step (Expr.Num (f l r))

  | Expr.And {left; right} ->
     (left, fun left' -> Expr.And {left = left'; right}) |-> fun () ->
     if Ast_util.Expr.aequiv left Expr.False then Step Expr.False else 
     (right, fun right' -> Expr.And{right = right'; left}) |-> fun () ->
     if Ast_util.Expr.aequiv right Expr.False then Step Expr.False else 
     Step Expr.True

  | Expr.Or {left; right} ->
     (left, fun left' -> Expr.Or {left = left'; right}) |-> fun () ->
     if Ast_util.Expr.aequiv left Expr.True then Step Expr.True else 
     (right, fun right' -> Expr.Or{right = right'; left}) |-> fun () ->
     if Ast_util.Expr.aequiv right Expr.True then Step Expr.True else 
      Step Expr.False
  
  | Expr.Relop {relop; left; right} ->
     (left, fun left' -> Expr.Relop {left = left'; relop; right}) |-> fun () ->
     (right, fun right' -> Expr.Relop {right = right'; relop; left}) |-> fun () ->
     let (Expr.Num l, Expr.Num r) = (left, right) in 
       let f = match relop with 
       | Gt -> (>)
       | Lt -> (<)
       | Eq -> (=)
       in 
       if (f l r) then Step Expr.True else Step Expr.False
  | Expr.If {cond; then_; else_} ->
    (* Printf.printf "if:%s\n" (Expr.to_string e); *)
    (* raise (RuntimeError (Printf.sprintf "error")) *)
    (cond, fun cond' -> Expr.If {cond = cond'; then_; else_}) |-> fun () ->
      (* Printf.printf "%s\n" (Expr.to_string cond); *)
    if (Ast_util.Expr.aequiv Expr.True cond) then Step then_ else 
    (* let () =  Printf.printf "%s\n" (Expr.to_string else_) in  *)
    Step else_
    (* raise (RuntimeError (Printf.sprintf "error")); *)
  (* Add more cases here *)

  | Expr.App {lam; arg} -> 
    (* Printf.printf "in app\n"; *)
    (match lam with 
    | Expr.Fix{x;tau; _} ->
      (* Printf.printf "%s\n" (Expr.to_string e); *)
      let Step f = trystep lam in
         (* Printf.printf "f: %s\n" (Expr.to_string f); *)
        let Expr.Fix {x=new_x; tau=tau'; e = new_e} = f in 
         (* let ()= Printf.printf "new_e: %s\n" (Expr.to_string new_e) in *)
          (* raise (RuntimeError (Printf.sprintf "error")); *)
          Step (Expr.App {lam=new_e; arg} )
    | _ -> 
         (* Printf.printf "app of fun expr: %s \n" (Expr.to_string e); *)
         (lam, fun lam' -> Expr.App {lam = lam'; arg}) |-> fun () ->
           let Expr.Lam {x; tau; e=e'} = lam  in 
           (* let () = Printf.printf "lam : %s\n" (Expr.to_string lam) in
           let () = Printf.printf "arg: %s\n" (Expr.to_string arg) in
           let () = Printf.printf "lam body:%s\n" (Expr.to_string e') in *)
            (* let () = Printf.printf "app of lam: %s\n" (Expr.to_string e) in
              let () = Printf.printf "lam body: %s" (Expr.to_string e') in
             let new_e = Ast_util.Expr.substitute x arg e' in 
             let () = Printf.printf "after substitude: %s\n" (Expr.to_string new_e) in  *)
             Step (Ast_util.Expr.substitute x arg e'))

  
  | Expr.Project {e; d} ->
    (e, fun e' -> Expr.Project {e=e'; d}) |-> fun () ->
      let Expr.Pair{left; right} = e in 
        (match d with 
        | Expr.Left -> Step left
        | Expr.Right -> Step right)
  
  | Expr.Case {e; xleft; eleft; xright; eright} ->
    (e, fun e' -> Expr.Case {e= e'; xleft; eleft; xright; eright}) |-> fun () ->
     let Expr.Inject {e=e'; d; tau} = e  in 
     (match d with 
     | Expr.Left -> Step (Ast_util.Expr.substitute xleft e' eleft)
     | Expr.Right-> Step (Ast_util.Expr.substitute xright e' eright))

  | Expr.Fix {x; tau; e = new_e} -> 
    (* Printf.printf "in fix: %s var: %s expr: %s\n" (Expr.to_string e) (x) (Expr.to_string new_e); *)
    let new_fix = (Expr.Fix {x; tau; e = Ast_util.Expr.substitute x e new_e}) in
      (* let () = Printf.printf "new fix: %s\n" (Expr.to_string new_fix) in *)
      Step new_fix
      (* raise (RuntimeError (Printf.sprintf "error")); *)

  | Expr.TyApp {e; tau} ->
    (e, fun e' -> Expr.TyApp {e=e'; tau}) |-> fun () ->
       let Expr.TyLam {a; e= lam_e} = e in 
        Step lam_e
  
  | Expr.Unfold t ->
       (t, fun t' -> Expr.Unfold t') |-> fun () ->
         (* let () = Printf.printf "unfold: %s\n" (Expr.to_string t) in  *)
         (match t with 
         | Expr.Fold_ {e; tau} -> Step e
         | Expr.Export {e; tau_adt; tau_mod} ->
            Step (Expr.Unfold e)
         | _ ->
            raise (RuntimeError (
              Printf.sprintf "unfold: %s\n" (Expr.to_string t)
            )))
  | Expr.Import {x; a; e_mod; e_body} ->
      (* Printf.printf "Import: %s\n" (Expr.to_string e); *)
      (e_mod, fun e_mod' -> Expr.Import {x; a; e_mod=e_mod'; e_body}) |-> fun () ->
       Step (Ast_util.Expr.substitute x e_mod e_body)

  | _ -> raise (RuntimeError (
    Printf.sprintf "Reached a stuck state at expression: %s" (Expr.to_string e)))

and (|->) ((e, hole) : Expr.t * (Expr.t -> Expr.t)) (next : unit -> outcome)
  : outcome =
  match trystep e with Step e' -> Step (hole e') | Val -> next ()

let rec eval e =
  match trystep e with
  | Step e' ->
    (if extra_verbose () then
       Printf.printf "Stepped:\n%s\n|->\n%s\n\n"
         (Expr.to_string e) (Expr.to_string e'));
    eval e'
  | Val -> Ok e

let inline_tests () =
  let p = Parser.parse_expr_exn in
  let e1 = p "2 + 3" in
  assert (trystep e1 = Step(Expr.Num 5));

  let e2 = p "(fun (x : num) -> x) 3" in
  assert (trystep e2 = Step(Expr.Num 3))

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)
