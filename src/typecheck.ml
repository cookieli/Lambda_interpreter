open Flags
open Core
open Result.Monad_infix
open Ast

exception Unimplemented

let rec typecheck_expr (ctx : Type.t String.Map.t) (e : Expr.t)
  : (Type.t, string) Result.t =
  match e with
  | Expr.Num _ -> Ok Type.Num
  | Expr.Unit -> Ok Type.Unit
  | Expr.Binop {binop;left; right;} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match (tau_left, tau_right) with
     | (Type.Num, Type.Num) -> Ok Type.Num
     | _ -> Error (
       Printf.sprintf
         "Binary operands have incompatible types: (%s : %s) and (%s : %s)"
         (Expr.to_string left) (Type.to_string tau_left)
         (Expr.to_string right) (Type.to_string tau_right)))

  (* Add more cases here! *)
  | Expr.True | Expr.False -> Ok Type.Bool
  | Expr.And {left; right} | Expr.Or {left; right}-> 
     typecheck_expr ctx left >>= fun tau_left ->
     typecheck_expr ctx right >>= fun tau_right ->
     (match (tau_left, tau_right) with 
     | (Type.Bool, Type.Bool) -> Ok Type.Bool
     | _ -> Error (Printf.sprintf
                  "And _ Or operands have incompatible types (%s: %s) and (%s: %s)"
                  (Expr.to_string left) (Type.to_string tau_left)
                  (Expr.to_string right) (Type.to_string tau_right)))
  | Expr.Relop {left; right; _} ->
    typecheck_expr ctx left >>= fun tau_left ->
    typecheck_expr ctx right >>= fun tau_right ->
    (match tau_left, tau_right with
     | (Type.Num, Type.Num) -> Ok Type.Bool
     | _ -> Error (Printf.sprintf
                  "Relation ops have incompatible types (%s: %s) and (%s: %s)"
                  (Expr.to_string left) (Type.to_string tau_left)
                  (Expr.to_string right) (Type.to_string tau_right)))
  | Expr.If {cond;then_; else_}->
  typecheck_expr ctx cond >>= fun tau_cond ->
  typecheck_expr ctx then_ >>= fun tau_then ->
  typecheck_expr ctx else_ >>= fun tau_else ->
  (match tau_cond with 
  | Type.Bool -> 
       if Ast_util.Type.aequiv tau_then tau_else then Ok tau_else
       else Error (
         Printf.sprintf 
         "If then else have imcompatible types then:(%s: %s) else (%s: %s)"
         (Expr.to_string then_) (Type.to_string tau_then) 
         (Expr.to_string else_) (Type.to_string tau_else)
       )
  | _   -> Error (
    Printf.sprintf 
    "If experiment cond type not bool (%s: %s)"
    (Expr.to_string cond) (Type.to_string tau_cond)
  ))

  | Expr.Var v ->
    (match (String.Map.find ctx v) with 
    | None -> Error(
      Printf.sprintf
      "variable %s doesn't match any type"
      v)
    | Some tau -> Ok tau)

  | Expr.Lam{x; tau; e} ->
      let new_map = String.Map.set ctx x tau in 
        typecheck_expr new_map e >>= fun ret_tau ->
        Ok (Type.Fn {arg = tau; ret = ret_tau})
  | Expr.App {lam; arg} ->
      typecheck_expr ctx lam >>= fun fun_tau ->
      (match fun_tau with 
       | Type.Fn {arg=_; ret} ->
        typecheck_expr ctx arg >>= fun arg_tau ->
        if Ast_util.Type.aequiv fun_tau (Type.Fn{arg=arg_tau; ret}) then 
          Ok ret else 
             let arg_tau = (
             match arg_tau with 
             | Type.Rec {a; tau} -> Type.Var a
             | _ -> arg_tau) in 
               if Ast_util.Type.aequiv fun_tau (Type.Fn {arg=arg_tau; ret}) then
                 Ok ret else
               Error (
                 Printf.sprintf "function type are incompatible %s %s,
                 real arg is %s\n"
                 (Type.to_string fun_tau) (Type.to_string (Type.Fn{arg=arg_tau; ret}))
                 (Expr.to_string arg)
               )
       | _ -> Error ("not function type"))

  | Expr.Pair {left; right} ->
     typecheck_expr ctx left >>= 
      fun left_tau -> typecheck_expr ctx right >>=
        fun right_tau -> Ok (Type.Product {left=left_tau; right=right_tau})
  
  | Expr.Project {e; d} ->
    typecheck_expr ctx e >>=
     fun tau ->
       (match tau with 
      | Type.Product {left; right} -> 
         (match d with 
         | Left -> Ok left
         | Right -> Ok right)
      | _ -> Error(Printf.sprintf "It is not product type, it is %s"
                     (Type.to_string tau)))
  | Expr.Inject {e; d; tau} ->
     typecheck_expr ctx e >>=
      fun e_tau ->
       (match tau with
       | Type.Sum {left; right} ->
          (match d with 
          | Expr.Left -> if (Ast_util.Type.aequiv left e_tau)
                            then Ok (Type.Sum {left; right})
                            else Error(
                              Printf.sprintf "injection left type %s not match with right type %s"
                              (Type.to_string left) (Type.to_string e_tau)
                            )
          | Expr.Right -> if (Ast_util.Type.aequiv right e_tau)
                            then Ok (Type.Sum {left; right})
                            else Error(Printf.sprintf "injection right type %s not match with right type %s"
                                     (Type.to_string right) (Type.to_string e_tau)))
       | _ -> Error("not sum type"))

  | Export {e; tau_adt; tau_mod} ->
     (match tau_mod with 
     | Exists {a; tau} ->
       typecheck_expr ctx e >>= fun e_tau ->
       let new_tau = Ast_util.Type.substitute a tau_adt tau in 
        if Ast_util.Type.aequiv e_tau new_tau 
        then Ok tau_mod 
        else Error(
          Printf.sprintf "Export type not match %s %s"
            (Type.to_string e_tau) (Type.to_string new_tau))
     | _ -> 
       Error(
         Printf.sprintf "Export has not a export type: %s"
         (Type.to_string tau_mod)
       ))

  | Import {x; a; e_mod; e_body} ->
     typecheck_expr ctx e_mod >>= fun e_tau ->
     ( match e_tau with 
      | Exists {a=a'; tau=tau_mod} ->
         let new_tau = Ast_util.Type.substitute a' (Var a) tau_mod in 
         let ctx = String.Map.set ctx x new_tau in 
           typecheck_expr ctx e_body >>= fun tau_body ->
             Ok tau_body
      | _ ->
         Error (
           Printf.sprintf "emod not existence type : %s"
           (Type.to_string e_tau)
         )
     )
  | Expr.Case {e; xleft; eleft; xright; eright} ->
     typecheck_expr ctx e >>=
      fun e_tau ->
        (match e_tau with 
         | Type.Sum {left; right} -> 
           let new_ctx0 = String.Map.set ctx xleft left in 
            typecheck_expr new_ctx0 eleft >>= fun left_tau ->
              let new_ctx1 = String.Map.set ctx xright right in 
               typecheck_expr new_ctx1 eright >>= fun right_tau ->
                 if Ast_util.Type.aequiv left_tau right_tau 
                  then Ok left_tau 
                  else Error (
                    Printf.sprintf "case left expr %s: %s right expr %s: %s not equal"
                    (Expr.to_string eleft) (Type.to_string left_tau) 
                    (Expr.to_string eright) (Type.to_string right_tau)
                  )
         | _ -> Error(
           Printf.sprintf " expr %s not sum type %s" 
            (Expr.to_string e) (Type.to_string e_tau))
        )
  | Expr.Fix {x; tau; e} ->
    let new_ctx = String.Map.set ctx x tau  in 
       typecheck_expr new_ctx e 
  | Expr.TyLam {a; e=e'} ->
      (* Printf.printf "tylam: %s\n" (Expr.to_string e); *)
      typecheck_expr ctx e' >>= fun tau ->
      Ok (Type.Forall {a; tau})
  | Expr.TyApp {e=e'; tau} ->
     (* Printf.printf "tyApp: %s\n" (Expr.to_string e); *)
     typecheck_expr ctx e' >>= fun tau' ->
     (* Printf.printf "app type: %s\n" (Type.to_string tau'); *)
     (match tau' with 
     | Type.Forall {a; tau= tau_body} ->
         Ok (Ast_util.Type.substitute a tau tau_body)
     | _ -> Error(
            Printf.sprintf "It is not for all type and can't be app: %s: %s"
            (Expr.to_string e) (Type.to_string tau')))
  
  | Expr.Fold_ {e; tau} ->
     typecheck_expr ctx e >>= fun e_tau ->
      (match tau with 
       | Rec {a; tau=tau'} -> 
          let new_tau = (Ast_util.Type.substitute a tau tau') in 
           if (Ast_util.Type.aequiv new_tau e_tau) then Ok tau 
           else  Error (
             Printf.sprintf "two rec types not equals: %s %s"
             (Type.to_string new_tau) (Type.to_string e_tau)
           )
       | _ -> Error (
         Printf.sprintf "this expr doesn't have fold type: %s: %s"
          (Expr.to_string e) (Type.to_string tau)
       ))

  | Expr.Unfold t ->
     typecheck_expr ctx t >>= fun e_tau ->
      (match e_tau with 
        | Rec {a; tau} ->
          Ok (Ast_util.Type.substitute a e_tau tau)
        | _ -> Error(
          Printf.sprintf "this expr doesn't have rec types: %s: %s"
           (Expr.to_string t) (Type.to_string e_tau)))

let typecheck t = typecheck_expr String.Map.empty t

let inline_tests () =
  let p_ex = Parser.parse_expr_exn in
  let p_ty = Parser.parse_type_exn in
  let e1 = p_ex "fun (x : num) -> x" in
  assert (typecheck e1 = Ok(p_ty "num -> num"));

  let e2 = p_ex "fun (x : num) -> y" in
  assert (Result.is_error (typecheck e2));

  let t3 = p_ex "(fun (x : num) -> x) 3"in
  assert (typecheck t3 = Ok(p_ty "num"));

  let t4 = p_ex "((fun (x : num) -> x) 3) 3" in
  assert (Result.is_error (typecheck t4));

  let t5 = p_ex "0 + (fun (x : num) -> x)" in
  assert (Result.is_error (typecheck t5))

(* Uncomment the line below when you want to run the inline tests. *)
(* let () = inline_tests () *)
