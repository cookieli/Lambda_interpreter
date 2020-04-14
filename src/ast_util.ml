open Flags
open Core

exception Unimplemented

let fresh s = s ^ "'"

module Type = struct
  open Ast.Type

  let rec substitute_map (rename : t String.Map.t) (tau : t) : t =
    match tau with
    | Num -> Num
    (* Add more cases here! *)
    | Var v ->
       (match String.Map.find rename v with 
        | None -> Var v
        | Some n_v -> n_v)
    | Bool -> Bool
    | Unit -> Unit
    | Fn {arg; ret} ->
       Fn {arg =(substitute_map rename arg); ret =substitute_map rename ret}
    | Product {left; right} ->
        Product {left=(substitute_map rename left); right = (substitute_map rename right)}
    | Sum {left; right} ->
        Sum {left=(substitute_map rename left); right = (substitute_map rename right)}
    | Rec {a; tau} ->
       (match String.Map.find rename a with 
       | None ->
          Rec {a; tau =substitute_map rename tau}
       | _ -> tau)
    | Forall {a; tau} ->
        (match String.Map.find rename a with 
         | None ->
             Forall {a; tau =substitute_map rename tau}
         | _ -> tau)
    | Exists {a; tau} ->
       (match String.Map.find rename a with 
         | None ->
             Exists {a; tau =substitute_map rename tau}
         | _ -> tau) 

  let substitute (x : string) (tau' : t) (tau : t) : t =
    substitute_map (String.Map.singleton x tau') tau

  let rec to_debruijn (tau : t) : t =
    let rec aux (depth : int String.Map.t) (tau : t) : t =
      match tau with
      | Num -> Num
      (* Add more cases here! *)
      | Bool -> Bool
      | Fn {arg; ret}   -> Fn {arg=(aux depth arg); ret= (aux depth ret)}
      | Unit -> Unit
      | Var v -> 
        (match String.Map.find depth v with
        | None -> tau
        | Some i -> Var(Int.to_string i))

      | Product {left; right} ->
        Product {left = aux depth left; right = aux depth right}

      | Sum {left; right} ->
        Sum {left = aux depth left; right = aux depth right}

      | Rec {a; tau} ->
        let new_depth = (String.Map.map depth (fun v ->(+) 1 v)) in 
         let new_depth' =String.Map.set new_depth a 0 in 
           Rec {a="_";tau= aux new_depth' tau}

      | Forall {a; tau} ->
        let new_depth = (String.Map.map depth (fun v ->(+) 1 v)) in 
          let new_depth' =String.Map.set new_depth a 0 in 
           Forall {a="_";tau= aux new_depth' tau}

      | Exists {a; tau} ->
         let new_depth = (String.Map.map depth (fun v ->(+) 1 v)) in 
          let new_depth' =String.Map.set new_depth a 0 in 
           Exists {a="_";tau= aux new_depth' tau}
          
    in
    aux String.Map.empty tau

  let rec aequiv (tau1 : t) (tau2 : t) : bool =
    let rec aux (tau1 : t) (tau2 : t) : bool =
      match (tau1, tau2) with
      | (Num, Num) -> true
      | (Bool, Bool) | (Unit, Unit) -> true
      | (Var x, Var y) -> x = y
      | (Fn x, Fn y) -> aux x.arg y.arg && aux x.ret y.ret
      | (Sum x, Sum y) -> aux x.left y.left && aux x.right y.right
      | (Product x, Product y) -> aux x.left y.left && aux x.right y.right
      | (Rec x, Rec y) -> aux x.tau y.tau
      | (Forall x, Forall y) -> aux x.tau y.tau
      | (Exists x, Exists y) -> aux x.tau y.tau
      | _ -> false
    in
    aux (to_debruijn tau1) (to_debruijn tau2)

  let inline_tests () =
    let p = Parser.parse_type_exn in

    assert (
      aequiv
        (substitute "a" (p "num") (p "forall b . a"))
        (p "forall a . num"));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . a"))
        (p "forall b . b")));
    assert (
      aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall q . forall c . b"));
    assert (
      not (aequiv
        (substitute "a" (p "b") (p "forall b . forall b . a"))
        (p "forall a . forall b . a")));

    assert (aequiv (p "forall a . a") (p "forall b . b"));
    assert (not (aequiv (p "forall a . a") (p "forall b . num")));
    assert (aequiv
              (p "forall a . forall b . a -> b")
              (p "forall x . forall y . x -> y"))

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end

module Expr = struct
  open Ast.Expr

  let rec substitute_map (rename : t String.Map.t) (e : t) : t =
    match e with
    | Num _ -> e
    | Binop {binop; left; right} -> Binop {
      binop;
      left = substitute_map rename left;
      right = substitute_map rename right}
    | (True | False) as t -> t 
    | Relop {relop; left; right} ->
       Relop {relop; left = substitute_map rename left; 
                    right = substitute_map rename right}
    | And {left; right} ->
       And {left = substitute_map rename left;
            right = substitute_map rename right}
    | Or {left; right} ->
       Or {left = substitute_map rename left;
           right = substitute_map rename right}

    | If {cond; then_; else_} ->
       If {cond = (substitute_map rename cond); 
          then_ = (substitute_map rename then_); 
          else_ = (substitute_map rename else_)}

    | Var v ->
      (match String.Map.find rename v with 
        | None -> Var v
        | Some n_v -> n_v)

    | Lam {x; tau; e = e'} -> 
       let rename = (String.Map.set rename x (Var (fresh x))) in 
          Lam {x=(fresh x); tau; e = substitute_map rename e'}
    
    | App {lam; arg} ->
       App {lam =substitute_map rename lam; arg= (substitute_map rename arg)}

    | Unit -> Unit

    | Pair {left; right} ->
       Pair {left = substitute_map rename left; right = substitute_map rename right}

    | Project {e; d} -> 
       Project {e = substitute_map rename e; d}

    | Inject {e; d; tau} ->
       Inject {e = substitute_map rename e; d; tau}

    | Case {e; xleft; eleft; xright ; eright} ->
       let eleft' = (match String.Map.find rename xleft with 
         | None -> substitute_map rename eleft
         | Some _ -> eleft) in 
         let eright' = (match String.Map.find rename xright with
            | None -> substitute_map rename eright
            | Some _ -> eright) in 
            Case {e =substitute_map rename e; xleft; eleft=eleft'; xright; eright=eright'}

    | Fix {x; tau; e} ->
       (match String.Map.find rename x with
       | None -> Fix {x; tau; e =substitute_map rename e}
       | Some _ -> Fix {x; tau; e})

    | TyApp {e; tau} ->
        TyApp {e =substitute_map rename e; tau}

    | TyLam {a; e} ->
       (match String.Map.find rename a with 
       | None -> 
          TyLam {a; e = substitute_map rename e}
       | Some _ -> TyLam {a; e})

    | Fold_ {e; tau} ->
      Fold_ {e = substitute_map rename e; tau}

    | Unfold t -> Unfold (substitute_map rename t)

    | Export {e; tau_adt; tau_mod} ->
       Export {e = substitute_map rename e; tau_adt; tau_mod}
    | Import {x; a; e_mod; e_body} -> 
       Import {x; a; e_mod =substitute_map rename e_mod; e_body}

    (* Put more cases here! *)
  let substitute (x : string) (e' : t) (e : t) : t =
    substitute_map (String.Map.singleton x e') e

  let rec to_debruijn (e : t) : t =
    let rec aux (depth : int String.Map.t) (e : t) : t =
      match e with
      | Num _ -> e
      | Binop {binop; left; right} -> Binop {
        binop; left = aux depth left; right = aux depth right}
      (* Add more cases here! *)
      | True -> True
      | False -> False 
      | If {cond; then_; else_} ->
         If {cond = (aux depth cond); then_ =(aux depth then_); else_= (aux depth else_)}
      | Relop {relop; left;right;} ->
          Relop {relop; left = (aux depth left); right = (aux depth right)}
      | And {left; right} -> 
         And {left = aux depth left; right = aux depth right}
      | Or {left; right} ->
         Or {left = aux depth left; right = aux depth right}
      | Var v ->
         (match String.Map.find depth v with 
         | None -> Var "_"
         | Some i -> Var (Int.to_string i))
      | Lam {x; tau; e} ->
         let depth = (String.Map.map depth (fun v-> (+) 1 v)) in 
           let depth = (String.Map.set depth x 0) in 
            Lam {x="_"; tau; e= aux depth e }
      | App {lam; arg} ->
         App {lam = aux depth lam; arg = aux depth arg}
      | Unit -> Unit
      | Pair {left; right} ->
         Pair {left = aux depth left; right = aux depth right}
      | Project {e; d} ->
        Project {e = aux depth e; d}
      | Inject {e; d; tau} ->
        Inject {e = aux depth e; d; tau}
      | Case {e; xleft; eleft; xright; eright} ->
         let depth' = (String.Map.map depth (fun v-> (+) 1 v)) in 
           let l_depth = (String.Map.set depth' xleft 0) in 
             let r_depth = (String.Map.set depth' xright 0 ) in 
               Case {e = aux depth e; 
                    xleft="_"; eleft = aux l_depth eleft; 
                    xright="_"; eright = aux r_depth eright}
      | Fix {x; tau; e} ->
         let depth' = (String.Map.map depth (fun v->(+) 1 v)) in 
            let depth = (String.Map.set depth' x 0) in 
               Fix {x = "_"; tau; e = aux depth e}
      | TyLam {a; e} ->
         let depth' = (String.Map.map depth (fun v->(+) 1 v)) in 
           let depth = (String.Map.set depth' a 0) in 
             TyLam {a= "_"; e=aux depth e}

      | TyApp {e; tau} ->
         TyApp {e; tau}

      | Fold_ {e; tau} ->
        Fold_ {e = aux depth e; tau}

      | Unfold t -> Unfold t

      | _ -> raise Unimplemented
    in
    aux String.Map.empty e

  let aequiv (e1 : t) (e2 : t) : bool =
    let rec aux (e1 : t) (e2 : t) : bool =
      match (e1, e2) with
      | (Num n1, Num n2) -> n1 = n2
      | (Var x, Var y) -> x = y
      | (Binop l, Binop r) ->
        l.binop = r.binop && aux l.left r.left && aux l.right r.right
      | (True, True) | (False, False) -> true
      | (If l, If r) ->
        aux l.cond r.cond && aux l.then_ r.then_ && aux l.else_ r.else_
      | (Relop l, Relop r) ->
        l.relop = r.relop && aux l.left r.left && aux l.right r.right
      | (And l, And r) ->
        aux l.left r.left && aux l.right r.right
      | (Or l, Or r) ->
        aux l.left r.left && aux l.right r.right
      | (Lam l, Lam r) ->
        aux l.e r.e
      | (App l, App r) ->
        aux l.lam r.lam && aux l.arg r.arg
      | (Unit, Unit) -> true
      | (Pair l, Pair r) ->
        aux l.left r.left && aux l.right r.right
      | (Project l, Project r) ->
        aux l.e r.e && l.d = r.d
      | (Inject l, Inject r) ->
        aux l.e r.e && l.d = r.d
      | (Case l, Case r) ->
        aux l.e r.e && aux l.eleft r.eleft && aux l.eright r.eright
      | (Fix l, Fix r) -> aux l.e r.e
      | (TyLam l, TyLam r) ->
        aux l.e r.e
      | (TyApp l, TyApp r) -> aux l.e r.e
      | (Fold_ l, Fold_ r) -> aux l.e r.e
      | (Unfold l, Unfold r) -> aux l r
      | (Export l, Export r) -> aux l.e r.e
      | (Import l, Import r) -> aux l.e_mod r.e_mod && aux l.e_body r.e_body
      | _ -> false
    in
    aux (to_debruijn e1) (to_debruijn e2)

  let inline_tests () =
    let p = Parser.parse_expr_exn in
    let t1 = p "(fun (x : num) -> x) y" in
    assert (aequiv (substitute "x" (Num 0) t1) t1);
    assert (aequiv (substitute "y" (Num 0) t1)
              (p "(fun (x : num) -> x) 0"));

    let t2 = p "x + (fun (x : num) -> y)" in
    assert (aequiv
              (substitute "x" (Num 0) t2)
              (p "0 + (fun (x : num) -> y)"));
    assert (aequiv (substitute "y" (Num 0) t2)
              (p "x + (fun (x : num) -> 0)"));

    assert (aequiv (p "fun (x : num) -> x") (p "fun (y : num) -> y"));

    assert (not (aequiv (p "fun (x : num) -> fun (x : num) -> x + x")
                   (p "fun (x : num) -> fun (y : num) -> y + x")));

    assert (
      aequiv
        (p "tyfun a -> fun (x : a) -> x")
        (p "tyfun b -> fun (x : b) -> x"));

    ()

  (* Uncomment the line below when you want to run the inline tests. *)
  (* let () = inline_tests () *)
end
