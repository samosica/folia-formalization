(* -- Converted from Coq -- *)

type __ = Obj.t

type bool =
| True
| False



type reflect =
| ReflectT
| ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op m =
    m.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT
 end

(** val belast : 'a1 -> 'a1 list -> 'a1 list **)

let rec belast x = function
| [] -> []
| x' :: s' -> x :: (belast x' s')

(** val foldr :
    ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val sumn : int list -> int **)

let sumn =
  foldr ( + ) 0

(** val scanl :
    ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 list **)

let rec scanl g x = function
| [] -> []
| y :: s' -> let x' = g x y in x' :: (scanl g x' s')

(** val map2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f s1 s2 =
  match s1 with
  | [] -> []
  | x :: s1' ->
    (match s2 with
     | [] -> []
     | y :: s2' -> (f x y) :: (map2 f s1' s2'))

(** val scanr :
    ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 list **)

let rec scanr f y0 = function
| [] -> y0 :: []
| x :: s' ->
  let r = scanr f y0 s' in
  (match r with
   | [] -> assert false (* absurd case *)
   | y :: _ -> (f x y) :: r)

type leave_spec = int list

(** val lower_bound_bottomup : leave_spec -> int **)

let lower_bound_bottomup s =
  foldr (fun l0 lb -> ( + ) l0 ((fun n -> (n + 1) / 2) lb))
    0 s

(** val upper_bounds_topdown :
    leave_spec -> int -> int list **)

let upper_bounds_topdown s n =
  belast n
    (scanl (fun ub l0 -> (fun n -> n * 2) (( - ) ub l0)) n s)

(** val upper_bounds_bottomup : int list -> int list **)

let upper_bounds_bottomup s =
  scanr ( + ) 0 s

(** val upper_bounds_backforth' :
    int list -> int -> int list **)

let upper_bounds_backforth' s n =
  map2 min (upper_bounds_bottomup s)
    (upper_bounds_topdown s n)

(** val upper_bound_total' : int list -> int -> int **)

let upper_bound_total' s n =
  sumn (upper_bounds_backforth' s n)
(* ------------------------ *)

let solve n a =
  if lower_bound_bottomup a = 1 then
    upper_bound_total' a 1
  else
    -1

let n = Scanf.scanf " %d" Fun.id
let a = List.init (n + 1) (fun _ -> Scanf.scanf " %d" Fun.id)
let () = Printf.printf "%d\n" (solve n a)
