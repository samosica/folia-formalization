
type __ = Obj.t

type bool =
| True
| False



type reflect =
| ReflectT
| ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val belast : 'a1 -> 'a1 list -> 'a1 list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val sumn : int list -> int

val scanl :
  ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 list

val map2 :
  ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val scanr :
  ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 list

type leave_spec = int list

val lower_bound_bottomup : leave_spec -> int

val upper_bounds_topdown : leave_spec -> int -> int list

val upper_bounds_bottomup : int list -> int list

val upper_bounds_backforth' : int list -> int -> int list

val upper_bound_total' : int list -> int -> int
