import Mathlib.Logic.Relation
import Mathlib.Computability.Encoding
import Mathlib.Data.PFun
import Std

unsafe instance [Fintype D] [Repr D] [Repr C] : Repr (D → C) where
  reprPrec f prec :=
    let ds : List D := Fintype.elems.val.lift id (unsafeCast ())
    open Std.Format in
    group <| nest 2 <| "fun " ++ align false ++ (
      ds.map (fun d => "| " ++ reprPrec d prec ++ " => " ++ reprPrec (f d) prec)
      |>.intersperse line
      |> join
      )

@[simp] theorem Option.isNone_eq_true (o : Option α)
  : o.isNone = true ↔ o = none
  := by cases o <;> simp
