
namespace sml

namespace type

def repr : type → string
| (arrow τ₁ τ₂) := string.join ["arrow (", repr τ₁, ") (", repr τ₂, ")"]

instance : has_repr type := ⟨repr⟩

end type

@[derive decidable_eq]
inductive term : Type
| lambda : type → term → term
| app : term → term → term
| var : ℕ → term

namespace term
open type

def synthtype : term → list type → option type
| (lambda τ e) := λ c,
  let c' := τ :: c in
  (synthtype e c').bind (λ τ₁, arrow τ τ₁)
| (app f e) := λ c,
  match (synthtype f c, synthtype e c) with
  | (some (arrow τ τ₁), some τ') :=
      ite (τ = τ') (some τ₁) none
  | _ := none
  end
| (var n) := λ c, c.nth n
| star := λ _, some unit

#eval synthtype (lambda bool (var 0)) []

def hastype (e : term) (t : type) := synthtype e [] = some t

def typechecks (e : term) := ∃ (t : type), hastype e t

def steps_to (e1 : term) (e2 : term) : Prop
  := 

end term

end sml