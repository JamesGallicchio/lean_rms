import data.vector
import data.vector2
import data.fin
import data.nat.pairing
import data.nat.log
import logic.function.iterate

/- for printing out register machines reasonably. should be autoderived but ?? whatever -/
instance {α : Type*} [has_repr α] {len : ℕ} : has_repr (vector α len)
  := {repr := λ v, repr v.to_list}

lemma vector.update_nth_eq_if {α : Type*} {len : ℕ} {v : vector α len}
    {i : fin len} {elem : α} (h : v.nth i = elem)
  : (v.update_nth i elem) = v
  := begin
    refine vector.ext _,
    assume m,
    rw vector.nth_update_nth_eq_if,
    rw ← h,
    sorry
  end

namespace regmachine

/-  inc r l    ->  increment r and jump to l
    dec r l k  ->  if (r) > 0 then decrement r and jump to l, else jump to k
    jump to halt represented by none instead of a line number
 -/
inductive instr (rc ic : ℕ)
| inc  : fin rc → option (fin ic) → instr
| dec  : fin rc → option (fin ic) → option (fin ic) → instr

namespace instr
variables {rc ic : ℕ}
  def map_regs {rc' : ℕ} (f : fin rc → fin rc')
    : instr rc ic → instr rc' ic
    | (instr.inc r l)   := instr.inc (f r) l
    | (instr.dec r l k) := instr.dec (f r) l k

  def map_locs {ic' : ℕ} (f : option (fin ic) → option (fin ic'))
    : instr rc ic → instr rc ic'
    | (instr.inc r l)   := instr.inc r (f l)
    | (instr.dec r l k) := instr.dec r (f l) (f k)
end instr

/- state consists of an instruction pointer and the registers.
   if ip is none then machine is halted. -/
structure state (rc ic : ℕ) := (ip : option (fin ic)) (regs : vector ℕ rc)
namespace state
  def is_halted {rc ic : ℕ} (s : state rc ic) := s.ip = none
end state

/- register machine with rc registers and ic instructions -/
def rm (rc ic : ℕ)
  := vector (instr rc ic) ic

namespace rm
  variables {rc ic : ℕ}

  section variable (M : rm rc ic)
  def extend {n : ℕ} : rm (rc+n) ic
    := M.map (instr.map_regs (fin.cast_add n))

  def append {ic' : ℕ} (M' : rm rc ic'.succ)
    : rm rc (ic + ic'.succ)
    := vector.append
        (M.map (instr.map_locs (λ l, match l with
          | some l' := some (fin.cast_add ic' l')
          | none := some ic
          end)))
        (M'.map (instr.map_locs (λ l, match l with
          | some l' := some (ic + l')
          | none := none
          end)))

  /- most important definition here! gives semantics to those incs and decs :) -/
  def step (c : state rc ic) : state rc ic :=
    match c.ip with
    | none := c
    | some ip :=
      match M.nth ip with
      | instr.inc r l := {ip := l, regs := c.regs.update_nth r (c.regs.nth r + 1)}
      | instr.dec r l k :=
          match c.regs.nth r with
          | p + 1 := {ip := l, regs := c.regs.update_nth r p}
          | 0 := {ip := k, regs := c.regs}
          end
      end
    end

  end

  /- a configuration for M is just a state.
      used to store M at the type level. -/
  structure conf (M : rm rc ic) := (s : state rc ic)
  @[simp]
  def mk_conf (M : rm rc ic) (s : state rc ic) : M.conf := {s := s}

  namespace conf
    variables {M : rm rc ic} (c : M.conf)

    def steps_to (d : M.conf) :=
      ∃ (t : ℕ), (M.step)^[t] c.s = d.s

    notation c `==>` d := c.steps_to d

    theorem steps_to_trans (c d e : M.conf)
      (pf1 : c ==> d) (pf2 : d ==> e) : c ==> e
      := begin
        cases pf1,
        cases pf2,
        use pf2_w + pf1_w,
        simp [function.iterate_add],
        rw pf1_h,
        exact pf2_h
      end

  end conf

  open conf

  /- generate an initial configuration with some input in the first
    register and 0 elsewhere -/
  def init (M : rm rc.succ ic.succ) (input : ℕ) : M.conf
    := conf.mk {ip := some 0, regs := input ::ᵥ vector.repeat 0 rc}

  def computes (M : rm rc.succ ic.succ) (f : ℕ → ℕ)
    := ∀ (n : ℕ), ∃ (d : M.conf), (M.init n ==> d) ∧ (d.s.regs.nth 0 = f n)

end rm

namespace macros
variables {rc ic : ℕ}

  open instr
  open rm

  def rst (r : fin rc) : rm rc 1 := ⟨[
    dec r (some 0) none
  ], rfl⟩

  lemma rst_step (r : fin rc) {n : ℕ} {regs : vector ℕ rc} {h : regs.nth r = n.succ}
    : (rst r).step {ip := some 0, regs := regs} =
      {ip := some 0, regs := regs.update_nth r n}
    := begin
      simp [rst, step, vector.head],
      rw h,
      simpa
    end

  theorem rst_effect {r : fin rc} {n : ℕ} {regs : vector ℕ rc} {h : regs.nth r = n}
    : (rst r).mk_conf {ip := some 0, regs := regs} ==>
      conf.mk {ip := none, regs := regs.update_nth r 0}
    := begin
      rw conf.steps_to,
      use n.succ,
      simp,
      induction n,
      simp [nat.iterate, step, vector.head, rst],
      rw h,
      rw vector.update_nth_eq_if,
      simp [step],
      exact h,
      sorry
    end

  def mov (_from _to : fin rc) : rm rc 2 := ⟨[
    dec _from (some 1) none,
    inc _to (some 0)
  ], rfl⟩
  
  theorem mov_effect {_from _to : fin rc} {rs : vector ℕ rc} {p : _from ≠ _to}
    : (mov _from _to).mk_conf {ip := some 0, regs := rs} ==>
      conf.mk {ip := none, regs := (rs.update_nth _from 0).update_nth _to (rs.nth _from + rs.nth _to)}
    := begin
      sorry
    end

end macros

end regmachine