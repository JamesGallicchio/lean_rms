import data.vector
import data.vector2
import data.fin
import data.nat.pairing
import data.nat.log
import logic.function.iterate

/- for printing out register machines reasonably. should be autoderived but ?? whatever -/
instance {α : Type*} [has_repr α] {len : ℕ} : has_repr (vector α len)
  := {repr := λ v, repr v.to_list}

@[simp]
lemma vector.update_nth_eq_if {α : Type*} {len : ℕ} {v : vector α len}
    {i : fin len} {elem : α} (h : v.nth i = elem)
  : v.update_nth i elem = v
  := begin
    refine vector.ext _,
    assume m,
    rw vector.nth_update_nth_eq_if,
    rw ← h,
    split_ifs,
    simp [h_1]
  end

@[simp]
lemma vector.update_nth_update_nth_same {α : Type*} {len : ℕ} {v : vector α len}
    {i : fin len} {e1 e2 : α}
  : (v.update_nth i e1).update_nth i e2 = v.update_nth i e2
  := begin
    refine vector.ext _,
    assume m,
    by_cases i=m,
    rw h,
    iterate { rw vector.nth_update_nth_same },
    iterate { rw vector.nth_update_nth_of_ne },
    iterate { exact h }
  end

lemma vector.update_nth_comm {α : Type*} {len : ℕ} {v : vector α len}
    {i j : fin len} {e1 e2 : α} (p : i ≠ j)
  : (v.update_nth i e1).update_nth j e2 = (v.update_nth j e2).update_nth i e1
  := begin
    refine vector.ext _,
    assume m,
    by_cases i=m,
    rw h,
    rw vector.nth_update_nth_same,
    rw vector.nth_update_nth_of_ne,
    rw vector.nth_update_nth_same,
    rw ← h,
    exact ne.symm p,
    by_cases j=m,
    rw ← h,
    rw vector.nth_update_nth_same,
    rw vector.nth_update_nth_of_ne,
    rw vector.nth_update_nth_same,
    exact p,
    iterate {rw vector.nth_update_nth_of_ne},
    iterate {simp [*]},
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
  def new_ic {rc ic ic' : ℕ} (s : state rc ic) : state rc (ic+ic') :=
    { ip := s.ip.map (λ l, fin.cast_add ic' l), regs := s.regs }
end state

/- register machine with rc registers and ic instructions -/
def rm (rc ic : ℕ)
  := vector (instr rc ic) ic

/- most important definition here! gives semantics to those incs and decs :) -/
def step {rc ic : ℕ} (M : rm rc ic) (c : state rc ic) : state rc ic :=
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

namespace rm
  variables {rc ic : ℕ}

  /- a configuration for M is just a state.
      used to store M at the type level. -/
  structure conf (M : rm rc ic) := (s : state rc ic)

  @[simp]
  def mk_conf (M : rm rc ic) (s : state rc ic) : M.conf := {s := s}

  namespace conf
    variables {M : rm rc ic} (c : M.conf)

    def steps_to (d : M.conf) :=
      ∃ (t : ℕ), (step M)^[t] c.s = d.s

    notation c `==>` d := c.steps_to d

    lemma step_is_steps_to {c d : state rc ic}
      (pf : step M c = d) : M.mk_conf c ==> conf.mk d
      := begin use 1, simpa end

    lemma steps_to_trans (c d e : M.conf)
      (pf1 : c ==> d) (pf2 : d ==> e) : c ==> e
      := begin
        cases pf1,
        cases pf2,
        use pf2_w + pf1_w,
        simpa [function.iterate_add, pf1_h]
      end

  end conf

  section variable (M : rm rc ic)

  def extend {n : ℕ} : rm (rc+n) ic
    := M.map (instr.map_regs (fin.cast_add n))

  /- joins M with M', one set of instructions
    after the other. allows the "rewiring"
    of the halts in each machine to a new loc
    in the new machine -/
  def join {ic' : ℕ} (M_halt_loc : option (fin (ic + ic')))
          (M' : rm rc ic') (M'_halt_loc : option (fin (ic + ic')))
    : rm rc (ic + ic')
    := vector.append
        (M.map (instr.map_locs (λ lopt, match lopt with
          | some l := some (⟨l.val + ic', begin simpa using l.property end⟩)
          | none := M_halt_loc
          end)))
        (M'.map (instr.map_locs (λ lopt, match lopt with
          | some l := some (⟨ic + l.val, begin simpa using l.property end⟩)
          | none := M'_halt_loc
          end)))

  theorem join_preserves_behavior_fst  {ic' : ℕ} (M_halt_loc  : option (fin (ic + ic')))
          (M' : rm rc ic') (M'_halt_loc : option (fin (ic + ic')))
    : ∀ {c d : M.conf} (h : c ==> d),
        (M.join M_halt_loc M' M'_halt_loc).mk_conf c.s.new_ic ==> conf.mk d.s.new_ic
    := begin sorry end
  
  end

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

  -- sets register r back to 0
  def rst (r : fin rc) : rm rc 1 := ⟨[
    dec r (some 0) none
  ], rfl⟩

  section
  variables {r : fin rc} {regs : vector ℕ rc}

  lemma rst_step_zero (h : regs.nth r = 0)
    : (rst r).mk_conf {ip := some 0, regs := regs} ==>
        conf.mk {ip := none, regs := regs}
    := begin apply conf.step_is_steps_to, simp [step, vector.head, rst, h] end
  
  lemma rst_step_succ {n : ℕ} (h : regs.nth r = n.succ)
    : (rst r).mk_conf {ip := some 0, regs := regs} ==>
        conf.mk {ip := some 0, regs := regs.update_nth r n}
    := begin apply conf.step_is_steps_to, simp [step, vector.head, rst, h] end
  
  theorem rst_effect {r : fin rc} {regs : vector ℕ rc}
    : (rst r).mk_conf {ip := some 0, regs := regs} ==>
      conf.mk {ip := none, regs := regs.update_nth r 0}
    := begin
      induction h : (regs.nth r) generalizing regs,
      simp [step, h],
      exact rst_step_zero h,
      refine rm.conf.steps_to_trans _
        ((rst r).mk_conf {ip := some 0, regs := regs.update_nth r n})
        _ _ _,
      exact rst_step_succ h,
      have : (regs.update_nth r n).nth r = n := vector.nth_update_nth_same _ _ _,
      convert ih this using 3,
      rw vector.update_nth_update_nth_same
    end

  end

  def mov (_from _to : fin rc) : rm rc 2 := ⟨[
    dec _from (some 1) none,
    inc _to (some 0)
  ], rfl⟩
  
  section
  variables {_from _to : fin rc} {regs : vector ℕ rc}

  lemma mov_step_zero (h : regs.nth _from = 0)
    : (mov _from _to).mk_conf {ip := some 0, regs := regs} ==>
        conf.mk {ip := none, regs := regs}
    := begin apply rm.conf.step_is_steps_to, simp [step, vector.head, mov, h] end
  
  lemma mov_step_succ {n_to n_from : ℕ} {nonequal : ¬ _from = _to} (h_from : regs.nth _from = n_from.succ) (h_to : regs.nth _to = n_to)
    : (mov _from _to).mk_conf {ip := some 0, regs := regs} ==>
        conf.mk {ip := some 0, regs := (regs.update_nth _from n_from).update_nth _to n_to.succ}
    := begin
        simp,
        use 2,
        simp [step, vector.head, vector.nth, mov, h_from, h_to, vector.nth_update_nth_of_ne nonequal]
      end

  theorem mov_effect {nonequal : ¬ _from = _to}
    : (mov _from _to).mk_conf {ip := some 0, regs := regs} ==>
      conf.mk {ip := none, regs := (regs.update_nth _from 0).update_nth _to (regs.nth _from + regs.nth _to)}
    := begin
      induction h : (regs.nth _from) generalizing regs,
      simp [step, h],
      exact mov_step_zero h,
      refine rm.conf.steps_to_trans _
        ((mov _from _to).mk_conf {ip := some 0, regs :=  (regs.update_nth _from n).update_nth _to (regs.nth _to).succ})
        _ _ _,
      refine mov_step_succ h rfl,
      exact nonequal,
      have : ((regs.update_nth _from n).update_nth _to (regs.nth _to).succ).nth _from = n,
      rw vector.nth_update_nth_of_ne,
      apply vector.nth_update_nth_same,
      exact ne.symm nonequal,
      convert ih this using 3,
      simp [vector.nth_update_nth_of_ne],
      rw vector.update_nth_comm (ne.symm nonequal),
      simp [vector.update_nth_update_nth_same],
      suffices : n.succ + regs.nth _to = n + (regs.nth _to).succ,
        rw this,
      exact nat.succ_add n (vector.nth regs _to)
    end

  end

end macros

end regmachine