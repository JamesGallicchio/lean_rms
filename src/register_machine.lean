import data.vector
import data.vector2
import data.equiv.encodable.basic
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

@[simp]
lemma vector.nth_of_append_fst {α : Type*} {l1 l2 : ℕ} (v1 : vector α l1) (v2 : vector α l2)
    (i : fin l1) : (v1.append v2).nth (fin.cast_add l2 i) = v1.nth i
  := begin
    cases v1,
    cases v2,
    exact list.nth_le_append _ _,
  end

@[simp]
lemma vector.nth_of_append_snd {α : Type*} {l1 l2 : ℕ} (v1 : vector α l1) (v2 : vector α l2)
    (i : fin l2) : (v1.append v2).nth (fin.nat_add l1 i) = v2.nth i
  := begin
    cases v1,
    cases v2,
    simp! [list.nth_le_drop],
    congr,
    simp [← v1_property],
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
  @[simp]
  def map_regs {rc' : ℕ} (f : fin rc → fin rc')
    : instr rc ic → instr rc' ic
    | (instr.inc r l)   := instr.inc (f r) l
    | (instr.dec r l k) := instr.dec (f r) l k

  @[simp]
  def map_locs {ic' : ℕ} (f : option (fin ic) → option (fin ic'))
    : instr rc ic → instr rc ic'
    | (instr.inc r l)   := instr.inc r (f l)
    | (instr.dec r l k) := instr.dec r (f l) (f k)

  def eq {ic' : ℕ} (loc_eq : option (fin ic) → option (fin ic) → Prop)
    : instr rc ic → instr rc ic → Prop
    | (instr.inc r l) := λ i, match i with
        instr.inc r' l' := r = r' ∧ loc_eq l l' | _ := ⊥ end 
    | (instr.dec r l k) := λ i, match i with
        instr.dec r' l' k' := r = r' ∧ loc_eq l l' ∧ loc_eq k k' | _ := ⊥ end
end instr

/- state consists of an instruction pointer and the registers.
   if ip is none then machine is halted. -/
structure state (rc ic : ℕ) := (ip : option (fin ic)) (regs : vector ℕ rc)
namespace state
  @[simp] def init {rc ic : ℕ} (input : ℕ) : state rc.succ ic.succ
    := {ip := some 0, regs := input ::ᵥ vector.repeat 0 rc}
  @[simp] def is_halted {rc ic : ℕ} (s : state rc ic) := s.ip = none
end state

/- register machine with rc registers and ic instructions -/
def rm (rc ic : ℕ)
  := vector (instr rc ic) ic

namespace rm
  variables {rc ic : ℕ} (M : rm rc ic)

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
  notation c `[` M `]==>` d := M.step c = d

  @[simp]
  def step_t (t : ℕ) := M.step^[t]
  notation c `[` M `]==>^[` t `]` d := (M.step_t t) c = d

  def steps_to (c d : state rc ic)
    := ∃ (t : ℕ), c [M]==>^[t] d
  notation c `[` M `]==>*` d := M.steps_to c d

  @[simp]
  lemma step_is_step_t_1 {c d : state rc ic}
    : (c [M]==>^[1] d) ↔ (c [M]==> d)
    := begin split, intro h, simpa using h,
              intro h, simpa using h end
  
  lemma steps_to_trans {c d e : state rc ic}
    (h1 : c [M]==>* d) (h2 : d [M]==>* e)
    : c [M]==>* e
    := begin
      cases h1, cases h2,
      use h2_w + h1_w,
      simp at h1_h h2_h,
      simp [function.iterate_add, h1_h, h2_h]
    end

  lemma halt_is_fixpoint (regs : vector ℕ rc)
    : {ip := none, regs := regs} [M]==> {ip := none, regs := regs}
    := begin simp [step] end

  def computes (M : rm rc.succ ic.succ) (f : ℕ → ℕ) := ∀ (n : ℕ), ∃ (regs : vector ℕ rc.succ),
    ({ip := some 0, regs := vector.of_fn (λ i, fin.cases n (λ _, 0) i)}
      [M]==>* {ip := none, regs := regs}) ∧ regs.nth 0 = f n

end rm

namespace subproc
  variables {rc prelen sublen postlen : ℕ}
            (halt_loc : option (fin (prelen + sublen + postlen)))

  def embed_line (l : fin sublen)
    : fin (prelen + sublen + postlen)
    := fin.cast_add postlen (fin.nat_add prelen l)

  def embed_loc (loc : option (fin sublen))
    : option (fin (prelen + sublen + postlen))
    := match loc with
    | some l := some (embed_line l)
    | none := halt_loc
    end
  
  @[simp] def embed_state (s : state rc sublen)
    : state rc (prelen + sublen + postlen)
    := {ip := embed_loc halt_loc s.ip, regs := s.regs}

  @[simp] def embed_rm (M : rm rc sublen)
    : vector (instr rc (prelen + sublen + postlen)) sublen
    := M.map (instr.map_locs (embed_loc halt_loc))

  section
  variables 
    (preM : vector (instr rc (prelen+sublen+postlen)) prelen)
    (subM : rm rc sublen)
    (postM : vector (instr rc (prelen+sublen+postlen)) postlen)

  lemma preserves_step
    : let M : rm rc (prelen+sublen+postlen)
            := (preM.append (embed_rm halt_loc subM)).append postM in
      ∀ {c : state rc sublen},
        (embed_state halt_loc c [M]==>* embed_state halt_loc (subM.step c))
    := begin
      intros,
      cases h : c, rw h at *, clear h c,
      cases ip,
      have h := subM.halt_is_fixpoint regs,
      use 0,
      simp [h],
      use 1,
      rw [rm.step_t, nat.iterate, nat.iterate],
      have : M.nth (embed_line ip) = instr.map_locs (embed_loc halt_loc) (subM.nth ip),
        simp [embed_line, embed_loc],
      simp [embed_loc, rm.step, this],
      cases h : (subM.nth ip),
      case regmachine.instr.inc : r l {
        simp [rm.step, embed_loc],
      },
      case regmachine.instr.dec : r l k {
        cases h' : regs.nth r,
        simp [rm.step, embed_loc, h'],
        simp [rm.step, embed_loc, h'],
      }
    end

  theorem preserves_behavior
    : let M : rm rc (prelen+sublen+postlen)
            := (preM.append (embed_rm halt_loc subM)).append postM in
      ∀ {c d : state rc sublen}, (c [subM]==>* d)
        → (embed_state halt_loc c [M]==>* embed_state halt_loc d)
    := begin
      intros M c d h,
      cases h,
      induction h_w generalizing c,
      simp at h_h,
      use 0,
      simp [h_h],
      simp at h_h,
      have rest := h_w_ih h_h,
      clear h_w_ih h_h,
      have step : (embed_state halt_loc c [M]==>* embed_state halt_loc (subM.step c))
                := preserves_step _ _ _ _,
      exact M.steps_to_trans step rest,
    end
  end

end subproc

end regmachine