import data.fin
import data.fin2
import data.fintype.fin
import data.equiv.encodable.basic
import data.list
import data.matrix.notation
import data.nat.log
import data.nat.pairing
import data.pfun
import data.vector
import data.vector2
import init.data.nat.basic
import logic.function.iterate

instance encodable.list {α} [encodable α] : encodable (list α)
  := ⟨list.rec 0 (λ h _, nat.mkpair (encodable.encode h)),
      sorry,
      sorry⟩

instance encodable.fin_tuple {n : ℕ} {α : Type*} [encodable α] : encodable (fin n → α)
  := encodable.of_equiv (list α) sorry

namespace rm

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

  def reg : instr rc ic → fin rc
    | (instr.inc r _) := r
    | (instr.dec r _ _) := r

  def equiv_destr : instr rc ic ≃ (fin rc × option (fin ic) ⊕ fin rc × option (fin ic) × option (fin ic))
    := ⟨(λ i, match i with instr.inc r l := sum.inl (r,l)
                        | instr.dec r l k := sum.inr (r,l,k) end),
        (λ i, match i with sum.inl (r,l) := instr.inc r l
                        | sum.inr (r,l,k) := instr.dec r l k end),
        begin intro, cases x, iterate {simp [equiv_destr._match_1, equiv_destr._match_2]}, end,
        begin intro, iterate {cases x, simp [equiv_destr._match_1, equiv_destr._match_2]},
              cases x_snd, simp [equiv_destr._match_1, equiv_destr._match_2], end⟩

  instance {rc ic : ℕ} : encodable (instr rc ic)
    := encodable.of_equiv _ equiv_destr

end instr

/- register machine program with rc registers, ic instructions -/
@[reducible] def prog (rc ic : ℕ) := fin ic → (instr rc ic)

/- config consists of an instruction pointer and registers. -/
structure config (rc ic : ℕ) := (ip : option (fin ic)) (regs : fin rc → ℕ)
namespace config
  -- start at instruction 0 if it exists
  @[simp] def init_ip (rc ic : ℕ) : option (fin ic)
    := match ic with 0 := none | icp+1 := some 0 end

  -- init register 0 with input, all others with 0
  @[simp] def init_regs (rcp ic : ℕ) (input : ℕ) : fin rcp.succ → ℕ
    := fin.cons input (function.const (fin rcp) 0)
  
  @[simp] def init {rcp ic : ℕ} (input : ℕ) : config rcp.succ ic
    :=  {ip := init_ip rcp.succ ic,
        regs := init_regs rcp ic input }
  
  @[simp] def halted {rc ic : ℕ} (regs : fin rc → ℕ) : config rc ic
    -- output will be at register 0
    := {ip := none, regs := regs}

  @[reducible] def is_halted {rc ic : ℕ} (c : config rc ic) : Prop
    := c.ip = none

  /- @[reducible] def is_halted {rc ic : ℕ} (c : config rc ic) := c.ip = none
  @[reducible] def output {rcp ic : ℕ} (c : config rcp.succ ic) : ℕ ⊕ config rcp.succ ic
    := if c.is_halted then sum.inl (c.regs 0) else sum.inr c

  theorem ic_zero_is_halted {rc : ℕ} (c : config rc 0) : c.is_halted
    := begin cases h : c.ip, exact h, exact fin.elim0 val end -/
end config

namespace prog
  variables {rc ic : ℕ} (P : prog rc ic)
  
  /- most important definition here! gives semantics to those incs and decs :) -/
  def step (c : config rc ic) :=
    match c.ip with
    | none := c
    | some ip :=
      match P ip with
      | instr.inc r l := {ip := l, regs := function.update c.regs r (c.regs r + 1)}
      | instr.dec r l k :=
          match c.regs r with
          | p + 1 := {ip := l, regs := function.update c.regs r p}
          | 0 := {ip := k, regs := c.regs}
          end
      end
    end

  notation c `[` P `]==>` d := step P c = d

  @[simp]
  def step_t (t : ℕ)
    := (step P)^[t]

  notation c `[` P `]==>^[` t `]` d := (step_t P t) c = d

  def steps_to (c d : config rc ic)
    := ∃ (t : ℕ), c [P]==>^[t] d

  notation c `[` P `]==>*` d := steps_to P c d

  @[simp]
  lemma step_is_step_t_1 {c d : config rc ic}
    : (c [P]==>^[1] d) ↔ (c [P]==> d)
    := begin split, intro h, simpa using h,
              intro h, simpa using h end
  
  lemma step_t_unique {c d e : config rc ic} {t : ℕ}
    (h1 : c [P]==>^[t] d) (h2 : c [P]==>^[t] e)
    : d = e
    := begin
      induction t generalizing c,
      simp at *, exact eq.trans h1.symm h2,
      simp at h1 h2,
      refine @t_ih (step P c) _ _,
      simpa using h1,
      simpa using h2,
    end
  
  lemma step_t_trans {c d e : config rc ic} {t1 t2 : ℕ}
    (h1 : c [P]==>^[t1] d) (h2 : d [P]==>^[t2] e)
    : c [P]==>^[t1+t2] e
    := begin
      simp at h1 h2 |-,
      rw nat.add_comm t1 t2,
      rw function.iterate_add_apply (step P) t2 t1 c,
      rw [h1,h2],
    end
  
  lemma steps_to_trans {c d e : config rc ic}
    (h1 : c [P]==>* d) (h2 : d [P]==>* e)
    : c [P]==>* e
    := begin
      cases h1, cases h2,
      use h2_w + h1_w,
      simp at h1_h h2_h,
      simp [function.iterate_add, h1_h, h2_h]
    end
  
  lemma halt_fix_step_t (regs : fin rc → ℕ) (t : ℕ)
    : {ip := none, regs := regs} [P]==>^[t] {ip := none, regs := regs}
    := begin induction t, simp, simpa, end

  def run_from_state : config rc ic →. (fin rc → ℕ)
    := pfun.fix (λ c, roption.some (
        if c.is_halted  then sum.inl c.regs
                        else sum.inr (P.step c)))
  
  theorem run_from_state_dom_if_steps {c : config rc ic}
    : (∃ rs, c [P]==>* config.halted rs) → (P.run_from_state c).dom
    := begin
      intro h, cases h, cases h_h,
      rw run_from_state,
      exact sorry,
    end

  @[simp]
  def evals_from_to {rcp : ℕ} (P : prog rcp.succ ic) (input : ℕ) (output : ℕ) : Prop
    := ∃ tail, config.init input [P]==>*
                config.halted (fin.cons output tail)
  
  def eval {rcp : ℕ} (P : prog rcp.succ ic) : ℕ →. ℕ
    := λ n, {dom := ∃ m, P.evals_from_to n m, get := λ h,
              (P.run_from_state (config.init n)).get (begin
                apply run_from_state_dom_if_steps,
                cases h, cases h_h, use fin.cons h_w h_h_w,
                exact h_h_h,
              end) 0}

  theorem eval_mem_iff_steps {rcp ic : ℕ} (P : prog rcp.succ ic) {n m : ℕ}
    : m ∈ P.eval n ↔ ∃ tail, config.init n [P]==>* config.halted (fin.cons m tail)
    := sorry


end prog

namespace prog
  def id : prog 1 0 := ![]

  theorem id.behavior (n : ℕ)
    : (config.init n) [id]==>* (config.halted ![n])
    := begin use 0, simp [prog.step], refl, end

  def succ : prog 1 1 := λ _, instr.inc 0 none

  theorem succ.behavior (n : ℕ)
    : (config.init n) [succ]==>* (config.halted ![n.succ])
    := begin use 1, simp [succ, prog.step, function.update],
        rw fin.update_cons_zero, refl,
      end

  def embed {rc ic : ℕ} (P : prog rc ic) {rc' : ℕ} (f : fin rc → fin rc')
    : prog rc' ic
    := (instr.map_regs f) ∘ P
  
/-   section
    variables {rc ic : ℕ} (P : prog rc ic) {rc' : ℕ}
        (f : fin rc → fin rc')
        (h : ∀ r', )

    variables
      {ip1 ip2 : fin ic} {r1 r2 : fin rc → ℕ}
      {r1' : fin rc' → ℕ} (h : r1 = r1' ∘ f)

    lemma embed_regs_preserves_step
      (behav : ⟨ip1, r1⟩ [P]==> ⟨ip2, r2⟩)
      : ⟨ip1, r1'⟩ [embed P f]==> ⟨ip2, embed_regs_res⟩
      := begin end

    theorem embed_regs_preserves_behavior
      (behav : ⟨ip1, r1⟩ [P]==>* ⟨ip2, r2⟩)
      : ⟨ip1, r1'⟩ [embed P f]==>* ⟨ip2, r2'⟩
      := begin
        cases behav, use behav_w,
        induction behav_w,
        simp at *, split, exact behav_h.1,
        
      end
  end -/

  def seq {rc ic1 ic2 : ℕ} (P1 : prog rc ic1) (P2 : prog rc ic2)
    : prog rc (ic1+ic2) :=
      fin.append
        (rfl : ic1+ic2 = ic1+ic2)
        (instr.map_locs (λ o : option (fin ic1), match o with
                              | some i := some ⟨i.val, i.val.lt_add_right ic1 ic2 i.prop⟩
                              | none := match ic2 with
                                        | 0 := none
                                        | ic2p+1 := some ⟨ic1, nat.add_lt_add_left fin.last_pos ic1⟩
                                        end
                              end)
            ∘ P1)
        (instr.map_locs (option.map (λ i, ⟨ic1 + i,nat.add_lt_add_left i.prop ic1⟩))
            ∘ P2)

  lemma seq.behavior {rc ic1 ic2 : ℕ} {P1 : prog rc ic1} {P2 : prog rc ic2}
    {n : ℕ} {r1 r2 r3 : fin rc → ℕ}
    (h1 : {ip := config.init_ip rc ic1, regs := r1} [P1]==>* config.halted r2)
    (h2 : {ip := config.init_ip rc ic2, regs := r2} [P2]==>* config.halted r3)
    : {ip := config.init_ip rc (ic1+ic2), regs := r1}
          [seq P1 P2]==>* config.halted r3
    := sorry

  def loop {rc ic : ℕ} (P : prog rc ic)
    : prog rc.succ ic.succ
    := fin.cons (instr.dec 0 (some 1) none)
        (instr.map_locs (λ l, match l with some x := some x.succ | none := some 0 end)
          ∘ instr.map_regs (λ r, r.succ)
          ∘ P)

  theorem loop.behavior {rc ic : ℕ} (P : prog rc ic)
        (f_P : (fin rc → ℕ) → (fin rc → ℕ))
        (hf : ∀ regs, ⟨config.init_ip rc ic,regs⟩ [P]==>* {ip := none, regs := f_P regs})
    : ∀ n regs, {ip := some 0, regs := fin.cons n regs}
        [loop P]==>* {ip := none, regs := fin.cons 0 (f_P^[n] regs)}
    := sorry

  def reset : prog 1 1 := loop ![]

  lemma reset.behavior (n : ℕ)
    : (config.init n) [reset]==>* (config.halted (![0]))
    := begin
      convert loop.behavior ![] (λ x,x) (begin intro, use 0, simp, end) n ![],
      simp,
    end

  def mov {rc : ℕ} (_fr _to : fin rc) : prog rc 2
    := embed (loop (![instr.inc 0 none])) ![_fr, _to]
  
  theorem mov.behavior {rc ic : ℕ} (_fr _to : fin rc) {hr : _fr ≠ _to}
    : sorry
    := sorry
end prog

/- encodable type where an RM can recognize
    valid/invalid encodings (to prevent adding
    computational power via the encoding) -/
class rmcodable (α : Type*)
  := (to_encodable : encodable α)
      {coding_rcp coding_icp : ℕ} (coding_P : prog coding_rcp.succ coding_icp.succ)
      (h : ∀ n, (encodable.encode (encodable.decode α n)) ∈ coding_P.eval n)

instance rmcodable_to_encodable {α : Type*} [rmcodable α] : encodable α
  := rmcodable.to_encodable

namespace rmcodable
  section
    variables {α : Type*} [c : rmcodable α]

    def encode : α → ℕ := c.to_encodable.encode
    def decode : ℕ → option α := c.to_encodable.decode
  end
  
  def of_equiv {β} (α) [c : rmcodable α] (e : β ≃ α) : rmcodable β
    := let beta_enc := encodable.of_equiv α e in
      ⟨beta_enc, c.coding_P, begin
        intros, have := @rmcodable.h _ c n,
        rw prog.eval_mem_iff_steps at this |-,
        cases this, use this_w,
        have : encodable.encode (encodable.decode α n) = @encodable.encode _ (@encodable.option _ beta_enc) (@encodable.decode β beta_enc n),
          simp [encodable.encode, encodable.decode],
          cases encodable.decode α n,
          dsimp, refl,
          dsimp, simp,
        rw ←this, exact this_h,
      end⟩
  
  instance nat : rmcodable ℕ := ⟨encodable.nat, prog.succ, begin
      intros, rw prog.eval_mem_iff_steps, use ![],
      exact prog.succ.behavior n,
    end⟩

  instance fin (n) : rmcodable (fin n)
    := ⟨encodable.fin n,
      (sorry : prog 1 1), sorry
    ⟩

  instance prod {α β} [rmcodable α] [rmcodable β] : rmcodable (α × β)
    := ⟨encodable.prod,
      (sorry : prog 1 1),
      sorry
    ⟩

  instance sum {α β} [rmcodable α] [rmcodable β] : rmcodable (α ⊕ β)
    := ⟨encodable.sum,
      (sorry : prog 1 1),
      sorry
    ⟩

  instance option {α : Type*} [ae : encodable α] : rmcodable (option α)
    := ⟨encodable.option,
      (sorry : prog 1 1), sorry
    ⟩

  instance list {α : Type*} [ae : encodable α] : rmcodable (list α)
    := ⟨encodable.list,
      (sorry : prog 1 1), sorry
    ⟩

  instance instr {rc ic : ℕ} : rmcodable (instr rc ic)
    := of_equiv _ instr.equiv_destr

  instance {rc ic : ℕ} : rmcodable (prog rc ic)
    := sorry

end rmcodable

def apply {rcp ic : ℕ} (P : prog rcp.succ ic)
    {α β : Type*} [rmcodable α] [rmcodable β] : α →. β
  := λ a, (P.eval (rmcodable.encode a)).bind
            (roption.of_option ∘ (@rmcodable.decode β _))

  /- goal: build up this universal machine

  0 := copy E R 1
  1 := write R p x 2
  2 := read E p I 3
  3 := pop I r 4
  4 := zero I halt 5
  5 := pop I p 6
  6 := read R r x 7
  7 := zero I 8 9
  8 := inc x 12
  9 := zero x 10 11
  10 := pop I p 2
  11 := dec x 12 12
  12 := write R r x 2
  -/

def univ_machine : prog (nat.succ sorry) sorry := sorry

theorem univ_machine_computes_eval {rcp ic : ℕ} (P : prog rcp.succ ic)
  (n : ℕ) : apply univ_machine (P,n) = P.eval n := sorry

end rm