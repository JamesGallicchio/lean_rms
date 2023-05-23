import RegMachine.Imported

namespace RegMachine

/-  inc r l    ->  increment r and jump to l
    dec r l k  ->  if (r) > 0 then decrement r and jump to l, else jump to k
    jump to halt represented by none instead of a line number
 -/
inductive Instr (R L : Type)
| inc (reg : R) (jmp : Option L)
| dec (reg : R) (jmp_s : Option L) (jmp_z : Option L)
deriving Repr

namespace Instr

instance [Encodable R] [Encodable L] : Encodable (Instr R L) :=
  Encodable.ofEquiv (α := R × Option L ⊕ R × Option L × Option L) {
    toFun   := fun | .inc r j => .inl (r,j) | .dec r js jz => .inr (r,js,jz)
    invFun  := fun | .inl (r,j) => .inc r j | .inr (r,js,jz) => dec r js jz
    left_inv  := by intro x; cases x <;> simp
    right_inv := by intro y; cases y <;> simp
  }

end Instr

/- register machine program with R registers, L instructions -/
@[reducible] def Prog (R L) := L → (Instr R L)

structure Prog.Start (R L) where
  prog : Prog R L
  start : L

/-- by convention, the I/O register is where input is placed
  at the start of execution and output is read when halting. -/
inductive WithIO (R) | io | internal (r : R)
deriving DecidableEq

/-- config consists of an instruction pointer and registers. -/
structure Config (R L) where
  ip : Option L
  regs : R → Nat

namespace Config

variables {R L : Type}

/-- registers are initialized to `input` for the io reg and 0 for all others -/
def init (input : Nat) (ip : Option L) : Config (WithIO R) L where
  ip := ip
  regs := fun | .io => input | .internal _ => 0

/-- halted config has `none` as the ip -/
@[reducible] def is_halted (c : Config R L) : Bool := c.ip.isNone

def haltedOn (output : Nat) (regs : R → Nat) : Config (WithIO R) L where
  ip := none
  regs := fun | .io => output | .internal r => regs r

@[simp] theorem is_halted_haltedOn : is_halted (haltedOn (R := R) (L := L) o r) = true :=
  by simp [is_halted, haltedOn]

@[simp] theorem io_reg_haltedOn : (haltedOn (R := R) (L := L) o r).regs .io = o :=
  by simp [Config.haltedOn]

end Config

/-- the small-step semantics of a program -/
def step (p : Prog R L) [DecidableEq R] (c : Config R L) :=
  match c.ip with
  | none => c
  | some ip =>
    match p ip with
    | .inc r l => {ip := l, regs := Function.update c.regs r (c.regs r + 1)}
    | .dec r l k =>
      match c.regs r with
      | n + 1 => {ip := l, regs := Function.update c.regs r n}
      | 0     => {ip := k, regs := c.regs}

variable (P : Prog R L) [DecidableEq R] (S : Start (WithIO R) L)

@[simp] def stepsTo (c d : Config R L) := step P c = d
@[simp, reducible] def stepsToTrans := Relation.TransGen (stepsTo P)
@[simp, reducible] def stepsToReflTrans := Relation.ReflTransGen (stepsTo P)

set_option quotPrecheck false in section
  notation c:30 " [" P "]==> "  d:30 => stepsTo          P c d
  notation c:30 " [" P "]==>+ " d:30 => stepsToTrans     P c d
  notation c:30 " [" P "]==>* " d:30 => stepsToReflTrans P c d
end

theorem stepsTo_functional (h1 : c [P]==> d1) (h2 : c [P]==> d2)
  : d1 = d2 := by
  match c with
  | {ip,regs} =>
    cases ip <;>
      (simp [step] at h1 h2; cases h1; cases h2; rfl)

theorem halt_is_fixpoint (h : c [P]==>* d)
  : c.is_halted → c = d
  := by
  induction h using Relation.ReflTransGen.head_induction_on
  case refl => simp
  case head c' d' h _ ih =>
    intro hc'
    simp [Config.is_halted] at hc' ih ⊢
    simp [step, hc'] at h
    cases h
    apply ih hc'

theorem halt_is_unique (h1 : c [P]==>* d1) (h2 : c [P]==>* d2)
  (hd1 : d1.is_halted) (hd2 : d2.is_halted) : d1 = d2
  := by
  induction h1 using Relation.ReflTransGen.head_induction_on
  case refl =>
    apply halt_is_fixpoint _ h2 hd1
  case head c' d' h _h ih =>
    apply ih
    clear ih _h hd1 d1 c
    cases Relation.ReflTransGen.cases_head h2 <;> clear h2
    case inl h2 =>
      cases h2
      have : d2 = d' := by
        apply halt_is_fixpoint
        . exact Relation.ReflTransGen.single h
        . exact hd2
      cases this; apply Relation.ReflTransGen.refl
    case inr h2 =>
      rcases h2 with ⟨c,hc,h2⟩
      have : c = d' := stepsTo_functional _ hc h
      cases this
      exact h2

theorem stepsToTrans_of_not_halts_stepsToTransRefl_halts
  (h : c [P]==>* d) (hc : ¬c.is_halted) (hd : d.is_halted)
  : c [P]==>+ d := by
  cases Relation.ReflTransGen.cases_head h
  clear h
  case inl heq =>
    cases heq; contradiction
  case inr h =>
    rcases h with ⟨c',hc_c',hc'_d⟩
    exact Relation.TransGen.head' hc_c' hc'_d

namespace Prog

/-- whether program halts, starting at `c` -/
def halts (c : Config R L) : Prop := ∃ d, (c [P]==>* d) ∧ d.is_halted

/-- Whether the program halts on a given input -/
def Start.haltsOn (i : Nat) : Prop := S.prog.halts (Config.init i S.start)

/-- The relation `P` generates between input and output values -/
def Start.evals (i o : Nat) : Prop :=
  ∃ regs, (Config.init i S.start) [S.prog]==>* (Config.haltedOn o regs)

/-- If an output exists for a certain input, it is unique. -/
theorem Start.evals_functional (h1 : S.evals i o1) (h2 : S.evals i o2)
  : o1 = o2 := by
  match h1, h2 with
  | ⟨regs1,h1'⟩, ⟨regs2,h2'⟩ =>
  clear h1 h2
  generalize Config.init _ _ = c1 at h1' h2'
  clear i
  induction h1' using Relation.ReflTransGen.head_induction_on
    <;> clear c1
  case refl =>
    have : o1 = (Config.haltedOn (L := L) o1 regs1).regs .io :=
      by simp [Config.haltedOn]
    rw [this]
    have := halt_is_fixpoint _ h2' (by simp)
    rw [this]
    simp
  case head c d h _ ih =>
    apply ih; clear ih
    cases Relation.ReflTransGen.cases_head h2' <;> clear h2'
    case inl h2' =>
      cases h2'
      have : _ = d := by
        apply halt_is_fixpoint _ (Relation.ReflTransGen.single h)
        simp
      rw [←this]
    case inr h2' =>
      rcases h2' with ⟨c',hc,h⟩
      have : c' = d := stepsTo_functional _ hc ‹_›
      rw [←this]
      exact h

/-- a configuration from which `P` halts. used to
  justify termination for `Start.eval` -/
structure HaltingConfig where
  config : Config R L
  halts : P.halts config

instance : WellFoundedRelation (HaltingConfig P) where
  rel d c := ¬c.config.is_halted ∧ c.config [P]==> d.config
  wf := .intro fun {config := d, halts := hd} => by
    rename HaltingConfig P => e; clear e
    rcases hd with ⟨f,hd_to_f,hf_halted⟩
    induction hd_to_f using Relation.ReflTransGen.head_induction_on <;> (
      apply Acc.intro
      rintro ⟨e,he_halts⟩ ⟨hd_running,hd_to_e⟩
      simp only at *
      clear d
    )
    . contradiction
    next x y hx_to_y hy_to_f ih =>
      have : y = e := by
        clear he_halts ih hd_running hy_to_f hf_halted f
        apply stepsTo_functional _ hx_to_y hd_to_e
      cases this
      apply ih


/-- Evaluation, expressed as a partial function whose
  domain is all inputs for which it halts -/
def Start.eval (n : Nat) (h : S.haltsOn n) : Nat :=
  aux S.prog ⟨Config.init n S.start, h⟩
where
  aux (P : Prog (WithIO R) L) (c : HaltingConfig P) : Nat :=    
    match hc : c.config.is_halted with
    | true => c.config.regs .io
    | false =>
      let c' : HaltingConfig P := ⟨step P c.config, by
        rcases c with ⟨c,d,h,hd⟩
        simp only at hc
        refine ⟨d, ?_, hd⟩
        cases Relation.ReflTransGen.cases_head h
        case inl h =>
          cases h; rw [hd] at hc; contradiction
        case inr h =>
          rcases h with ⟨c', h, hc'⟩
          cases h
          exact hc'⟩
      have : ¬c.config.ip = none := by
        intro; simp [Config.is_halted, *] at hc
      aux P c'
termination_by aux c => c

theorem Start.eval_eq : S.eval n hn = m ↔ S.evals n m := by
  suffices ∀ c hc,
    eval.aux S.prog ⟨c,hc⟩ = m ↔
      ∃ regs, c [S.prog]==>* Config.haltedOn m regs
    from this _ _
  clear hn n
  intro c hc
  rcases hc with ⟨d,h,hd⟩
  induction h using Relation.ReflTransGen.head_induction_on
  case refl =>
    unfold eval.aux
    split
    case h_2 h =>
      rw [hd] at h
      contradiction
    next h =>
    clear h
    simp
    constructor <;> intro h
    . use fun r => d.regs (.internal r)
      have : d = Config.haltedOn m (fun r => d.regs (.internal r)) := by
        rcases d with ⟨ip,regs⟩
        simp at hd; cases hd
        simp [Config.haltedOn]
        funext r
        cases r <;> simp at h ⊢
        . exact h
      rw [this] at *
      cases this
      exact .refl
    . rcases h with ⟨regs,h⟩
      have := halt_is_fixpoint _ h hd
      clear h hd
      cases this
      simp
  case head a b ha_to_b hb_to_d ih =>
    clear c
    unfold eval.aux
    constructor <;> intro h
    . have : ∃ regs, b [S.prog]==>* Config.haltedOn m regs := by
        simp at *
        split at h
        . have : a = b := halt_is_fixpoint _ (.single ha_to_b) ‹_›
          cases this
          have : a = Config.haltedOn m (a.regs <| .internal ·) := by
            cases a; simp at *; simp [Config.haltedOn, *]; funext x; split <;> simp [*]
          rw [this]
          refine ⟨_, Relation.ReflTransGen.refl⟩
        . apply ih.mp
          cases ha_to_b
          exact h
      rcases this with ⟨regs,h⟩
      use regs
      exact .head ha_to_b h
    . rcases h with ⟨regs,h⟩
      split
      next ha =>
        simp only at *
        have := halt_is_fixpoint _ h ha
        simp [this]
      next ha =>
        simp
        cases ha_to_b
        apply ih.mpr
        use regs
        have := stepsToTrans_of_not_halts_stepsToTransRefl_halts _ h ?_ ?_
        . rcases Relation.TransGen.head'_iff.mp this with ⟨e,rfl,he⟩
          exact he
        . simp at ha; simp [ha]
        . simp
