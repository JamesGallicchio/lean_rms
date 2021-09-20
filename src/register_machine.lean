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
  := ⟨list.rec 0 (λ h _ t', (nat.mkpair (encodable.encode h) t').succ),
      @nat.strong_rec' (λ _, option (list α)) (λ n,
        @nat.cases_on (λ n, (Π (m : ℕ), m < n → option (list α)) → option (list α)) n
          (λ _, some [])
          (λ n' f,
            let p := nat.unpair n' in
            (encodable.decode α p.fst).bind (λ h,
            (f p.snd begin
              refine nat.lt_succ_iff.mpr _,
              exact nat.unpair_le_right n',
            end).map (λ t, h::t)
            )
          )
      ),
      begin
        intro, induction a,
        simp, dsimp, rw [nat.strong_rec'], simp,
        simp, dsimp, rw [nat.strong_rec'], simp,
        convert a_ih, rw nat.unpair_mkpair,
      end⟩

instance encodable.vector {α} [encodable α] {n} : encodable (vector α n)
  := encodable.subtype

instance encodable.fin_tuple {n : ℕ} {α : Type*} [encodable α] : encodable (fin n → α)
  := encodable.of_equiv (vector α n)
      ⟨vector.of_fn, vector.nth,
        begin intro, ext, exact vector.nth_of_fn x x_1, end,
        vector.of_fn_nth⟩

notation f `<-[` x `]` y := function.update f x y

namespace rm

/-  inc r l    ->  increment r and jump to l
    dec r l k  ->  if (r) > 0 then decrement r and jump to l, else jump to k
    jump to halt represented by none instead of a line number
 -/
@[derive decidable_eq]
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

  instance encodable {rc ic : ℕ} : encodable (instr rc ic)
    := encodable.of_equiv _ equiv_destr

  instance has_repr {rc ic : ℕ} : has_repr (instr rc ic)
    := ⟨@instr.rec rc ic (λ _, string)
        (λ r l,
          "(rm.instr.inc ".append (
          (repr r)        .append (
          " "             .append (
          (repr l)        .append (
          ")"
          ))))
        ) (λ r l k,
          "(rm.instr.dec ".append (
          (repr r)        .append (
          " "             .append (
          (repr l)        .append (
          " "             .append (
          (repr k)        .append (
          ")"
          ))))))
        )⟩

end instr

/- register machine program with rc registers, ic instructions -/
@[reducible] def prog (rc ic : ℕ) := fin ic → (instr rc ic)
@[reducible] def prog' (rc : ℕ) := Σ ic, prog rc ic

namespace prog
  instance has_repr {rc ic : ℕ} : has_repr (prog rc ic) :=
    ⟨@repr _ subtype.has_repr ∘ vector.of_fn⟩
end prog

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
      | instr.inc r l := {ip := l, regs := c.regs <-[r] (c.regs r + 1)}
      | instr.dec r l k :=
          match c.regs r with
          | p + 1 := {ip := l, regs := c.regs <-[r] p}
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

namespace progs
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

  section variables {rc rc' ic : ℕ} (P : prog rc ic)
                    (f : fin rc → fin rc')
  def embed : prog rc' ic
    := (instr.map_regs f) ∘ P
  
  variable (finv : fin rc' → (fin rc) ⊕ ℕ)
  @[simp] def embed.reg_map (regs : fin rc → ℕ) : fin rc' → ℕ
    := λ r', match finv r' with sum.inl r := regs r | sum.inr x := x end

  @[simp] def embed.config_map (c : config rc ic) : config rc' ic := ⟨c.ip, embed.reg_map finv c.regs⟩

  variable (h_finv : (∀ r, finv (f r) = sum.inl r) ∧
              (∀ r', sum.elim (λ r, r' = f r) (λ _, true) (finv r'))
            )
  include h_finv

  lemma embed.preserve_step
    : (embed.config_map finv) ∘ P.step = (embed P f).step ∘ (embed.config_map finv)
    := begin
      ext c, simp [embed.reg_map, embed.config_map],
      cases c with ip regs,
      cases ip,
      case none { simp [prog.step] },
      case some {
      cases h : P ip with r ip' r ip' ip'',
      case inc {
        simp [embed, prog.step, h, embed.config_map],
        rw h_finv.1 r,
        ext,
        cases h2 : finv x,
        case inr {
          simp [←h2, function.update],
          rw h2, simp,
          have : ¬ x = f r :=
            begin
              intro h3,
              rw h3 at h2,
              rw h_finv.1 r at h2,
              simpa using h2,
            end,
          simp [this],
        },
        case inl {
          simp [←h2, function.update],
          rw h2, simp [function.update],
          congr' 1, ext,
          have := h_finv.2 x,
          rw h2 at this, simp at this, rw this,
          split,
          intro h, rw h,
          intro h,
          have h1 := h_finv.1 val,
          have h2 := h_finv.1 r,
          rw [h,h2] at h1,
          simp at h1, exact h1.symm,
        }
      },
      case dec {
      cases hr : regs r,
      case zero {
        simp [embed, prog.step, h, hr],
        rw h_finv.1 r,
        simp [prog.step, hr],
      },
      case succ {
        simp [embed, prog.step, h, hr],
        rw h_finv.1 r,
        simp [prog.step, hr],
        ext,
        cases h2 : finv x,
        case inr {
          simp [←h2, function.update],
          rw h2, simp,
          have : ¬ x = f r :=
            begin
              intro h3,
              rw h3 at h2,
              rw h_finv.1 r at h2,
              simpa using h2,
            end,
          simp [this],
        },
        case inl {
          simp [←h2, function.update],
          rw h2, simp [function.update],
          congr' 1, ext,
          have := h_finv.2 x,
          rw h2 at this, simp at this, rw this,
          split,
          intro h, rw h,
          intro h,
          have h1 := h_finv.1 val,
          have h2 := h_finv.1 r,
          rw [h,h2] at h1,
          simp at h1, exact h1.symm,
        },
      }}},
    end

    lemma embed.preserves_steps
      : ∀ t, (embed.config_map finv) ∘ (P.step^[t]) =
              ((embed P f).step^[t]) ∘ (embed.config_map finv)
      := begin
        intro, induction t,
        case zero { simp, },
        case succ : w {
          rw function.iterate_succ,
          rw ←function.comp.assoc,
          rw t_ih,
          rw function.comp.assoc,
          rw embed.preserve_step P f finv,
          refl,
          exact h_finv,
        },
      end

    theorem embed.behavior {ip ip' : option (fin ic)} {regs regs' : fin rc → ℕ}
      (behav : ⟨ip,regs⟩ [P]==>* ⟨ip',regs'⟩)
      : ⟨ip, embed.reg_map finv regs⟩ [embed P f]==>*
          ⟨ip', embed.reg_map finv regs'⟩
      := begin
        cases behav with w h,
        use w,
        simp,
        have emps := embed.preserves_steps P f finv h_finv w,
        have : (embed.config_map finv ∘ (P.step^[w])) ⟨ip,regs⟩ = ((embed P f).step^[w] ∘ embed.config_map finv) ⟨ip,regs⟩,
          rw emps, clear emps,
        simp at h,
        simp [h, embed.config_map] at this,
        exact this.symm,
      end
  end

  section
    variables {rc ic1 ic2 : ℕ} (P1 : prog rc ic1) (P2 : prog rc ic2)
    include P1 P2

    def seq.midpoint_ic : option (fin (ic1+ic2))
      := (config.init_ip rc ic2).map (λ z,
          ⟨ic1 + z, begin exact nat.add_lt_add_left z.prop ic1, end⟩)

    def seq : prog rc (ic1+ic2) :=
      fin.append rfl
        (instr.map_locs (λ o, match o with
                              | some i := some ⟨i.val, i.val.lt_add_right ic1 ic2 i.prop⟩
                              | none := seq.midpoint_ic P1 P2
                              end)
            ∘ P1)
        (instr.map_locs (option.map (λ i, ⟨ic1 + i,nat.add_lt_add_left i.prop ic1⟩))
            ∘ P2)

    def seq' (P1 P2 : prog' rc) : prog' rc :=
      ⟨P1.fst+P2.fst, seq P1.snd P2.snd⟩

    lemma seq.behavior
      {r1 r2 r3 : fin rc → ℕ}
      (h1 : ⟨config.init_ip rc ic1, r1⟩ [P1]==>* config.halted r2)
      (h2 : ⟨config.init_ip rc ic2, r2⟩ [P2]==>* config.halted r3)
      : ⟨config.init_ip rc (ic1+ic2), r1⟩ [seq P1 P2]==>* config.halted r3
      := begin
        have phase1 : ⟨config.init_ip rc (ic1+ic2), r1⟩ [seq P1 P2]==>* ⟨seq.midpoint_ic P1 P2, r2⟩,
          cases h1, use h1_w,
          induction h1_w,
            simp at h1_h |-, split, swap, exact h1_h.2,
            simp [seq.midpoint_ic],
            rw (sorry : ic1 = 0),
            simp [nat.zero_add, fin.zero_add],
            exact sorry,
          exact sorry,
        have phase2 : ⟨seq.midpoint_ic P1 P2, r2⟩ [seq P1 P2]==>* config.halted r3,
          exact sorry,
        exact prog.steps_to_trans (seq P1 P2) phase1 phase2,
      end

  end

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

  @[simp] def mov.loop_prog : prog 1 1 := ![instr.inc 0 none]
  def mov : prog 2 2 := loop (mov.loop_prog)
  
  theorem mov.behavior {n m : ℕ}
    : ⟨some 0, ![n, m]⟩ [mov]==>* ⟨none, ![0, n+m]⟩
    := begin have :=
          loop.behavior mov.loop_prog (λ regs, regs <-[0] (regs 0).succ)
          (begin intros, use 1, dsimp [prog.step], refl, end) n ![m],
      convert this, clear this,
      induction n, simp,
      rw function.iterate_succ_apply', rw ←n_ih,
      simp [matrix.vec_cons], rw fin.update_cons_zero, congr,
      exact nat.succ_add n_n m,
    end

  @[simp] def dup.loop_prog : prog 2 2 := ![instr.inc 0 (some 1), instr.inc 1 none]
  lemma dup.loop_prog.behavior (regs : fin 2 → ℕ)
    : ⟨some 0, regs⟩ [dup.loop_prog]==>* ⟨none, ![(regs 0).succ, (regs 1).succ]⟩
    := begin
      use 2, simp [prog.step], ext x, cases x,
      cases x_val, simp [function.update],
      simp, cases x_val, simp [function.update],
      apply false.elim (nat.not_lt_zero x_val _),
      iterate 2 {
        apply nat.lt_of_succ_lt_succ _,
      }, exact x_property,
    end

  def dup : prog 3 3 := loop (dup.loop_prog)
  theorem dup.behavior (a b c : ℕ)
    : ⟨some 0, ![a,b,c]⟩ [dup]==>* ⟨none, ![0, b+a, c+a]⟩
    := begin have :=
          loop.behavior dup.loop_prog
          (λ regs, ![(regs 0).succ, (regs 1).succ])
          (dup.loop_prog.behavior) a ![b,c],
      convert this, clear this,
      induction a, simp,
      rw function.iterate_succ_apply', rw ←a_ih,
      simp,
    end

  def double : prog 3 7 :=
    cast (by refl) (
      seq dup (
        seq
          (embed mov ![1,0])
          (embed mov ![2,0])
      )
    )
  
  section open sum
  theorem double.behavior (n : ℕ)
    : config.init n [double]==>* config.halted ![2*n,0,0]
    := begin
      have db := dup.behavior n 0 0, simp at db,
      have h_c1 : ![0,n,n] = embed.reg_map ![inl 1, inl 0, inr n] ![n, 0]
          := begin ext, fin_cases x, iterate { simp, }, end,
      rw h_c1 at db,
      have em1 := embed.behavior mov ![1,0] ![inl 1, inl 0, inr n] (begin 
          split, intro, fin_cases r, iterate {simp,},
          intro, fin_cases r', iterate {simp,},
        end) (@mov.behavior n 0),
      have h_c2 : embed.reg_map ![inl 1, inl 0, inr n] ![0, n + 0] =
                  embed.reg_map ![inl 1, inr 0, inl 0] ![n, n]
          := begin ext, fin_cases x, iterate { simp, }, end,
      rw h_c2 at em1,
      have em2 := embed.behavior mov ![2,0] ![inl 1, inr 0, inl 0] (begin 
          split, intro, fin_cases r, iterate {simp,},
          intro, fin_cases r', iterate {simp,},
        end) (@mov.behavior n n),
      have h_c3 : embed.reg_map ![inl 1, inr 0, inl 0] ![0, n + n] =
                  ![2*n, 0, 0]
          := begin ext, fin_cases x, iterate {simp, abel,}, end,
      rw h_c3 at em2,
      have s1 := seq.behavior _ _ em1 em2,
      have s2 := seq.behavior _ _ db s1,
      convert s2,
      simp, ext, fin_cases x, iterate { simp, simpa, },
    end
  end
  
end progs

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

    @[simp] def encode : α → ℕ := c.to_encodable.encode
    @[simp] def decode : ℕ → option α := c.to_encodable.decode
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
  
  instance nat : rmcodable ℕ := ⟨encodable.nat, progs.succ, begin
      intros, rw prog.eval_mem_iff_steps, use ![],
      exact progs.succ.behavior n,
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

namespace prog
  def apply {rcp ic : ℕ} (P : prog rcp.succ ic)
      {α β : Type*} [rmcodable α] [rmcodable β] : α →. β
    := λ a, (P.eval (rmcodable.encode a)).bind
              (roption.of_option ∘ (@rmcodable.decode β _))
  
  def add : prog 3 10 := sorry
  theorem add.behavior : add.apply = pfun.lift (λ pair : ℕ × ℕ, pair.fst + pair.snd)
    := begin
      simp [apply, pfun.lift], ext,
      exact sorry,
    end

end prog

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
  (n : ℕ) : prog.apply univ_machine (P,n) = P.eval n := sorry

end rm