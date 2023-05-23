import RegMachine.Basic

namespace RegMachine.Components

def id : Prog Unit Empty := Empty.elim

theorem id.behavior (n : ℕ)
  : (config.init n) [id]==>* (config.halted ![n])
  := by use 0, simp [prog.step], refl

def succ : prog 1 1 := λ _, instr.inc 0 none

theorem succ.behavior (n : ℕ)
  : (config.init n) [succ]==>* (config.halted ![n.succ])
  := by use 1, simp [succ, prog.step, function.update],
      rw fin.update_cons_zero, refl,

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
  := by
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
          by
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
          by
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
    := by
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
    := by
      cases behav with w h,
      use w,
      simp,
      have emps := embed.preserves_steps P f finv h_finv w,
      have : (embed.config_map finv ∘ (P.step^[w])) ⟨ip,regs⟩ = ((embed P f).step^[w] ∘ embed.config_map finv) ⟨ip,regs⟩,
        rw emps, clear emps,
      simp [h, embed.config_map] at this,
      exact this.symm,
    end
end

section
  variables {rc ic1 ic2 : ℕ} (P1 : prog rc ic1) (P2 : prog rc ic2)
  include P1 P2

  def seq.midpoint_ic : option (fin (ic1+ic2))
    := (config.init_ip rc ic2).map (λ z,
        ⟨ic1 + z, by exact nat.add_lt_add_left z.prop ic1, end⟩)

  @[simp] def seq.loc_map_1 : option (fin ic1) → option (fin (ic1+ic2))
  | (some i) := some ⟨i.val, i.val.lt_add_right ic1 ic2 i.prop⟩
  | none := seq.midpoint_ic P1 P2

  @[simp] def seq.loc_map_2 : option (fin ic2) → option (fin (ic1+ic2))
  | (some i) := some ⟨ic1 + i,nat.add_lt_add_left i.prop ic1⟩
  | none := none

  def seq : prog rc (ic1+ic2) :=
    fin.append rfl
      (instr.map_locs (seq.loc_map_1 P1 P2) ∘ P1)
      (instr.map_locs (seq.loc_map_2 P1 P2) ∘ P2)

  def seq' (P1 P2 : prog' rc) : prog' rc :=
    ⟨P1.fst+P2.fst, seq P1.snd P2.snd⟩

  variables {P1 P2}

  lemma seq.preserves_step_1 {regs : fin rc → ℕ} {i : fin ic1} {c}
    (h : ⟨some i, regs⟩ [P1]==> c)
    : ⟨seq.loc_map_1 P1 P2 (some i), regs⟩ [seq P1 P2]==>
        ⟨seq.loc_map_1 P1 P2 c.ip, c.regs⟩
    := by
      have hic : (↑i < ic1 ↔ true),
        split, intro, trivial,
        intro, simpa using i.prop,
      cases hi : P1 i,
      case inc : r l {
        simp [prog.step, hi] at h,
        simp [prog.step, seq, ←h, hi, hic, fin.append],
      },
      case dec : r l k {
        cases hr : regs r,
        iterate {
          simp [prog.step, hi, hr] at h,
          simp [prog.step, seq, hi, hic, hr, ←h, fin.append],
        },
      },
    end

  lemma seq.preserves_step_2 {regs : fin rc → ℕ} {i : fin ic2} {c}
    (h : ⟨some i, regs⟩ [P2]==> c)
    : ⟨seq.loc_map_2 P1 P2 (some i), regs⟩ [seq P1 P2]==>
        ⟨seq.loc_map_2 P1 P2 c.ip, c.regs⟩
    := by
      cases hi : P2 i,
      case inc : r l {
        simp [prog.step, hi] at h,
        simp [prog.step, seq, hi, ←h, fin.append],
      },
      case dec : r l k {
        cases hr : regs r,
        iterate {
          simp [prog.step, hi] at h,
          simp [prog.step, seq, hi, hr, ←h, fin.append],
        }
      },
    end
  
  lemma seq.preserves_steps_1 {i : fin ic1} {regs regs' : fin rc → ℕ}
    (h : ⟨some i, regs⟩ [P1]==>* config.halted regs')
    : ⟨seq.loc_map_1 P1 P2 (some i), regs⟩ [seq P1 P2]==>* ⟨seq.midpoint_ic P1 P2,regs'⟩
    := by
      cases ic1,
      case zero {
        exact fin.elim0 i,
      },
      simp,
      cases h, induction h_w generalizing i regs,
      case zero {
        simpa using h_h,
      },
      case succ {
        simp at h_h,
        cases h_c : P1.step {ip := some i, regs := regs},
        rw h_c at h_h,
        cases ip,
        case none {
          rw prog.halt_fix_step_t at h_h,
          simp at h_h,
          use 1,
          simp,
          convert seq.preserves_step_1 h_c,
          exact h_h.symm,
        },
        refine prog.steps_to_trans _ _ (h_w_ih h_h),
        use 1, simp,
        exact seq.preserves_step_1 h_c,
      },
    end

  lemma seq.preserves_steps_2 {i : fin ic2} {regs regs' : fin rc → ℕ}
    (h : ⟨some i, regs⟩ [P2]==>* config.halted regs')
    : ⟨seq.loc_map_2 P1 P2 (some i), regs⟩ [seq P1 P2]==>* ⟨none,regs'⟩
    := by
      cases ic2,
      case zero {
        exact fin.elim0 i,
      },
      simp,
      cases h, induction h_w generalizing i regs,
      case zero {
        simpa using h_h,
      },
      case succ {
        simp at h_h,
        cases h_c : P2.step {ip := some i, regs := regs},
        rw h_c at h_h,
        cases ip,
        case none {
          rw prog.halt_fix_step_t at h_h,
          simp at h_h,
          use 1,
          simp,
          convert seq.preserves_step_2 h_c,
          exact h_h.symm,
        },
        refine prog.steps_to_trans _ _ (h_w_ih h_h),
        use 1, simp,
        exact seq.preserves_step_2 h_c,
      },
    end

eorem seq.behavior {r1 r2 r3 : fin rc → ℕ}
(h1 : ⟨config.init_ip rc ic1, r1⟩ [P1]==>* config.halted r2)
(h2 : ⟨config.init_ip rc ic2, r2⟩ [P2]==>* config.halted r3)
: ⟨config.init_ip rc (ic1+ic2), r1⟩ [seq P1 P2]==>* config.halted r3
    := by
      have phase1 : ⟨config.init_ip rc (ic1+ic2), r1⟩ [seq P1 P2]==>* ⟨seq.midpoint_ic P1 P2, r2⟩
        := by
        cases ic1,
        case zero {
          simp [config.init_ip] at h1 |-,
          cases h1,
          simp [prog.halt_fix_step_t] at h1_h,
          rw h1_h,
          use 0,
          simp [seq.midpoint_ic],
          cases ic2, simp, simp, congr,
        },
        simp at h1,
        convert seq.preserves_steps_1 h1,
        induction ic2,
        refl, refl,
      end,
      have phase2 : ⟨seq.midpoint_ic P1 P2, r2⟩ [seq P1 P2]==>* config.halted r3
        := by
        cases ic2,
        case zero {
          simp [config.init_ip] at h2 |-,
          cases h2,
          simp [prog.halt_fix_step_t] at h2_h,
          rw h2_h,
          use 0,
          simp [seq.midpoint_ic],
        },
        simp at h2,
        exact seq.preserves_steps_2 h2,
        end,
      exact prog.steps_to_trans (seq P1 P2) phase1 phase2,
    end

end

def loop {rc icp : ℕ} (P : prog rc icp.succ) : prog rc.succ icp.succ.succ
  := fin.cons (instr.dec 0 (some 1) none)
      (instr.map_locs (λ l, match l with some x := some x.succ | none := some 0 end)
        ∘ instr.map_regs (λ r, r.succ)
        ∘ P)

namespace loop
  variables {rc icp : ℕ} (P : prog rc icp.succ)
      (f_P : (fin rc → ℕ) → (fin rc → ℕ))
      (hf : ∀ regs, ⟨config.init_ip rc icp.succ,regs⟩ [P]==>* {ip := none, regs := f_P regs})

  lemma preserves_step (x : ℕ) (i : fin icp.succ) (ip' : option (fin icp.succ))
    (regs regs' : fin rc → ℕ)
    (h : ⟨some i, regs⟩ [P]==> ⟨ip', regs'⟩)
    : ⟨some i.succ, fin.cons x regs⟩ [loop P]==>
        ⟨match ip' with none := some 0 | some x := x.succ end, fin.cons x regs'⟩
    := by
      simp [loop, prog.step] at h |-,
      cases h_i : P i,
      case inc : r l {
        simp [prog.step, h_i] at h |-,
        rw [h.1, ←fin.cons_update, h.2], simp,
        cases ip',
        simp [_match_1],
        simp [_match_1],
        congr,
      },
      case dec : r l k {
        simp [prog.step, h_i] at h |-,
        cases h_r : regs r,
        simp [prog.step, _match_1, h_r] at h |-,
        rw [h.1, h.2], simp [_match_1],
        cases ip',
        simp [_match_1],
        simp [_match_1],
        congr,
        simp [prog.step, _match_1, h_r] at h |-,
        rw [h.1, ←fin.cons_update, h.2], simp [_match_1],
        cases ip',
        simp [_match_1],
        simp [_match_1],
        congr,
      },
    end

  lemma preserves_steps (x : ℕ) (i : fin icp.succ)
    (regs regs' : fin rc → ℕ)
    (h : ⟨some i, regs⟩ [P]==>* ⟨none, regs'⟩)
    : ⟨some i.succ, fin.cons x regs⟩ [loop P]==>*
        ⟨some 0, fin.cons x regs'⟩
    := by
      cases h, induction h_w generalizing i regs,
      case zero {
        simp at h_h, contradiction,
      },
      rw function.iterate_succ_apply at h_h,
      cases h_step : P.step ⟨some i, regs⟩,
      rw h_step at h_h,
      cases ip,
      case none {
        simp [prog.halt_fix_step_t] at h_h,
        rw h_h at h_step,
        use 1, simp,
        exact preserves_step P x i none regs regs' h_step,
      },
      have : ⟨some i.succ, fin.cons x regs⟩ [loop P]==>* ⟨some ip.succ, fin.cons x regs_1⟩,
        use 1, exact preserves_step P x i (some ip) regs regs_1 h_step,
      refine prog.steps_to_trans (loop P) this _, clear this,
      exact h_w_ih ip regs_1 h_h,
    end
  
  include hf

  theorem behavior
    : ∀ n regs, {ip := some 0, regs := fin.cons n regs}
        [loop P]==>* {ip := none, regs := fin.cons 0 (f_P^[n] regs)}
    := by
      intros,
      induction n generalizing regs,
      case zero {
        use 1, simp [loop, prog.step],
      },
      have step_1 : ⟨some 0, fin.cons n_n.succ regs⟩ [loop P]==>* ⟨some 1, fin.cons n_n regs⟩,
        use 1, simp [loop, prog.step, fin.update_cons_zero],
      have step_2 : ⟨some 1, fin.cons n_n regs⟩ [loop P]==>* ⟨some 0, fin.cons n_n (f_P regs)⟩,
        refine preserves_steps P n_n 0 regs (f_P regs) _,
        exact hf regs,
      have step_12 := prog.steps_to_trans _ step_1 step_2,
      exact prog.steps_to_trans _ step_12 (n_ih (f_P regs)),
    end
end loop

def reset : prog 1 1 := ![instr.dec 0 (some 0) none]

lemma reset.behavior (n : ℕ)
  : (config.init n) [reset]==>* (config.halted (![0]))
  := by
    use n.succ,
    induction n, simpa [reset, prog.step],
    rw function.iterate_succ_apply,
    conv {
      to_lhs,
      congr, skip, skip,
      simp [reset, prog.step, fin.update_cons_zero],
    },
    simpa using n_ih,
  end

@[simp] def mov.loop_prog : prog 1 1 := ![instr.inc 0 none]
def mov : prog 2 2 := loop (mov.loop_prog)

theorem mov.behavior {n m : ℕ}
  : ⟨some 0, ![n, m]⟩ [mov]==>* ⟨none, ![0, n+m]⟩
  := by have :=
        loop.behavior mov.loop_prog (λ regs, regs <-[0] (regs 0).succ)
        (by intros, use 1, dsimp [prog.step], refl, end) n ![m],
    convert this, clear this,
    induction n, simp,
    rw function.iterate_succ_apply', rw ←n_ih,
    simp [matrix.vec_cons], rw fin.update_cons_zero, congr,
    exact nat.succ_add n_n m,
  end

@[simp] def dup.loop_prog : prog 2 2 := ![instr.inc 0 (some 1), instr.inc 1 none]
lemma dup.loop_prog.behavior (regs : fin 2 → ℕ)
  : ⟨some 0, regs⟩ [dup.loop_prog]==>* ⟨none, ![(regs 0).succ, (regs 1).succ]⟩
  := by
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
  := by have :=
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
  := by
    have db := dup.behavior n 0 0, simp at db,
    have h_c1 : ![0,n,n] = embed.reg_map ![inl 1, inl 0, inr n] ![n, 0]
        := by ext, fin_cases x, iterate { simp, }, end,
    rw h_c1 at db,
    have em1 := embed.behavior mov ![1,0] ![inl 1, inl 0, inr n] (by 
        split, intro, fin_cases r, iterate {simp,},
        intro, fin_cases r', iterate {simp,},
      end) (@mov.behavior n 0),
    have h_c2 : embed.reg_map ![inl 1, inl 0, inr n] ![0, n + 0] =
                embed.reg_map ![inl 1, inr 0, inl 0] ![n, n]
        := by ext, fin_cases x, iterate { simp, }, end,
    rw h_c2 at em1,
    have em2 := embed.behavior mov ![2,0] ![inl 1, inr 0, inl 0] (by 
        split, intro, fin_cases r, iterate {simp,},
        intro, fin_cases r', iterate {simp,},
      end) (@mov.behavior n n),
    have h_c3 : embed.reg_map ![inl 1, inr 0, inl 0] ![0, n + n] =
                ![2*n, 0, 0]
        := by ext, fin_cases x, iterate {simp, abel,}, end,
    rw h_c3 at em2,
    have s1 := seq.behavior em1 em2,
    have s2 := seq.behavior db s1,
    convert s2,
    simp, ext, fin_cases x, iterate { simp, simpa, },
  end
end

def pair : prog 4 8 := loop double

def pair.behavior (n m : ℕ)
  : ⟨some 0, ![n, m, 0, 0]⟩ [pair]==>* ⟨none, ![0, 2^n * m, 0, 0]⟩
  := by
    refine loop.behavior double (λ r, ![2 * r 1, r 2, r 3]) _,
  end

def div2 : prog 3 4 :=
  ![
    instr.dec 0 (some 1) none,
    instr.dec 0 (some 2) (some 3),
    instr.inc 1 (some 0),
    instr.inc 2 none
  ]

def div2.behavior (n a b : ℕ)
  : ⟨some 0, ![n,a,b]⟩ [div2]==>* ⟨none, ![0,a + (n / 2),b + (n % 2)]⟩
  := by
    induction h : (n/2) generalizing a,
    case zero {
      cases n,
      use 1, simp [div2, prog.step],
      cases n,
      use 3, simp [div2, prog.step],
      ext, fin_cases x, iterate {simpa},
    },
    refine prog.steps_to_trans _ _ (n_ih a.succ),
  end

end progs

/- Encodable type where an RM can recognize
    valid/invalid encodings (to prevent adding
    computational power via the encoding) -/
class rmcodable (α : Type*)
  := (to_Encodable : Encodable α)
      {coding_rcp coding_icp : ℕ} (coding_P : prog coding_rcp.succ coding_icp.succ)
      (h : ∀ n, (Encodable.encode (Encodable.decode α n)) ∈ coding_P.eval n)

instance rmcodable_to_Encodable {α : Type*} [rmcodable α] : Encodable α
  := rmcodable.to_Encodable

namespace rmcodable
  section
    variables {α : Type*} [c : rmcodable α]

    @[simp] def encode : α → ℕ := c.to_Encodable.encode
    @[simp] def decode : ℕ → option α := c.to_Encodable.decode
  end
  
  def of_equiv {β} (α) [c : rmcodable α] (e : β ≃ α) : rmcodable β
    := let beta_enc := Encodable.of_equiv α e in
      ⟨beta_enc, c.coding_P, by
        intros, have := @rmcodable.h _ c n,
        rw prog.eval_mem_iff_steps at this |-,
        cases this, use this_w,
        have : Encodable.encode (Encodable.decode α n) = @Encodable.encode _ (@Encodable.option _ beta_enc) (@Encodable.decode β beta_enc n),
          simp [Encodable.encode, Encodable.decode],
          cases Encodable.decode α n,
          dsimp, refl,
          dsimp, simp,
        rw ←this, exact this_h,
      end⟩
  
  instance nat : rmcodable ℕ := ⟨Encodable.nat, progs.succ, by
      intros, rw prog.eval_mem_iff_steps, use ![],
      exact progs.succ.behavior n,
    end⟩

  instance fin (n) : rmcodable (fin n)
    := ⟨Encodable.fin n,
      (sorry : prog 1 1), sorry
    ⟩

  instance prod {α β} [rmcodable α] [rmcodable β] : rmcodable (α × β)
    := ⟨Encodable.prod,
      (sorry : prog 1 1),
      sorry
    ⟩

  instance sum {α β} [rmcodable α] [rmcodable β] : rmcodable (α ⊕ β)
    := ⟨Encodable.sum,
      (sorry : prog 1 1),
      sorry
    ⟩

  instance option {α : Type*} [ae : Encodable α] : rmcodable (option α)
    := ⟨Encodable.option,
      (sorry : prog 1 1), sorry
    ⟩

  instance list {α : Type*} [ae : Encodable α] : rmcodable (list α)
    := ⟨Encodable.list,
      (sorry : prog 1 1), sorry
    ⟩

  instance instr : rmcodable (Instr R L)
    := of_equiv _ instr.equiv_destr

  instance : rmcodable (prog rc ic)
    := sorry

end rmcodable

namespace prog
  def apply {rcp ic : ℕ} (P : prog rcp.succ ic)
      {α β : Type*} [rmcodable α] [rmcodable β] : α →. β
    := λ a, (P.eval (rmcodable.encode a)).bind
              (roption.of_option ∘ (@rmcodable.decode β _))
  
  def add : prog 3 10 := sorry
  theorem add.behavior : add.apply = pfun.lift (λ pair : ℕ × ℕ, pair.fst + pair.snd)
    := by
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
