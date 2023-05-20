import data.fintype.fin

def init : Π (ic : ℕ), option (fin ic)
  | 0 := none
  | (_+1) := some 0

example (ic1 ic2 : ℕ) : init (ic1.succ + ic2) = some (fin.cast_add ic2 0)
  := begin
    have : cast (begin congr' 2, exact nat.add_comm _ _, end) (init (ic2 + ic1.succ)) = init (ic1.succ + ic2),
    
  end