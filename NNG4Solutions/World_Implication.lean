import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition

namespace MyNat


-- World     :   Implication World
-- Level 2   :   0 + x = (0 + y) + 2   =>   x = y + 2

theorem impl_level_2 (x y : MyNat) : (zero + x = (zero + y) + two) → (x = y + two) := by
  intro h
  repeat rw [zero_add] at h
  exact h




-- World     :   Implication World
-- Level 9   :   x + 1 = 4   =>   x = 3
