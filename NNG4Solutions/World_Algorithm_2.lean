import NNG4Solutions.Define_MyNat
import NNG4Solutions.World_Addition




namespace MyNat

-- World     :   Algorithm World
-- Level 1   :   add_left_comm

theorem add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  -- Goal : a + b + c = b + (a + c)
  rw [add_comm a b]
  -- Goal : b + a + c = b + (a + c)
  rw [add_assoc]
  -- Goal : b + (a + c) = b + (a + c)
