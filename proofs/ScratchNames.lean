import Mathlib

#check Bool.false_and
#check Bool.and_false
#check Bool.true_and
#check Bool.and_true
#check Bool.not_false
#check Bool.not_true
#check decide_true
#check decide_false
#check of_decide_eq_true
#check decide_eq_true_eq
#check Fin.reduceLT
#check Nat.reduceLT
#check Bool.and_eq_true
#check Bool.not_eq_true
#check Bool.not_eq_false
#check Bool.or_eq_true
#check Bool.or_eq_false
#check Bool.decide_coe

example : decide ((4 : Fin 13) < 5) = true := by decide
example : decide ((6 : Fin 13) < 2) = false := by decide
example (x : Bool) : false && x = false := by rfl

example (x y z : Bool) : (x && y && z) = (x && (y && z)) := by rfl
example (x y z : Bool) : (x && y && z) = ((x && y) && z) := by
  cases x <;> cases y <;> cases z <;> decide

#check segment_subset_convexHull
#check Set.mem_range_self
#check left_mem_openSegment_iff
#check right_mem_openSegment_iff
#check Finset.card_filter_add_card_filter_neg
#check Finset.card_filter_add_card_filter_not
#check List.ofFn
#check List.all
#check List.any
#check List.foldl
#check BitVec.ofFin
#check BitVec.toFin
#check BitVec.add
