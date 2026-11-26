import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19483 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3257437 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [16, 6]⟩, ⟨.not, [17]⟩, ⟨.and, [15, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
