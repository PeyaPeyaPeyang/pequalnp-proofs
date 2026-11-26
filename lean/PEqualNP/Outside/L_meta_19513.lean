import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19513 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16269878 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.and, [10, 0]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [4, 9]⟩, ⟨.not, [14]⟩, ⟨.and, [13, 15]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [16, 17]⟩], 18⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
