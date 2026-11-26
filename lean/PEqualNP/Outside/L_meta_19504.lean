import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19504 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [0, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
