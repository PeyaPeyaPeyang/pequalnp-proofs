import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19473 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.and, [4, 7]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [12, 9]⟩, ⟨.not, [13]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [15, 9]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
