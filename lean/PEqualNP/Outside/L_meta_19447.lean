import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19447 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236078 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.and, [0, 5]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [11, 9]⟩, ⟨.not, [12]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [14, 1]⟩, ⟨.or, [13, 15]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
