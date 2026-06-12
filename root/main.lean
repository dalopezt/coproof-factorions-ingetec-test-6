import «digitfactorialsum_upper_bound».«main»
import «digitfactorialsum_finite_solutions».«main»
import Definitions
theorem root : {n : ℕ | digitFactorialSum n = n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hbound := digitFactorialSum_upper_bound n h
    have hmem : n ∈ {n : ℕ | digitFactorialSum n = n ∧ n ≤ 2540160} := by
      simp only [Set.mem_setOf_eq]
      exact ⟨h, hbound⟩
    rw [digitFactorialSum_finite_solutions] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    exact hmem
  · intro h
    have hmem : n ∈ ({1, 2, 145, 40585} : Set ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact h
    rw [← digitFactorialSum_finite_solutions] at hmem
    simp only [Set.mem_setOf_eq] at hmem
    exact hmem.1
