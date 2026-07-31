import Mathlib

open Complex Real MeasureTheory Filter
open scoped Topology

#check Filter.Frequently
#check Filter.frequently_iff
#check Filter.frequently_def
#check Filter.Eventually
#print Filter.Frequently

example (p : ℝ → Prop) (l : Filter ℝ) : ∃ᶠ x in l, p x ↔ ¬ (∀ᶠ x in l, ¬ p x) := by
  rfl

example (p : ℝ → Prop) (l : Filter ℝ) (h : {x : ℝ | p x} ∈ l) : ∃ᶠ x in l, p x := by
  exact (Filter.frequently_iff.mpr ?_)  -- placeholder
  sorry

#check Filter.Eventually.of_forall
#check Filter.Frequently.of_mem
#check Filter.Eventually.frequently
#check Filter.frequently_of_mem

example (p : ℝ → Prop) (l : Filter ℝ) (h : {x : ℝ | p x} ∈ l) : ∃ᶠ x in l, p x := by
  rw [Filter.frequently_iff]
  intro U hU
  have hU' : (U ∩ {x : ℝ | p x}).Nonempty := by
    exact Filter.nonempty_of_mem (Filter.inter_mem hU h)
  rcases hU' with ⟨x, hxU, hxp⟩
  exact ⟨x, hxU, hxp⟩

example : (fun x : ℝ => x = x) ∈ 𝓝[≠] (2 : ℝ) := by
  exact univ_mem

example : ∃ᶠ x in 𝓝[≠] (2 : ℝ), x = x := by
  exact Filter.frequently_of_mem univ_mem

/-- The frequently condition from a set in the filter. -/
example (p : ℝ → Prop) (l : Filter ℝ) (h : {x : ℝ | p x} ∈ l) : ∃ᶠ x in l, p x := by
  exact Filter.frequently_of_mem h
