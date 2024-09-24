import Mathlib.Data.Set.Basic

variable (α : Type)
variable (s t u : Set α)

open Set

--# `Set α` es un álgebra de Boole
--## Conmutatividad

example : s ∩ t = t ∩ s := by
  sorry

example : s ∪ t = t ∪ s := by
  sorry


--## Asociatividad

example : s ∩ (t ∩ u) = (s ∩ t) ∩ u := by
  sorry

example : s ∪ (t ∪ u) = (s ∪ t) ∪ u := by
  sorry


--## Distributividad

example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  sorry

example : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := by
  sorry


--## Idempotencia

example : s ∪ s = s := by
  sorry

example : s ∩ s = s := by
  sorry


--## Absorción

example : s ∩ (t ∪ s) = s := by
  sorry

example : s ∪ (t ∩ s) = s := by
  sorry


--## Neutro

example : s ∩ ⊤ = s := by
  sorry

example : s ∪ ∅ = s := by
  sorry


--## Complemento

example : s ∪ sᶜ = ⊤ := by
  sorry

example : s ∩ sᶜ = ∅ := by
  sorry


--## Intersección es un ínfimo

example : s ∩ t ⊆ s := by
  sorry

example : s ∩ t ⊆ t := by
  sorry

example (h1 : u ⊆ s) (h2 : u ⊆ t) : u ⊆ s ∩ t := by
  sorry


--## Unión es un supremo

example : s ⊆ s ∪ t := by
  sorry

example : t ⊆ s ∪ t := by
  sorry

example (h1 : s ⊆ u) (h2 : t ⊆ u) : s ∪ t ⊆ u := by
  sorry


--## De Morgan

example : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  sorry

example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  sorry
