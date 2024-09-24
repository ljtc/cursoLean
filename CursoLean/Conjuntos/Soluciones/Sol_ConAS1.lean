import Mathlib.Data.Set.Basic

variable (α : Type)
variable (s t u : Set α)

open Set

--# `Set α` es un álgebra de Boole
--## Conmutatividad

example : s ∩ t = t ∩ s := by
  ext x; constructor
  · intro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  · intro ⟨xt, xs⟩
    exact ⟨xs, xt⟩

example : s ∪ t = t ∪ s := by
  ext x
  rw [mem_union, mem_union, or_comm]


--## Asociatividad

example : s ∩ (t ∩ u) = (s ∩ t) ∩ u := by
  ext x
  rw [mem_inter_iff,mem_inter_iff]
  rw [mem_inter_iff,mem_inter_iff]
  rw [and_assoc]

example : s ∪ (t ∪ u) = (s ∪ t) ∪ u := by
  ext x; constructor
  · rintro (xs | (xt | xu))
    · left; left
      exact xs
    · left; right
      exact xt
    · right
      exact xu
  · rintro ((xs | xt) | xu)
    · left
      exact xs
    · right; left
      exact xt
    · right; right
      exact xu


--## Distributividad

example : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  calc x ∈ s ∩ (t ∪ u)
    _ ↔ x ∈ s ∧ (x ∈ t ∨ x ∈ u) := by
      rw [mem_inter_iff, mem_union]
    _ ↔ (x ∈ s ∧ x ∈ t) ∨ (x ∈ s ∧ x ∈ u) := by
      rw [and_or_left]
    _ ↔ x ∈ (s ∩ t) ∪ (s ∩ u) := by
      rw [<-mem_inter_iff,<-mem_inter_iff,<-mem_union]

example : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := by
  ext x
  simp only [mem_union, mem_inter_iff,or_and_left]


--## Idempotencia

example : s ∪ s = s := by
  ext x; constructor
  · rintro (xs | xs)
    assumption'
  · intro xs
    left
    assumption

example : s ∩ s = s := by
  ext x;
  rw [mem_inter_iff, and_self]


--## Absorción

example : s ∩ (t ∪ s) = s := by
  ext x; constructor
  · rintro ⟨xs, (_ | xss)⟩
    assumption'
  · intro xs; constructor
    · exact xs
    · right; exact xs

example : s ∪ (t ∩ s) = s := by
  ext x; constructor
  · rw [mem_union, mem_inter_iff]
    rintro (xs | ⟨_, xs⟩)
    assumption'
  · intro xs
    left
    exact xs


--## Neutro

example : s ∩ ⊤ = s := by
  ext x; constructor
  · intro ⟨xs, _⟩
    exact xs
  · intro xs
    constructor
    · exact xs
    · trivial

example : s ∪ ∅ = s := by
  ext x
  rw [mem_union, mem_empty_iff_false,or_false]


--## Complemento

example : s ∪ sᶜ = ⊤ := by
  ext x; constructor
  · rintro (_ | _)
    repeat'
      trivial
  · intro
    by_cases xs : x ∈ s
    · left; assumption
    · rw [<-mem_compl_iff] at xs
      right; assumption

example : s ∩ sᶜ = ∅ := by
  ext x
  rw [mem_inter_iff, mem_compl_iff,and_not_self_iff]
  rw [mem_empty_iff_false]


--## Intersección es un ínfimo

example : s ∩ t ⊆ s := by
  intro x ⟨xs, _⟩
  exact xs

example : s ∩ t ⊆ t := by
  intro x ⟨_, xt⟩
  exact xt

example (h1 : u ⊆ s) (h2 : u ⊆ t) : u ⊆ s ∩ t := by
  intro x xu
  constructor
  · apply h1; exact xu
  · apply h2; exact xu


--## Unión es un supremo

example : s ⊆ s ∪ t := by
  intro x xs
  left
  exact xs

example : t ⊆ s ∪ t := by
  intro x xt
  right
  exact xt

example (h1 : s ⊆ u) (h2 : t ⊆ u) : s ∪ t ⊆ u := by
  rintro x (xs | xt)
  · apply h1; exact xs
  · apply h2; exact xt


--## De Morgan

example : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  ext x; constructor
  · intro h
    rw [mem_compl_iff] at h
    by_cases xs : x ∈ s
    · right
      rw [mem_compl_iff]
      intro xt
      have : x ∈ s ∩ t := by
        constructor
        assumption'
      exact h this
    · left
      rw [mem_compl_iff]
      exact xs
  · rintro (xns | xnt)
    · rw [mem_compl_iff] at *
      intro ⟨xs, _⟩
      exact xns xs
    · rw [mem_compl_iff] at *
      intro ⟨_, xt⟩
      exact xnt xt

example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  ext x
  rw [mem_compl_iff, mem_union]
  rw [mem_inter_iff, mem_compl_iff,mem_compl_iff]
  push_neg
  rfl
