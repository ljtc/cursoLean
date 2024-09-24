import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

open Set Function

variable (α β γ ι : Type)
variable (f : α → β) (g : β → γ) (f₁ f₂ : β → α)
variable (s t : Set α) (u v : Set β)
variable (A : ι → Set α) (B : ι → Set β)


--# Imágenes directas e inversas

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example : f '' ⋂ i, A i ⊆ ⋂ i, f '' (A i) := by
  sorry

example : f '' ⋃ i, A i = ⋃ i, f '' (A i) := by
  sorry

example (h : u ⊆ v) : f⁻¹' u ⊆ f⁻¹' v := by
  sorry

example : f⁻¹' ⋃ i, B i = ⋃ i, f⁻¹' (B i) := by
  sorry

/-
Después de aplicar `ext x` se puede intentar reducir el enunciado
a proposiciones lógicas. Si se hace esto se llegará a la misma
fórmula de ambos lados del `↔`. Por lo tanto, el simplificador
de Lean puede demostrar esto
-/
example : f⁻¹' ⋃ i, B i = ⋃ i, f⁻¹' (B i) := by
  sorry

example : f ⁻¹' ⋂ i, B i = ⋂ i, f⁻¹' (B i) := by
  sorry

/-
El simplificador de Lean puede reducir las expresiones de la
equivalencia hasta llegar a la misma espresión de ambos lados
del `↔` y cerrar el goal por "reflexividad".
-/
example : f ⁻¹' ⋂ i, B i = ⋂ i, f⁻¹' (B i) := by
  sorry

example : f⁻¹' ⊤ = ⊤ := by
  sorry

example : f⁻¹' (u \ v) = (f⁻¹' u) \ (f⁻¹' v) := by
  sorry

--De nuevo, basta con simplificar las expresiones
example : f⁻¹' (u \ v) = (f⁻¹' u) \ (f⁻¹' v) := by
  sorry


--## Combinación de las dos

example : f '' (f⁻¹' u) ⊆ u := by
  sorry

example : s ⊆ f⁻¹' (f '' s) := by
  sorry


--# Funciones inyectivas

example : Injective (@id α) := by
  sorry

example (h : Injective f) : f⁻¹' (f '' s) ⊆ s := by
  sorry

example (h : LeftInverse f₁ f) : Injective f := by
  sorry

example (injf : Injective f) (h1 : RightInverse f₁ f)
    (h2 : RightInverse f₂ f) : f₁ = f₂ := by
  sorry


--# Funciones suprayectivas

example : Surjective (@id α) := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) := by
  sorry

example (h : RightInverse f₁ f) : Surjective f := by
  sorry

example (surf : Surjective f) (h1 : LeftInverse f₁ f)
    (h2 : LeftInverse f₂ f) : f₁ = f₂ := by
  sorry
