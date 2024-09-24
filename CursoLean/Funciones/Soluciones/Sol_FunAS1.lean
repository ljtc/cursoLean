import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

open Set Function

variable (α β γ ι : Type)
variable (f : α → β) (g : β → γ) (f₁ f₂ : β → α)
variable (s t : Set α) (u v : Set β)
variable (A : ι → Set α) (B : ι → Set β)


--# Imágenes directas e inversas

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y
  simp only [mem_image]
  intro ⟨x, ⟨xs, fxy⟩⟩
  use x; constructor
  · apply h
    exact xs
  · exact fxy

example : f '' ⋂ i, A i ⊆ ⋂ i, f '' (A i) := by
  intro y
  simp only [mem_image, mem_iInter]
  intro ⟨x, ⟨xa, fxy⟩⟩ i
  use x; constructor
  · apply xa
  · exact fxy

example : f '' ⋃ i, A i = ⋃ i, f '' (A i) := by
  ext y; constructor
  · simp only [mem_image, mem_iUnion]
    intro ⟨x, ⟨⟨i, xai⟩, fxy⟩⟩
    use i
    use x
  · simp only [mem_iUnion, mem_image]
    intro ⟨i, ⟨x, ⟨xai, fxy⟩⟩⟩
    use x; constructor
    · use i
    · exact fxy

example (h : u ⊆ v) : f⁻¹' u ⊆ f⁻¹' v := by
  intro x xif
  simp only [mem_preimage] at *
  apply h
  exact xif

example : f⁻¹' ⋃ i, B i = ⋃ i, f⁻¹' (B i) := by
  ext x; constructor
  · simp only [mem_preimage, mem_iUnion]
    intro ⟨i, h⟩
    use i
  · simp only [mem_preimage, mem_iUnion]
    intro ⟨i, h⟩
    use i

/-
Después de aplicar `ext x` se puede intentar reducir el enunciado
a proposiciones lógicas. Si se hace esto se llegará a la misma
fórmula de ambos lados del `↔`. Por lo tanto, el simplificador
de Lean puede demostrar esto
-/
example : f⁻¹' ⋃ i, B i = ⋃ i, f⁻¹' (B i) := by
  ext x
  simp

example : f ⁻¹' ⋂ i, B i = ⋂ i, f⁻¹' (B i) := by
  ext x; constructor
  · simp only [mem_preimage, mem_iInter]
    intro h i
    apply h
  · simp only [mem_preimage, mem_iInter]
    intro h i
    apply h

/-
El simplificador de Lean puede reducir las expresiones de la
equivalencia hasta llegar a la misma espresión de ambos lados
del `↔` y cerrar el goal por "reflexividad".
-/
example : f ⁻¹' ⋂ i, B i = ⋂ i, f⁻¹' (B i) := by
  ext x
  simp

example : f⁻¹' ⊤ = ⊤ := by
  ext x
  rw [mem_preimage]
  rfl

example : f⁻¹' (u \ v) = (f⁻¹' u) \ (f⁻¹' v) := by
  ext x; constructor
  · intro h
    rw [mem_diff, mem_preimage]
    rw [mem_preimage, mem_diff] at h
    obtain ⟨fu, fnv⟩ := h
    constructor
    · exact fu
    · intro fv
      rw [mem_preimage] at fv
      exact fnv fv
  · intro h
    rw [mem_preimage, mem_diff]
    rw [mem_diff, mem_preimage] at h
    obtain ⟨fu, xnv⟩ := h
    constructor
    · assumption
    · intro fv
      rw [<-mem_preimage] at fv
      contradiction

--De nuevo, basta con simplificar las expresiones
example : f⁻¹' (u \ v) = (f⁻¹' u) \ (f⁻¹' v) := by
  ext x
  simp


--## Combinación de las dos

example : f '' (f⁻¹' u) ⊆ u := by
  intro y h
  rw [mem_image] at h
  obtain ⟨x, ⟨xfi, fxy⟩⟩ := h
  rw [mem_preimage] at xfi
  rw [<-fxy]
  exact xfi

example : s ⊆ f⁻¹' (f '' s) := by
  intro x xs
  rw [mem_preimage, mem_image]
  use x


--# Funciones inyectivas

example : Injective (@id α) := by
  intro x y
  rw [id, id]
  intro h
  exact h

example (h : Injective f) : f⁻¹' (f '' s) ⊆ s := by
  intro x xf
  rw [mem_preimage, mem_image] at xf
  obtain ⟨x', ⟨xps, h'⟩⟩ := xf
  have : x' = x := by
    apply h
    assumption
  rw [<-this]
  exact xps

example (h : LeftInverse f₁ f) : Injective f := by
  intro x y xy
  have : f₁ (f x) = f₁ (f y) := by
    apply congrArg; assumption
  rw [h, h] at this
  exact this

example (injf : Injective f) (h1 : RightInverse f₁ f)
    (h2 : RightInverse f₂ f) : f₁ = f₂ := by
  funext y
  apply injf
  rw [h1, h2]


--# Funciones suprayectivas

example : Surjective (@id α) := by
  intro y
  use y
  rw [id]

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) := by
  intro y yu
  rw [mem_image]
  obtain ⟨x, fxy⟩ := h y
  use x; constructor
  · rw [mem_preimage, fxy]
    exact yu
  · exact fxy

example (h : RightInverse f₁ f) : Surjective f := by
  intro y
  use (f₁ y)
  rw [h]

example (surf : Surjective f) (h1 : LeftInverse f₁ f)
    (h2 : LeftInverse f₂ f) : f₁ = f₂ := by
  funext y
  obtain ⟨x, fxy⟩ := surf y
  rw [<-fxy, h1, h2]
