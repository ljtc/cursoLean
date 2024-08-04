import Mathlib.Tactic

section prop

variable (a b c : Prop)

/-
## Implicación
Recuerda usar
* `intro`
* `apply`
-/
example : (a → b) → (b → c) → (a → c) := by sorry

example : (a → b → c) → (a → b) → (a → c) := by sorry


/-
## Conjunción
Recuerda usar las tácticas
* `rcases`
* `constructor`
-/
example : (a ∧ b) → b := by sorry

--destruyendo el `∧` al mismo tiempo que se introduce
example : (a ∧ b) → b := by sorry

example : a ∧ b → b ∧ a := by sorry


/-
## Disyunción
En estos ejercicios hay que usar
* `left` y `right`
* `rcases`
-/
example : b → a ∨ b := by sorry

example : a ∨ b → (a → c) → (b → c) → c := by sorry


/-
## Negación
Usa las siguientes tácticas
* `exfalso`
* `contradiction`
-/
example : a → ¬¬a := by sorry


/-
## Lógica clásica
En esta sección hay que usar
* `by_cases`
* `by_contra`
-/
example : ¬¬a → a := by sorry

example : ¬¬a → a := by sorry

end prop



section fol

variable (α : Type) (p q r : α → Prop)

example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := by sorry

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by sorry


/-
Esta última es más difícil. Se sugiere usar el lema, aún así es
mucho más complicada que todo lo anteior.
-/

lemma c_iff_noc (c : Prop) : ¬(c ↔ ¬c) := by
  intro ⟨h1, h2⟩
  have nc : ¬c := by sorry
  have nnc : ¬¬c := by sorry
  sorry

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  sorry

end fol
