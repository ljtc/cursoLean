import Mathlib.Tactic

section prop
variable (a b c : Prop)

/-
## Implicación
Recuerda usar
* `intro`
* `apply`
-/
example : (a → b) → (b → c) → (a → c) := by
  intro hab hbc ha
  apply hbc
  apply hab
  exact ha

example : (a → b → c) → (a → b) → (a → c) := by
  intro h hab ha
  apply h
  · exact ha
  · apply hab
    exact ha


/-
## Conjunción
Recuerda usar las tácticas
* `rcases`
* `constructor`
-/
example : (a ∧ b) → b := by
  intro h
  rcases h with ⟨_, hb⟩
  exact hb

--destruyendo el `∧` al mismo tiempo que se introduce
example : (a ∧ b) → b := by
  intro ⟨_, hb⟩
  exact hb

example : a ∧ b → b ∧ a := by
  intro ⟨ha, hb⟩
  constructor
  · exact hb
  · exact ha


/-
## Disyunción
En estos ejercicios hay que usar
* `left` y `right`
* `rcases`
-/
example : b → a ∨ b := by
  intro hb
  right
  exact hb

example : a ∨ b → (a → c) → (b → c) → c := by
  intro h hac hbc
  rcases h with (ha | hb)
  · apply hac
    exact ha
  · apply hbc
    exact hb


/-
## Negación
Usa las siguientes tácticas
* `exfalso`
* `contradiction`
-/
example : a → ¬¬a := by
  intro ha hna
  apply hna ha


/-
## Lógica clásica
En esta sección hay que usar
* `by_cases`
* `by_contra`
-/
example : ¬¬a → a := by
  intro hn
  by_cases ha : a
  · exact ha
  · contradiction

example : ¬¬a → a := by
  intro hn
  by_contra hna
  contradiction

end prop



section fol

variable (α : Type) (p q r : α → Prop)

example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := by
  intro h
  constructor
  · intro a
    rcases (h a) with ⟨pa, _⟩
    exact pa
  · intro a
    rcases (h a) with ⟨_, qa⟩
    exact qa

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h h' a
  apply (h a)
  exact h' a


/-
Esta última es más difícil. Se sugiere usar el lema, aún así es
mucho más complicada que todo lo anteior.
-/

lemma c_iff_noc (c : Prop) : ¬(c ↔ ¬c) := by
  intro ⟨h1, h2⟩
  have nc : ¬c := by
    intro hc
    exact (h1 hc) hc
  have nnc : ¬¬c := by
    intro hnc
    exact hnc (h2 hnc)
  exact nnc nc

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have : shaves barber barber ↔ ¬shaves barber barber := by
    apply h barber
  exact (c_iff_noc (shaves barber barber)) this

end fol
