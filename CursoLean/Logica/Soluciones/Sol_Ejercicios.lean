import Mathlib.Tactic

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
