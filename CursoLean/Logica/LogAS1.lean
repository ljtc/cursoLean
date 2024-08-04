import Mathlib.Tactic

section prop
variable (a b c : Prop)

/-
# Lógica de proposiciones

## Comportamiento estructural
Veremos que las proposiciones froman un álgebra de Boole.
Además de algunas propiedades en la misma línea.
-/

--conmutatividad de `∧` y `∨`
example : a ∧ b ↔ b ∧ a := by sorry


example : a ∨ b ↔ b ∨ a := by sorry

--asociatividad de ∧ y ∨
example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ c := by sorry

example : a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c := by sorry

--∧ y ∨ son idempotentes
example : a ∧ a ↔ a := by sorry

example : a ∨ a ↔ a := by sorry

--absorciones
example : a ∧ (a ∨ b) ↔ a := by sorry

example : a ∨ (a ∧ b) ↔ a := by sorry

--distributividades
example : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) := by sorry

example : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) := by sorry

-- complemento
example : a ∧ ¬a ↔ False := by sorry

/-
Nota:
Esta parte del complemento tiene implicaciones fuertes acerca del
tipo de lógica que vamos a trabajar
-/
example : a ∨ ¬a ↔ True := by sorry


/-
## Métodos de demostración
-/

--contrapuesta
example : (a → b) ↔ (¬b → ¬a) := by sorry

--contradicción
example : ((a → b) ∧ (a → ¬b)) → ¬a := by sorry

end prop




section fol

variable (α : Type) (p q : α → Prop)
variable (c : Prop)

/-
# Lógica de primer orden
-/

/-
## Donde la variable cuantificada no aparece
-/
example (a : α) : (∃ x : α, c) ↔ c := by sorry

example (a : α) : (∀ x : α, r) ↔ r := by sorry


/-
## Comportamioento con la conjunción
-/

-- ∀ con ∧
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by sorry

-- ∃ con ∧
-- sólo se vale una implicación
example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := by sorry

--consecuencia de lo anterior
example (a : α) : (∀ x, p x ∧ c) ↔ (∀ x, p x) ∧ c := by sorry

-- caso especial con ∃ y ∧
example : (∃ x, p x ∧ c) ↔ (∃ x, p x) ∧ c := by sorry


/-
## Comportamiento con la disyunción
-/

-- ∀ con ∨
-- sólo se vale una implicación
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by sorry

-- ∃ con ∨
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by sorry

-- consecuencioa de lo anterior
example (a : α) : (∃ x, p x ∨ c) ↔ (∃ x, p x) ∨ c := by sorry

-- caso especial
example : (∀ x, p x ∨ c) ↔ (∀ x, p x) ∨ c := by sorry


/-
## Comportamiento con la implicación
-/

-- ∀ con →
-- sólo se vale una implicación
example : (∀ x, p x → q x) → ((∀ x, p x) → (∀ x, q x)) := by sorry


-- caso especial, consecuente
example : (∀ x, p x → c) ↔ (∃ x, p x) → c := by sorry

example (a : α) : (∃ x, p x → c) ↔ (∀ x, p x) → c := by sorry

-- caso especial, antecedente
example (a : α) : (∃ x, c → p x) ↔ (c → ∃ x, p x) := by sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by sorry


/-
## Comportamiento con la negación
-/
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by sorry

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by sorry

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by sorry

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by sorry

end fol
