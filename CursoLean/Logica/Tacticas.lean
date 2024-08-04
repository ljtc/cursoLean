import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases
/-
# Tácticas para lógica
En este archivo veremos una breve descripción de las tácticas que se usarán en
la sección de lógica.

Se recomienda pasar el cursor sobre cada una de las tácticas para que VS Code de
algo de información sobre la táctica.
-/

variable (a b c : Prop)
variable (α : Type) (p q r : α → Prop)


/-
## sorry
En realidad `sorry` no es una táctica exclusiva para lógica, es una
"demostración" de cualquier cosa. Incluso es una demostración de cosas falsas,
por lo que no se debe confiar en una proposición que use `sorry` en su demostración.
-/
theorem fermats_last_theorem :
    ∀ (x y z : Int), ∀ n ≥ 3, x^n + y^n = z^n → x*y*z = 0 := by sorry

example : a ∧ ¬a := by sorry


/-
## intro
Dado el goal `a → b`, la táctica `intro ha` introduce una hipótesis local
`ha : a` y reemplaza el goal por `b`.

También se puede usar para introducir un elemento cuando se demustra un
enunciado universal. Si se quiere demostrar `∀ x, p x`, entonces `intro w`
introduce el término `w` y cambia el goal por `p w`
-/
example : a → b := by
  intro ha
  sorry

example : ∀ x, p x := by
  intro w
  sorry


/-
## exact
`exact` es una táctica para cerrar un goal. Su forma es `exact t` donde `t` es
el término que cierra el goal
-/
example (ha : a) : a := by
  exact ha


/-
## assumption
Esta es otra táctica para cerrar un goal. En este caso Lean busca entre el
conjunto de hipótesis y las compara con el goal.
-/
example (ha : a) (hb : b) (hc : c) : b := by
  assumption


/-
## apply
Esta táctica se usa para "razonar hacia atrás". Si tenemos una hipótesis
`h : a → b` y queremos demostrar `b`, entonces `apply h` cambiara el goal, ahora
tenemos que demostrar `a`.

En general, `apply` trata de unificar el goal con el término `h`. Si logra la
unificación entonces crea un goal por cada premisa de `h`
-/
example (h : a → b) (ha : a) : b := by
  apply h
  exact ha

example (ha : a) (hb : b) (h : a → b → b)  : b := by
  apply h
  . exact ha
  . exact hb


/-
## rcases
Esta es una táctica bastante general para destruir hipótesis. Sólo veremos
algunas formas básicas de cómo se usa.

Si una de nuestras hipótesis es `h : a ∨ b`, entonces `rcases h with (ha | hb)`
divide la demostración en dos casos, uno suponiendo `ha : a` y otro suponiendo
`hb : b`.

Si tenemos `h : a ∧ b`, entonces `rcases h with ⟨ha, hb⟩` reemplaza `h` por las
dos hipotesis `ha : a` y `hb : b`.
-/
example (h : a ∨ b) : c := by
  rcases h with (ha | hb)
  . sorry
  . sorry

example (h : a ∧ b) : a := by
  rcases h with ⟨ha, _⟩
  assumption


/-
## constructor
Cuando el goal es una conjunción, digamos `a ∧ b`, se usa `constructor` para
romper la conjunción y crear dos goals, `a` y `b`.

Notemos que, por definición, el bicondicional tambien es una conjunción
-/
example (ha : a) (hb : b) : a ∧ b := by
  constructor
  . exact ha
  . exact hb

example : a ↔ b := by
  constructor
  . sorry
  . sorry


/-
## left y right
Estas tácticas se usan cuando se quiere demostrar una conjunción y se sabe qué
lado de la conjunción es el que va a demostrar.
-/
example (ha : a) : a ∨ b := by
  left
  exact ha

example (hb : b) : a ∨ b := by
  right
  exact hb


/-
## by_contra
Esta táctica sirve para hacer demostraciones por contradicción. Si tuvieramos
que demostrar.

Requiere `import Mathlib.Tactic.ByContra`
-/
example : a := by
  by_contra hna
  sorry


/-
## by_cases
Esta táctica es el tercero excluido. Así, `by_cases h : a` divide la
demostración en dos casos, uno suponiendo `h : a` y otro con `h : ¬a`.

Requiere `import Mathlib.Tactic.Cases`
-/
example : a ∨ ¬a := by
  by_cases h : a
  . left; exact h
  . right; exact h
