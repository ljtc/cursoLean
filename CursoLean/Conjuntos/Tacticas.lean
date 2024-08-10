import Mathlib.Data.Set.Lattice

/-
# Tácticas para conjuntos

En este archivo veremos una breve descripción de las tácticas que se
usarán en la sección de conjuntos.

Se recomienda pasar el cursor sobre cada una de las tácticas para que
VS Code de algo de información sobre la táctica.
 -/

variable (α : Type*) (s t u : Set α)
open Set

/-
## rw [...]
Con la táctica `rw [...]` podemos hacer sustituciones de iguales por
iguales. El sentido de la palabra "igual" en el enunciado anterior no
se refiere a la igualdad estricta sino a una relación de equivalencia.
-/
example (h1 : s = t) (h2 : t = u) : s = u := by -- ⊢ s = u
  rw [h1] -- ⊢ t = u
  rw [h2] -- cierra el goal
/-
Se pueden hacer muchas reescrituras en el mismo renglón.
-/
example (h1 : s = t) (h2 : t = u) : s = u := by
  rw [h1, h2]
/-
En Lean las igualdades tienen dirección, de tal forma que cuando usamos
`rw [h1]` se sustutye el lado izquierdo `s` por el lado derecho `t`.
Para hacer la sustitución en la otra dirección se usa `rw [<-h1]`.
-/
example (h1 : s = t) (h2 : t = u) : s = u := by -- ⊢ s = u
  rw [<-h2] -- ⊢ s = t
  rw [<-h1] -- cierra el goal

example (h1 : s = t) (h2 : t = u) : s = u := by
  rw [<-h2, <-h1]

example (a b c : Prop) (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c := by
  rw [h1, h2]


/-
## simp only [...]

El simplificador de Lean es muy poderoso y mientras estamos aprendiendo
a demostrar y formalizar las demostraciones en Lean, sólo usaremos esta
versión en la que debemos pasar el término que usa para simplificar.

Usado de esta forma, es una especie de `rw [...]` pero hace todas las
sustituciones posibles. Veamos la diferencia en un ejemplo:
-/
example : s ∩ t ∩ u ⊆ s ∩ (t ∩ u) := by
  intro x
  rw [mem_inter_iff, mem_inter_iff, mem_inter_iff, mem_inter_iff]
  -- ahora el goal está escrito en términos de conectivos
  sorry

example : s ∩ t ∩ u ⊆ s ∩ (t ∩ u) := by
  intro x
  simp only [mem_inter_iff]
  -- ahora el goal está escrito en términos de conectivos
  sorry


/-
## ext
Esta táctica es el axioma de extencionalidad en conjuntos. Se usa para
demostrar que dos conjuntos son iguales. Si quisieramos demostrar que
`s = t`, entonces `ext x` cambia el goal a demostrar una "doble
contensión". Por lo tanto, seguramente estará seguida de un
`constructor`. La variable `x` es un nombre arbitrario.
-/
example : s = t := by
  ext x; constructor
  · sorry
  · sorry


/-
## calc
Esta táctica nos permita hacer demostraciones que se siguen de la
aplicación sucesiva de la transitividad de una relación. Por ejemplo,
podemos razonar usando `calc` en aquellos luagares que se uso `rw`.
-/
example (h1 : s = t) (h2 : t = u) : s = u := by
  calc
    s = t := by exact h1
    _ = u := by exact h2

example (x y z : Nat) (h1 : x ≤ y) (h2: y ≤ z) : x ≤ z := by
  calc
    x ≤ y := by exact h1
    _ ≤ z := by exact h2
