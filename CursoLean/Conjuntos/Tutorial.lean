import Mathlib.Data.Set.Lattice

/-
# Conjuntos

En Lean los conjuntos se organizan por tipos, de tal forma que `Set α`
es la colección de conjuntos de tipo `α`. Podemos imeginar que `Set α`
es la potencia de `α` y cada conjunto `s : Set α` es un subconjunto de
`α`.

Al final veremos algunno ejemplos con uniones e intersecciones
arbitrarias. Para formalizar estas operaciones en Lean es necesario
hacer familias de conjuntos. Para ahacer esto primero necesitamos un
tipo `ι : Type` que servira como colección de índices y una función
`A : ι → Set α`. Esta función se interpretará como la familia
`{A i ∣ i ∈ ι}`, lo cual nos permitirá hacer la operaciones
`⋃ i, A i` y `⋂ i, A i`.


## Notación

Además de los conectivos y cuantificadores de la parte de lógica, en
esta sección usaremos los siguientes símbolos

| símbolo |    nombre    |    en Lean    |
| :-----_ | :----------- | :------------ |
| ∈       | pertenecia   | `\in`         |
| ⊆       | subconjunto  | `\sub`        |
| ∩       | intersección | `\cap`        |
| ∪       | unión        | `\cup`        |
| \       | diferencia   | `\\`          |
| ᶜ       | complemento  | `\complement` |
| ∅       | vacío        | `\empty`      |
| ⋃       | unión arb.   | `\bigcup`     |
| ⋂       | int. arb.    | `\bigcap`     |


## Tácticas

En esta sección usaremos las siguientes tácticas
* `rw [...]`
* `simp only [...]`
* `ext ...`
* `calc`


## Definiciones adicionales

Cuando se esta trabajando con algún concepto matemático lo ideal no es
empezar a hacer todo desde cero. Aquí usaremos las definiciones que ya
están en la biblioteca de matemáticas de Lean. Además de que será una
primera oportunidad de ver las convenciones de nombres que sigue Lean.
https://leanprover-community.github.io/contribute/naming.html

Se sugiere poner el cursor al final de cada línea o pasar el cursor
sobre el nombre para ver la definición y tener alguna explicación.
-/

--Permite usar las cosas de conjutos de "forma abreviada".
--En lugar de `Set.mem_union` se puede usar `mem_union`.
open Set

#check mem_setOf
#check subset_def
#check inter_def
#check mem_inter_iff
#check union_def
#check mem_union
#check mem_compl_iff
#check mem_iInter
#check mem_iUnion



--Sean s, t y u conjuntos de tipo `α`
variable (α : Type*) (s t u : Set α)
--Sean A y B familias de conjuntos
variable (ι : Type*) (A B : ι → Set α)


--## Ejemplos

--### Con subconjuntos
example : s ⊆ s ∪ t := by
  sorry

example : s ∩ t ⊆ s := by
  sorry

--se puede usar `rw [...]` es una hipótesis
example : s ∩ t ⊆ s := by
  sorry

example : ∅ ⊆ s := by
  sorry

example : s ⊆ ⊤ := by
  sorry


--### Con igualdad
--pasando a lógica
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  sorry


--directamente como en conjuntos
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  sorry

--usando `calc`
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  sorry

example (h : s ⊆ t) : s ∪ t = t := by
  sorry


--### Con diferencia
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry


-- ### Con complemento
example : s ∩ sᶜ = ∅ := by
  sorry

example : s ∪ sᶜ = ⊤ := by
  sorry


--### Con intersecciones arbitrarias
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  sorry

example : (⋃ i, A i ∪ B i) = (⋃ i, A i) ∪ ⋃ i, B i := by
  sorry
