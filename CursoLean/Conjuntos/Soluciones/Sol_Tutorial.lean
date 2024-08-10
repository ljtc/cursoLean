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
variable (ι : Type*) (A B : ι → Set α)


--## Ejemplos

--### Con subconjuntos
example : s ⊆ s ∪ t := by
  intro x xs
  rw [mem_union]
  left
  exact xs

example : s ∩ t ⊆ s := by
  intro x
  rw [mem_inter_iff]
  intro ⟨xs, _⟩
  exact xs

--se puede usar `rw [...]` es una hipótesis
example : s ∩ t ⊆ s := by
  intro x h
  rw [mem_inter_iff] at h
  rcases h with ⟨xs, _⟩
  exact xs

example : ∅ ⊆ s := by
  intro x h
  contradiction

example : s ⊆ ⊤ := by
  intro x _
  trivial


--### Con igualdad
--pasando a lógica
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  ext x; simp only [mem_inter_iff]; constructor
  · intro ⟨⟨xs, xt⟩, xu⟩
    exact ⟨xs, ⟨xt, xu⟩⟩
  · intro ⟨xs, ⟨xt, xu⟩⟩
    exact ⟨⟨xs, xt⟩, xu⟩


--directamente como en conjuntos
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  ext x; constructor
  · intro ⟨⟨xs, xt⟩, xu⟩
    exact ⟨xs, ⟨xt, xu⟩⟩
  · intro ⟨xs, ⟨xt, xu⟩⟩
    exact ⟨⟨xs, xt⟩, xu⟩

--usando `calc`
example : s ∩ t ∩ u = s ∩ (t ∩ u) := by
  ext x
  calc x ∈ s ∩ t ∩ u
    _ ↔ x ∈ s ∩ t ∧ x ∈ u := by rw [mem_inter_iff]
    _ ↔ (x ∈ s ∧ x ∈ t) ∧ x ∈ u := by rw [mem_inter_iff]
    _ ↔ x ∈ s ∧ (x ∈ t ∧ x ∈ u) := by rw [and_assoc]
    _ ↔ x ∈ s ∧ (x ∈ t ∩ u) := by rw [<-mem_inter_iff]
    _ ↔ x ∈ s ∩ (t ∩ u) := by rw [<-mem_inter_iff]

example (h : s ⊆ t) : s ∪ t = t := by
  ext x; constructor
  · rintro (xs | xt)
    · apply h
      exact xs
    · exact xt
  · intro xt
    right
    exact xt


--### Con diferencia
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x h
  rw [mem_diff, mem_diff] at h
  rcases h with ⟨⟨xs, xnt⟩, xnu⟩
  rw [mem_diff]
  constructor
  · exact xs
  · rintro (xt | xu)
    · contradiction
    · contradiction

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x ⟨⟨xs, xnt⟩, xnu⟩
  constructor
  · exact xs
  · rintro (xt | xu)
    · exact xnt xt
    · exact xnu xu


-- ### Con complemento
example : s ∩ sᶜ = ∅ := by
  ext x; constructor
  · intro ⟨xs, xcs⟩
    rw [mem_compl_iff] at xcs
    exact xcs xs
  · intro xv
    contradiction

example : s ∪ sᶜ = ⊤ := by
  ext x; constructor
  · intro _
    trivial
  · intro _
    by_cases xs : x ∈ s
    · left; exact xs
    · right; exact xs


--### Con intersecciones arbitrarias
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x; constructor
  · intro h
    simp only [mem_iInter, mem_inter_iff] at h
    simp only [mem_inter_iff, mem_iInter]
    constructor
    · intro i
      rcases h i with ⟨xai, _⟩
      exact xai
    · intro i
      obtain ⟨_, xbi⟩ := h i
      exact xbi
  · simp only [mem_inter_iff, mem_iInter]
    intro ⟨xa, xb⟩ i
    constructor
    · exact xa i
    · exact xb i

example : (⋃ i, A i ∪ B i) = (⋃ i, A i) ∪ ⋃ i, B i := by
  ext x; constructor
  · intro h
    rw [mem_iUnion] at h
    rcases h with ⟨i, (xai | xbi)⟩
    · left
      rw [mem_iUnion]
      use i
    · right
      rw [mem_iUnion]
      use i
  · rintro (xa | xb)
    · rw [mem_iUnion] at xa
      rcases xa with ⟨i, xai⟩
      rw [mem_iUnion]
      use i
      left
      exact xai
    · rw [mem_iUnion] at xb
      obtain ⟨i, xbi⟩ := xb
      rw [mem_iUnion]
      use i
      right
      exact xbi
