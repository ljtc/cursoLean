import Mathlib.Data.Set.Lattice

variable (α : Type) (s t u : Set α)
variable (ι : Type*) (A B : ι → Set α)

open Set

/-
## Con contensión

Todos estos deben empezar introduciendo un elemento que está
en el conjunto de la izquierda, algo como
`intro x h`
Recuerda que se puede destruir `h` al mismo tiempo que se
introduce, la forma de destruir depende de la forma de `h`.
Un ejemplo cuando `h` tiene una intersección:
`intro x ⟨xa, xb⟩`
En el caso cuando `h` es que `x` está en una unión se debe usar
`rintro x (xa | xb)`
-/

example (h : s ⊆ t) : u ∩ s ⊆ u ∩ t := by
  intro x ⟨xu, xs⟩
  constructor
  · exact xu
  · apply h
    exact xs

example (h : s ⊆ t) : u ∪ s ⊆ u ∪ t := by
  rintro x (xu | xs)
  · left; exact xu
  · right
    apply h
    exact xs


/-
## Con igualdad

Estos ejercicios deben empezar con
`ext x; constructor`
-/

example : s ∪ t = t ∪ s := by
  sorry

example (h : s ⊆ t) : s ∩ t = s := by
  sorry


/-
## Con diferencia

No usa tácticas que nos se hayan visto antes. Si es necesario recordar
la definición de diferencia poner el curso al final de la línea que
empieza con `#check`
-/
#check mem_diff

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

/-
## Con complemento
De nuevo, lo único que puede ser de relevancia para los siguientes
ejercicios es la definición de complemento
-/
#check mem_compl_iff

example (h : s ⊆ t) : s ∩ tᶜ = ∅ := by
  sorry

example : (sᶜ)ᶜ = s := by
  sorry


/-
## Con uniones e intersecciones arbitrarias
-/

example : s ∩ ⋃ i, A i = ⋃ i, s ∩ A i := by
  sorry

--Sugerencia: usar by_cases en la contensión de derecha a izquierda
example : s ∪ ⋂ i, A i = ⋂ i, s ∪ A i := by
  sorry
