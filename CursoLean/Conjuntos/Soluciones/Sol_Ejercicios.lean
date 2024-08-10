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
  ext x; constructor
  · rintro (xs | xt)
    · right; exact xs
    · left ; exact xt
  · rintro (xt | xs)
    · right; exact xt
    · left; exact xs

example (h : s ⊆ t) : s ∩ t = s := by
  ext x; constructor
  · intro ⟨xs, _⟩
    exact xs
  · intro xs
    constructor
    · exact xs
    · apply h
      exact xs


/-
## Con diferencia

No usa tácticas que nos se hayan visto antes. Si es necesario recordar
la definición de diferencia poner el curso al final de la línea que
empieza con `#check`
-/
#check mem_diff

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      · left; exact xs
      · intro ⟨_, xt⟩
        exact xnt xt
    · constructor
      · right; exact xt
      · intro ⟨xs, _⟩
        exact xns xs
  · rintro ⟨(xs | xt), xni⟩
    · left; constructor
      · exact xs
      · intro xt
        exact xni ⟨xs, xt⟩
    · right; constructor
      · exact xt
      · intro xs
        exact xni ⟨xs, xt⟩

/-
## Con complemento
De nuevo, lo único que puede ser de relevancia para los siguientes
ejercicios es la definición de complemento
-/
#check mem_compl_iff

example (h : s ⊆ t) : s ∩ tᶜ = ∅ := by
  ext x; constructor
  · intro ⟨xs, xct⟩
    rw [mem_compl_iff] at xct
    apply xct
    apply h
    exact xs
  · intro _
    contradiction

example : (sᶜ)ᶜ = s := by
  ext x; constructor
  · intro xcc
    by_cases xs : x ∈ s
    · exact xs
    · rw [mem_compl_iff] at xcc
      rw [<-mem_compl_iff] at xs
      contradiction
  · rw [mem_compl_iff]
    intro xs xcs
    rw [mem_compl_iff] at xcs
    exact xcs xs


/-
## Con uniones e intersecciones arbitrarias
-/

example : s ∩ ⋃ i, A i = ⋃ i, s ∩ A i := by
  ext x; constructor
  · intro ⟨xs, xa⟩
    rw [mem_iUnion] at xa
    rcases xa with ⟨i, xai⟩
    rw [mem_iUnion]
    use i
    constructor
    · exact xs
    · exact xai
  · rw [mem_iUnion]
    intro ⟨i, ⟨xs, xai⟩⟩
    constructor
    · exact xs
    · rw [mem_iUnion]
      use i

--Sugerencia: usar by_cases en la contensión de derecha a izquierda
example : s ∪ ⋂ i, A i = ⋂ i, s ∪ A i := by
  ext x; constructor
  · rw [mem_iInter]
    rintro (xs | xa)
    · intro i
      left
      exact xs
    · rw [mem_iInter] at xa
      intro i
      right
      apply xa
  · intro h
    by_cases xs : x ∈ s
    · left
      exact xs
    · right
      rw [mem_iInter] at *
      intro i
      rcases (h i) with xss | xai
      · contradiction
      · exact xai
