import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

/-
# Funciones

Las funciones en Lean van de un tipo a otro. El conjunto de
funciones de `α` en `β` es un tipo que se denota con `α → β`.
Así, un término `f : α → β` es una función.

En la sección de conjuntos vimos que `Set α` se puede
interpretar como la potencia de `α`, de manera que `s : Set α`
es algo como "`s` es subconjunto de `α`". Con esto podremos
hacer calculos de imágenes diretas e inversas.

Otra cosa que comúnmente hacemos con funciones es reconocer
las que cumplen propiedades especiales, como las funciones
inyectivas, suprayectivas y biyectivas. Así que también haremos
algunas cosas con estos tipos de funciones.


## Notación

La notación adicional para esta sección de funciones es:

| símbolo | nombre         | en Lean  |
| :------ | :------------- | :------- |
| ()''    | imagen directa | `()''`   |
| ()⁻¹'   | imagen inversa | `()\- '` |


## Tácticas

Además de las tácticas de las secciones anteriores, posiblemente
usemos las siguientes:
* `funext ...`
* `obtain`


## Definiciones adicionales

De nuevo haremos uso de las definiciones que ya fuero  escritas en
la biblioteca Mathlib
-/

open Function
open Set

#check congrArg
#check funext
#check congrFun
#check mem_image
#check mem_preimage
#check comp
#check comp_apply
#print Injective
#print Surjective
#print Bijective
#print LeftInverse
#print RightInverse

--Sean `α` y `β`dos tipos
variable (α β γ : Type*)

--Sea `f` una función de `α` en `β`
variable (f : α → β)

--Sea `g` una función de `β` en `γ`
variable (g : β → γ)

--Sea `h` una función de `β` en `α`
variable (k : β → α)

--Sean `s`, `t` suconjuntos de `α` y `u`, `v` subconjuntos de `β`
variable (s t : Set α) (u v : Set β)


--## Ejemplos

--### Imagen directa
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · intro h
    rw [mem_image] at h
    rcases h with ⟨x, ⟨xst, fxy⟩⟩
    rcases xst with xs | xt
    · left
      rw [mem_image]
      use x
    · right
      rw [mem_image]
      use x
  · rintro (yis | yit)
    · rw [mem_image] at *
      rcases yis with ⟨x, ⟨xs, fxy⟩⟩
      use x
      constructor
      · left
        exact xs
      · exact fxy
    · rw [mem_image] at *
      rcases yit with ⟨x, ⟨xt, fxy⟩⟩
      use x
      constructor
      · right
        exact xt
      · exact fxy

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  rw [mem_image]
  rw [mem_union, mem_image, mem_image]
  constructor
  · rintro ⟨x, ⟨(xs | xt), fxy⟩⟩
    · left; use x
    · right; use x
  · rintro (⟨x, ⟨xs, fxy⟩⟩ | ⟨x, ⟨xt, fxy⟩⟩)
    · use x; constructor
      · left; exact xs
      · exact fxy
    · use x; constructor
      · right; exact xt
      · exact fxy


--### Imagen inversa
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x; constructor
  · intro h
    rw [mem_preimage] at h
    rcases h with ⟨fxu, fxv⟩
    constructor
    · exact fxu
    · exact fxv
  · intro ⟨h1, h2⟩
    rw [mem_preimage] at *
    constructor
    · exact h1
    · exact h2

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  rw [mem_preimage, mem_inter_iff]
  rw [mem_inter_iff, mem_preimage, mem_preimage]

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  simp


--### Funciones inyectivas
example (injf : Injective f) (injg : Injective g) :
    Injective (g ∘ f) := by
  rw [Injective]
  intro x y h
  apply injf
  apply injg
  exact h

example (injgf : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  intro x y h
  apply injgf
  rw [comp_apply, comp_apply]
  apply congrArg
  exact h

example (h : LeftInverse k f) : Injective f := by
  intro a b h1
  have : k (f a) = k (f b) := by
    apply congrArg
    assumption
  rw [LeftInverse] at h
  rw [<-(h a), <-(h b)]
  assumption

example (h : LeftInverse k f) : Injective f := by
  rw [LeftInverse] at h
  intro a b fab
  calc
    a = k (f a) := by apply (h a).symm
    _ = k (f b) := by rw [fab]
    _ = b       := by apply h


--### Funciones suprayectivas
example (surf : Surjective f) (surg : Surjective g) :
    Surjective (g ∘ f) := by
  rw [Surjective] at *
  intro z
  obtain ⟨y, gyz⟩ := by
    exact surg z
  obtain ⟨x, fxy⟩ := by
    exact surf y
  use x
  rw [comp_apply, fxy, gyz]

example (srgf: Surjective (g ∘ f)) : Surjective g := by
  rw [Surjective] at *
  intro z
  obtain ⟨x, cxz⟩ := by
    exact srgf z
  use (f x)
  exact cxz

example (h : RightInverse k f) : Surjective f := by
  intro y
  use k y
  rw [Function.RightInverse, LeftInverse] at h
  apply h
