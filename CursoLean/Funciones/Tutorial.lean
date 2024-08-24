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

--Sean `α` y `β`dos tipos
variable (α β γ : Type*)

--Sea `f` una función de `α` en `β`
variable (f : α → β) (g : β → γ)

--Sean `s`, `t` suconjuntos de `α` y `u`, `v` subconjuntos de `β`
variable (s t : Set α) (u v : Set β)


--## Ejemplos

--### Imagen directa
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  sorry


--### Imagen inversa
example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  sorry


--### Funciones inyectivas
example (injf : Injective f) (injg : Injective g) :
    Injective (g ∘ f) := by
  sorry

example (injgf : Injective (g ∘ f)) : Injective f := by
  sorry

--### Funciones suprayectivas
example (surf : Surjective f) (surg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

example (srgf: Surjective (g ∘ f)) : Surjective g := by
  sorry
