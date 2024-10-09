import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

/-
# Tácticas para números

Como siempre, se recomienda pasar el cursor sobre la táctica para
obtener información adicional.
-/

variable (R : Type*) [CommRing R]
variable (a b c : R)

/-
## nth_rw

Las tácticas de reescritura usan que si `x = y` entonces `φ(x) ≡ φ(y)`.
Sin embargo, la sutitución de variables común sustituye todas las
ocurrencias de `x` por `y`. Si quisieramos sustituir sólo algunas de
estas ocurrencias se usa `nth_rw n [...]`, donde `n` es el número de
la ocurrencia que será sustituida.
-/

--sustituir todas las ocurrencias de `a` por `b`
example (h : a = b) : a * c * a = b * c * a := by
  rw [h]-- ⊢ b * c * b = b * c * b

--sustituir la primera ocurrencia de `a` por `b`
example (h : a = b) : a * c * a = b * c * a := by
  nth_rw 1 [h]-- ⊢ b * c * a = b * c * a


/-
## norm_num

Cuando se trabaja con números concretos, como naturales, enteros, etc.,
y operaciones entre ellos, los resultados son un proceso de
"normalización" de tal forma que tenemos ciertas igualdades porque se
"normalizan" al mismo término.
-/
example : 1 + 5 = 6 := by
  norm_num

example : 4 * (3 + 3) = 2 * 10 + 4 := by
  norm_num


/-
## ring

Hay algunas cuentas que sabemos son ciertas y no nos gustaría tener que
demostrar cuando estamos haciendo algo más importante. Cuando estas
cuentas se demuestran con los axiomas de anillo conmutativo es posible
usar la táctica `ring`.
-/
example : 1 * a = a := by
  ring

example : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring


/-
## induction'

Dada una propiedad de números naturales `p : ℕ → Prop` podemos demostrar
`∀ n : ℕ, p n` por inducción. La sintaxis de la táctica es
`induction' n with k ih`,
que significa que haremos inducción sobre `n` la variable que se usará
en la inducción es `k` y la hipótesis de inducción se llama `ih`. No es
necesario que `k` sea una variable diferente a `n`.
-/
variable (p : ℕ → Prop)
open Nat
example (n : ℕ ) : p n := by
  induction' n with n ih
  · sorry
  · sorry
