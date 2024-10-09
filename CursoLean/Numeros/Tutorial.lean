import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

/-
# Estructuras numéricas
El objetivo de esta sección es hacer inducción, pero las
demostraciones con números puedes verse diferente a las que hemos
estado haciendo. Empezaremos viendo algunas cosas de anillos y
luego haremos inducción.

Un anillo es un conjunto `R` con funciones `+,* : R × R → R` que
satisfacen ciertas propiedades. En Lean obtenemos lo anterior
diciendo que `R` es un tipo (en algún universo), `R : Type*` y la
estructura se obtiene  con `[Ring R]`.


## Notación
La notación que usaremos en esta sección es

| símbolo | nombre         | en Lean |
| :------ | :------------- | :------ |
| *       | multiplicación | *       |
| ∑       | suma           | `\sum`  |

## Tácticas
Las tácticas nuevas que usaremos en esta sección son
* `nth_rw n [...]`
* `norm_num`
* `ring`
* `induction'`

## Definiciones adicionales

Recordemos los axiomas de anillo conmutativo con 1
(Hay algunos de más, pero así vemos más nombres de propiedades)
-/
#check add_assoc
#check add_comm
#check add_zero
#check zero_add
#check neg_add_self
#check add_neg_self
#check mul_assoc
#check mul_one
#check one_mul
#check mul_add
#check add_mul


--Sea `R` un anillo
variable (R : Type*) [Ring R]

--Sean `a,b,c ∈ R`
variable (a b c : R)


lemma l1 : a * 0 + a * 0 = a * 0 := by
  rw [<-mul_add, zero_add]

lemma l2 : -(a * 0) + (a * 0 + a * 0) = -(a * 0) + a * 0 := by
  apply congrArg
  apply l1

example : a * 0 = 0 := by
  nth_rw 2 [<-neg_add_self (a * 0)]
  nth_rw 1 [<-zero_add (a * 0)]
  nth_rw 1 [<-neg_add_self (a * 0)]
  rw [add_assoc]
  apply l2

example : a * 0 = 0 := by
  calc a * 0
    _ = 0 + a * 0                  := by rw [zero_add]
    _ = (-(a * 0) + a * 0) + a * 0 := by rw [neg_add_self]
    _ = -(a * 0) + (a * 0 + a * 0) := by rw [add_assoc]
    _ = -(a * 0) + a * (0 + 0)     := by rw [mul_add]
    _ = -(a * 0 ) + a * 0          := by rw [add_zero]
    _ = 0                          := by rw [neg_add_self]

example (h : ∀ c, c ≠ 0 → ∀ (a b : R), c * a = c * b → a = b) :
    ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b h'
  by_cases ac : a = 0
  · left; assumption
  · right
    rw [<-ne_eq] at ac
    rw [<-mul_zero a] at h'
    apply h a
    assumption'

example (h : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) :
    ∀ c, c ≠ 0 → ∀ (a b : R), c * a = c * b → a = b := by
  intro c cnc a b h'
  have desp : c * a - c * b = 0 := by
    apply sub_eq_iff_eq_add.mpr
    rw [zero_add]
    assumption
  rw [<-mul_sub] at desp
  have : c = 0 ∨ a - b = 0 := by
    apply h
    assumption
  rcases this with cc | amb
  · contradiction
  · rw [<-zero_add b]
    apply sub_eq_iff_eq_add.mp
    assumption



/-
# Inducción
-/

open BigOperators Finset Nat

#check sum_range_zero
#check sum_range_succ
#check Nat.div_eq_of_eq_mul_right

example : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  sorry


example : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

example : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry


/-
# Inducción fuerte
-/

#check two_le_iff

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  sorry
