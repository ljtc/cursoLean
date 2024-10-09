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
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [sum_range_succ, mul_add 2, ← ih]
  rw [<-add_mul, mul_comm]


example : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  symm
  induction' n with n ih
  · simp only [sum_range_succ,sum_range_zero,pow_two,mul_zero,add_zero,zero_mul]
  · calc 6 * ∑ i ∈ range (n + 1 + 1), i ^ 2
      _ = 6 * (∑ i ∈ range (n + 1), i ^ 2 + (n + 1) ^ 2) := by
        rw [sum_range_succ]
      _ = 6 * ∑ i ∈ range (n + 1), i ^ 2 + 6 * (n + 1) ^ 2 := by
        rw [mul_add]
      _ = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by
        rw [ih]
      _ = (n + 1) * (n * (2 * n + 1) + (n + 1) * 6) := by
        rw [mul_comm n, mul_assoc]
        rw [pow_two, mul_comm 6, mul_assoc]
        rw [mul_add (n + 1)]
      _ = (n + 1) * (2 * n ^ 2 + n + 6 * n + 6) := by
        rw [mul_add n, add_mul n 1 6, mul_comm n, mul_assoc]
        rw [<-pow_two, mul_one, mul_comm n 6, one_mul, add_assoc _ _ 6]
      _ = (n + 1) * (2 * n ^ 2 + 7 * n + 6) := by
        nth_rw 3 [<-one_mul n]
        rw [add_assoc _ _ (6 * n), add_mul 1 6 n]
      _ = (n + 1) * ((n + 2) * (2 * n + 3)) := by
        rw [mul_add (n + 2), add_mul n 2 _, add_mul n 2 3]
        rw [mul_comm n (2 * n), mul_assoc 2 n n, <-pow_two n]
        rw [<-mul_assoc 2 2 n, mul_comm n 3, <-add_assoc _ (3 * n)]
        rw [add_assoc _ _ (3 * n)]
        norm_num; rw [<-add_mul]
      _ = (n +1) * ((n + 2) * (2 * (n + 1) + 1)) := by
        norm_num
        rw [mul_add, mul_one]
      _ = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by
        rw [mul_assoc]

example : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  symm
  induction' n with n ih
  · simp only [sum_range_succ,sum_range_zero,pow_two,mul_zero,add_zero,zero_mul]
  · calc 6 * ∑ i ∈ range (n + 1 + 1), i ^ 2
      _ = 6 * (∑ i ∈ range (n + 1), i ^ 2 + (n + 1) ^ 2) := by
        rw [sum_range_succ]
      _ = 6 * ∑ i ∈ range (n + 1), i ^ 2 + 6 * (n + 1) ^ 2 := by ring
      _ = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by rw [ih]
      _ = (n + 1) * (n * (2 * n + 1) + (n + 1) * 6) := by ring
      _ = (n + 1) * (2 * n ^ 2 + n + 6 * n + 6) := by ring
      _ = (n + 1) * (2 * n ^ 2 + 7 * n + 6) := by ring
      _ = (n + 1) * ((n + 2) * (2 * n + 3)) := by ring
      _ = (n +1) * ((n + 2) * (2 * (n + 1) + 1)) := by ring
      _ = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by ring


/-
# Inducción fuerte
-/

#check two_le_iff

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := by
    apply (two_le_iff m).mpr
    exact ⟨this, mne1⟩
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
