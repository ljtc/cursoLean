import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Use

namespace Gru

class Grupo₁ (G : Type*) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ x y z : G, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x : G, mul one x = x
  inv_mul_cancel : ∀ x : G, mul (inv x) x = one


instance hasMulGrupo₁ {G: Type*} [Grupo₁ G] : Mul G :=
  ⟨Grupo₁.mul⟩

instance hasOneGrupo₁ {G : Type*} [Grupo₁ G] : One G :=
  ⟨Grupo₁.one⟩

instance hasInvGrupo₁ {G : Type*} [Grupo₁ G] : Inv G :=
  ⟨Grupo₁.inv⟩

section grupo1

variable (G : Type*) [Grupo₁ G]
variable (x y : G)

#check x * y
#check x⁻¹
#check (1 : G)

end grupo1


class Grupo (G : Type*) extends One G, Mul G, Inv G where
  mul_assoc : ∀ x y z : G, (x * y) * z = x * (y * z)
  one_mul : ∀ x : G, 1 * x = x
  inv_mul_cancel : ∀ x : G, x⁻¹ * x = 1


variable (G : Type*) [Grupo G]
variable (x y z : G)


/-
Un idempotente es un elemento x tal que x * x = x
El único idempotente en un grupo es el neutro
-/
lemma lema1 (h : x * x = x) : x = 1 := by
  calc
    x = 1 * x := by rw [Grupo.one_mul]
    _ = (x⁻¹ * x) * x := by rw [Grupo.inv_mul_cancel]
    _ = x⁻¹ * (x * x) := by rw [Grupo.mul_assoc]
    _ = x⁻¹ * x := by rw [h]
    _ = 1 := by rw [Grupo.inv_mul_cancel]

example (h : x * x = x) : x = 1 := by
  rw [<-Grupo.one_mul x, <-Grupo.inv_mul_cancel x]
  rw [Grupo.mul_assoc, h]

lemma lema2 : (x * x⁻¹) * (x * x⁻¹) = x * x⁻¹ := by
  rw [Grupo.mul_assoc, <-Grupo.mul_assoc x⁻¹, Grupo.inv_mul_cancel]
  rw [Grupo.one_mul]

/-
El inverso izquierdo también es derecho
-/
theorem mul_inv_cancel : x * x⁻¹ = 1 := by
  apply lema1
  apply lema2

/-
El neutro también es por la derecha
-/
theorem mul_one : x * 1 = x := by
  rw [<-Grupo.inv_mul_cancel x, <-Grupo.mul_assoc,mul_inv_cancel]
  rw [Grupo.one_mul]

/-
Si x tiene inv derecho e izquierdo, entonces los inv son iguales
-/
example (h1 : y * x = 1) (h2 : x * z = 1) : y = z := by
  calc
    y = y * 1       := by rw [mul_one]
    _ = y * (x * z) := by rw [h2]
    _ = (y * x) * z := by rw [Grupo.mul_assoc]
    _ = 1 * z       := by rw [h1]
    _ = z           := by rw [Grupo.one_mul]

/-
Multiplicar por x es inyectiva
-/
theorem mul_iny (h : x * y = x * z) : y = z := by
  rw [<-Grupo.one_mul y, <-Grupo.inv_mul_cancel x]
  rw [Grupo.mul_assoc, h, <-Grupo.mul_assoc]
  rw [Grupo.inv_mul_cancel, Grupo.one_mul]

/-
El inverso del inverso es el original
-/
theorem inv_inv : (x⁻¹)⁻¹ = x := by
  apply mul_iny _ x⁻¹
  rw [Grupo.inv_mul_cancel, mul_inv_cancel]

theorem mul_inv : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by
  apply mul_iny _ (x * y)
  rw [mul_inv_cancel, Grupo.mul_assoc, <-Grupo.mul_assoc y]
  rw [mul_inv_cancel, Grupo.one_mul, mul_inv_cancel]

/-
Multiplicar por x es suprayectiva
-/
theorem mul_sup : ∀ (a : G), ∃ (b : G), x * b = a := by
  intro a
  use x⁻¹ * a
  rw [<-Grupo.mul_assoc, mul_inv_cancel, Grupo.one_mul]
end Gru
