import Mathlib.Tactic


section prop
/-
# Lógica de proposiciones en Lean

Lean tiene un tipo especial para hablar de proposiciones, `Prop`.
De esta manera:
* `a : Prop` significa que `a` es una proposición,
* `h : a` significa que `h` es una demostración de que `a` es verdadera.


## Notación

En esta sección usaremos los siguientes símbolos

| símbolo |    nombre     | en Lean |
| :-----: | :-----------: | :------ |
|    ∨    |  disyunción   | `\or`   |
|    ∧    |  conjunción   | `\and`  |
|    →    |  implicación  | `\r`    |
|    ↔    | bicondicional | `\iff`  |
|    ¬    |    negación   | `\n`    |
|    ∃    |  existencial  | `\ex`   |
|    ∀    |   universal   | `\fo`   |

Nota: pasa el cursor sobre el símbolo y VS Code te dara información
acerca del significado y cómo incluirlo en el editor.


## Tácticas

Para hacer los ejercicios de esta sección se usaran las siguientes
tácticas
* `intro`
* `exact`
* `apply`
* `rcases`
* `constructor`
* `left`
* `right`
* `by_contra` (lógica clásica)
* `by_cases` (lógica clásica)
-/


variable (a b c : Prop) --Sean a, b y c proposiciones

--Toda proposición se sigue de sí misma
example : a → a := by sorry

/-
Nota:
En Lean la implicación asocia hacia la derecha. Por lo tanto
`a → b → c` significa `a → (b → c)`

Puese pasar el cursor sobre los conectivos, ya sea en el editor o en el
infoview y se resaltará el alcance del conectivo. Lo mismo con
cuantificadores, operaciones, etc.
-/


--## Ejemplos

--### Implicación
--Si `a` es cierta, entonces cualquier cosa la implica
example : a → b → a := by sorry


--Modus Ponens
example : a → (a → b) → b := by
  intro ha h
  apply h
  exact ha


--### Conjunción
example : a ∧ b → a := by sorry

example : a ∧ b → a := by sorry

example : a → b → a ∧ b := by sorry


--### Disyunción
example : a → a ∨ b := by sorry

example : a ∨ b → b ∨ a := by sorry

/-
Nota:
Es posible romper la disyunción al mismo tiempo que se introduce la
hipótesis, para esto se usa `rintro`
-/
example : a ∨ b → b ∨ a := by sorry


--### Negación
/-
En Lean `¬a` se define como `a → False`. Esto es, `¬a` significa que
`a` implica algo absurdo
-/
example : False → ¬True := by sorry

example : True → ¬False := by sorry

example : a → ¬a → False := by sorry

example : a → ¬a → False := by sorry

example : (a → b) → (a → ¬b) → ¬a := by sorry


--### Lógica clásica
example : (¬b → ¬a) → (a → b) := by sorry

example : (¬a → b) → (¬a → ¬b) → a := by sorry

end prop



section fol
/-
# Lógica de primer orden
Una fórmula con una vriable, como x²=0, es una expresión que al darle
un valor específico a la variable se vuelve una proposición, como
1²=0. En este sentido, la fórmula x²=0 es una función que a cada valor
de x le asigna una proposición.

En Lean tenemos que decir que tipo de varuable le pasaremos a una
fórmula. En el ejemplo de arriba, es diferente pasarle el 1 como
número natural a pasarle el 1 como real.


## Notación

En esta sección usaremos los siguientes símbolos

| símbolo |    nombre     | en Lean |
| :-----: | :-----------: | :------ |
|    ∃    |  existencial  | `\ex`   |
|    ∀    |   universal   | `\fo`   |


## Tácticas

Además de las tácticas para proposiciones, ahora usaremos
* `use`
-/

variable (α : Type) (p q r : α → Prop)


--## Ejemplos

--### Caso particular
example (a : α) : (∀ x, p x) → p a := by sorry

--### Testigo
example (a : α) : p a → ∃ x, p x := by sorry

--### Otras
example : (∀ x, p x ∧ q x) → ∀ x, p x := by sorry

example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := by sorry


end fol
