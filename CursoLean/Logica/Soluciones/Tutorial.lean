import Mathlib.Tactic

/-
# Lógica de proposiciones en Lean

Lean tiene un tipo especial para hablar de proposiciones, `Prop`. De esta
manera:
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

Nota: pasa el cursor sobre el símbolo y VS Code te dara información acerca del
significado y cómo incluirlo en el editor.


## Tácticas

Para hacer los ejercicios de esta sección se usaran las siguientes tácticas
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
