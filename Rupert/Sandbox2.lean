import Mathlib
set_option linter.unusedVariables false

def Church : Type 1 := (A : Type)
  → (A → A → A)
  → ((A → A) → A)
  → A

def ChurchK  : Type 1 := (A : ℕ → Type)
  → (n : ℕ)
  → (∀ m ≥ n, A m → A m → A m)
  → (∀ m ≥ n, (∀ p ≥ m, A p → A p) → A m)
  → A n

def cvt : Church →  ChurchK := by
  intro t A n klam kapp
  sorry

def ChurchL : Type 1 := (A : Type)
  → ((A → A) → A) → A

def ChurchL2  : Type 1 := (A : Fin 2 → Type)
  → (n : Fin 2) → ((∀ m ≥ n, (∀ p ≥ m, A p → A p) → A m) → A n)

lemma above_1 (P : Fin 2 → Type) : (∀ m ≥ 1, P m) = P 1 := by
  sorry
def above_0 (P : Fin 2 → Type) : (∀ m ≥ 0, P m) = (P 0 × P 1) := by
  sorry

def cvtL : ChurchL → ChurchL2 := by
  intro t A n
  match n with
  | ⟨0, _⟩ =>
     change (∀ m ≥ 0, (∀ p ≥ m, A p → A p) → A m) → A 0
     rw [above_0, above_0, above_1]
     intro ⟨x, y⟩
     have t0 := t (A 0)
     have t1 := t (A 1)
     have a1 := t1 y
     apply t0
     intro f0
     apply x
     exact ⟨f0, fun _ => a1⟩
  | ⟨1, _⟩ =>
    change (∀ m ≥ 1, (∀ p ≥ m, A p → A p) → A m) → A 1
    rw [above_1, above_1]
    exact t (A 1)
