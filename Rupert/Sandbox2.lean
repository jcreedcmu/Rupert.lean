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

def ChurchL3  : Type 1 := (A : Fin 3 → Type)
  → (n : Fin 3) → ((∀ m ≥ n, (∀ p ≥ m, A p → A p) → A m) → A n)

lemma above_2 (P : Fin 3 → Type) : (∀ m ≥ 2, P m) = P 2 := by
  sorry
lemma above_1 (P : Fin 3 → Type) : (∀ m ≥ 1, P m) = (P 1 × P 2) := by
  sorry
def above_0 (P : Fin 3 → Type) : (∀ m ≥ 0, P m) = (P 0 × P 1 × P 2) := by
  sorry

def cvtL : ChurchL → ChurchL3 := by
  intro t A n
  match n with
  | ⟨0, _⟩ =>
     change (∀ m ≥ 0, (∀ p ≥ m, A p → A p) → A m) → A 0
     rw [above_0, above_0, above_1, above_2]
     intro ⟨x0, ⟨x1, x2⟩⟩
     let a2 := t (A 2) x2
     let z1 : (A 1 → A 1) → A 1 := fun f1 => x1 ⟨f1, fun _ => a2⟩
     let a1 := t (A 1) z1
     let z0 : (A 0 → A 0) → A 0 := fun f0 => x0 ⟨f0, fun _ => a1, fun _ => a2⟩
     let a0 := t (A 0) z0
     exact a0
  | ⟨1, _⟩ =>
    change (∀ m ≥ 1, (∀ p ≥ m, A p → A p) → A m) → A 1
    rw [above_1, above_1, above_2]
    intro ⟨x, y⟩
    have t0 := t (A 1)
    have t1 := t (A 2)
    have a1 := t1 y
    apply t0
    intro f0
    apply x
    exact ⟨f0, fun _ => a1⟩
  | ⟨2, _⟩ =>
    change (∀ m ≥ 2, (∀ p ≥ m, A p → A p) → A m) → A 2
    rw [above_2, above_2]
    exact t (A 2)
