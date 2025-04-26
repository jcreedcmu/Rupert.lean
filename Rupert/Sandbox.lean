import Mathlib
set_option linter.unusedVariables false

inductive Deb : (n : ℕ) → Type where
| dVar : {n : ℕ} → Fin n → Deb n
| dApp : {n : ℕ} → Deb n → Deb n → Deb n
| dLam : {n : ℕ} → Deb (n + 1) → Deb n
open Deb

def Church (n : ℕ) : Type 1 := (A : ℕ → Type)
  → (weaken : {n m : ℕ} → n ≤ m → A n → A m)
  → (∀ m ≥ n, A m → A m → A m)
  → (∀ m ≥ n, (∀ p ≥ m, A p → A p) → A m)
  → A n

-- First let's do deBruijn indices

def weaken_above {n m p : ℕ} : n ≤ m → Deb (n + p) → Deb (m + p)
| le, dVar q  =>
   if q < p
   then
     let isLt : q < m + p := lt_add_of_lt_add_right q.isLt le
     dVar (Fin.mk q isLt)
   else
     let ineq : q + (m - n) < m + p := by
        rw [← Nat.add_sub_assoc le ↑q]
        apply (Nat.add_lt_add_iff_right (k := n)).mp
        rw [Nat.sub_add_cancel (le_add_of_le_right le)]
        rw [add_rotate m p n]
        apply Nat.add_lt_add_right
        rw [Nat.add_comm p n]
        exact q.isLt
     dVar (Fin.mk (q + (m - n)) ineq)
| le, dApp e1 e2  => dApp (weaken_above le e1) (weaken_above le e2)
| le, dLam body  =>
    let wbody : Deb (m + p + 1) := weaken_above (n := n) (m := m) (p := p + 1) le body
    dLam wbody

def weaken_deb {n m : ℕ} : n ≤ m → Deb n → Deb m :=
  weaken_above (p := 0)

def cvt (t : Church 0) : Deb 0 :=
  t Deb weaken_deb app lam where
   app : (∀ m ≥ 0, Deb m → Deb m → Deb m) :=
     λ _ _ ↦ dApp
   lam : (∀ m ≥ 0, (∀ p ≥ m, Deb p → Deb p) → Deb m) :=
     λ m _ body ↦
      let mf : Fin (m + 1) := Fin.mk 0 (Nat.zero_lt_succ m)
      dLam (body (m + 1) (Nat.le_add_right m 1) (dVar mf))


#eval (cvt λ A weak app lam ↦ lam 0 (Nat.le_refl 0) (λ p pgm x => x))

#eval (cvt λ A weak app lam ↦ lam 0 (Nat.le_refl 0) (λ p pgm x =>
                           lam p pgm (λ p2 pgm2 y => app p2 (Nat.le_trans pgm pgm2) (weak pgm2 x) y)))
