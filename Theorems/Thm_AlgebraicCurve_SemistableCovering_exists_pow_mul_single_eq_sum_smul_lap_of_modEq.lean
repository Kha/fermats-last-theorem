import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableCovering_exists_pow_mul_single_eq_sum_smul_lap_of_modEq

set_option autoImplicit false

theorem
    AlgebraicCurve.SemistableCovering.exists_pow_mul_single_eq_sum_smul_lap_of_modEq
    (n m : ℕ) (src tgt : Fin m → Fin n) (w : Fin m → ℕ) (hw : ∀ e, w e ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (hk : 0 < k) (n₀ : Fin m → ℤ) :
    ∃ (K : ℕ) (hK : k ≤ K) (nn : Fin m → ℤ), (∀ e, ((ℓ ^ k : ℕ) : ℤ) ∣ nn e - n₀ e) ∧
    let V := Fin n ⊕ (Σ e : Fin m, Fin (ℓ ^ K * w e - 1))
    let ends : (Σ e : Fin m, Fin (ℓ ^ K * w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = ℓ ^ K * w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (ℓ ^ K * w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∃ φ : V → ℤ, ∀ v : Σ e : Fin m, Fin (ℓ ^ K * w e - 1),
      (ℓ ^ K : ℤ) * (∑ e, nn e • (Pi.single (Sum.inr ⟨e, ⟨ℓ ^ (K - k) - 1, by
          have h1 : 1 ≤ ℓ ^ (K - k) := Nat.one_le_pow _ _ (Fact.out : ℓ.Prime).pos
          have h2 : ℓ ^ (K - k) < ℓ ^ K := Nat.pow_lt_pow_right (Fact.out : ℓ.Prime).one_lt (by omega)
          have h3 : ℓ ^ K ≤ ℓ ^ K * w e := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (hw e))
          omega⟩⟩) 1 : V → ℤ)) (Sum.inr v)
        = (∑ u, φ u • lap u) (Sum.inr v) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableCovering_exists_pow_mul_single_eq_sum_smul_lap_of_modEq.solution
