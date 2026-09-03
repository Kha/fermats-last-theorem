import Mathlib
import P2M.Util
import P2M.Sol.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute

theorem Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∀ n : ℕ, Nonempty (ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ≃+ Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ))) (u v : ℤ) (i j : A →+ A) (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) : ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute.solution
