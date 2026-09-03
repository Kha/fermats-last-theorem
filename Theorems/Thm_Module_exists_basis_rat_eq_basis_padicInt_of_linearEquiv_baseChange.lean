import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange

open scoped TensorProduct
theorem Module.exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange
    (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module ℚ A] [Module.Finite ℚ A]
    (Hp : Type*) [AddCommGroup Hp] [Module ℤ_[p] Hp]
    [Module.Finite ℤ_[p] Hp] [Module.Flat ℤ_[p] Hp]
    (φ : (ℚ_[p] ⊗[ℚ] A) ≃ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] Hp)) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ A) (bHp : Basis (Fin n) ℤ_[p] Hp),
      ∀ i, φ (1 ⊗ₜ[ℚ] (b i)) = 1 ⊗ₜ[ℤ_[p]] (bHp i) := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_basis_rat_eq_basis_padicInt_of_linearEquiv_baseChange.solution
