import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import P2M.Util
import P2M.Sol.S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul

set_option autoImplicit false

theorem PadicComplex.eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul
    (p : ℕ) [Fact p.Prime] (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv :
                ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_eq_zero_of_forall_smul_eq_cyclotomicCharacter_zpow_mul.solution
