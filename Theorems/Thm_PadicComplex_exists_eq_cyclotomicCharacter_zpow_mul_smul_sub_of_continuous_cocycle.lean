import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import P2M.Util
import P2M.Sol.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle

set_option autoImplicit false

theorem PadicComplex.exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (k : ℤ) (hk : k ≠ 0) (c : K.fixingSubgroup → ℂ_[p]) (hc : Continuous c)
    (hcocycle : ∀ σ τ : K.fixingSubgroup,
      c (σ * τ) = c σ + (algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p
            (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k *
          ((σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • c τ)) :
    ∃ b : ℂ_[p], ∀ σ : K.fixingSubgroup,
      c σ = (algebraMap ℚ_[p] ℂ_[p]
        (((cyclotomicCharacter (PadicAlgCl p) p
            (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p).toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k *
          ((σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) • b) - b := by p2m_exact_reverting @_root_.P2MW.S_PadicComplex_exists_eq_cyclotomicCharacter_zpow_mul_smul_sub_of_continuous_cocycle.solution
