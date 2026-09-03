import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral
import P2M.Util
import P2M.Sol.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash {n : ℕ}
    {f : UpperHalfPlane → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (σ : SL(2, ℤ)) (h : ℤ) (τ : UpperHalfPlane) :
    MvPolynomial.coeff (Finsupp.single 1 n)
      ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹
          (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ)
            - HeckeEis.binaryFormRepSL ℂ n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)) : ↥(HeckeEis.BinaryForm ℂ n)) :
        MvPolynomial (Fin 2) ℂ)
      = ∫ t in (0 : ℝ)..(h : ℝ), (f ∣[((n : ℤ) + 2)] σ) ((t : ℝ) +ᵥ (σ⁻¹ • τ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash.solution
