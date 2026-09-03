import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete"

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (u : (UVCrossingModel W (π ^ (m * n)))ˣ)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    (θ : F) (hθ : θ ^ n = algebraMap (UVCrossingModel W (π ^ (m * n))) F (↑u * U (π ^ (m * n))))
    (hF : IntermediateField.adjoin K₀ {θ} = ⊤) :
    Module.Finite (UVCrossingModel W (π ^ (m * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ∧
    ∃ e : ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F) ≃+* UVCrossingModel W (π ^ m),
      (∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (const (π ^ (m * n)) w)) =
        const (π ^ m) w) ∧
      (∃ v : (UVCrossingModel W (π ^ m))ˣ,
        ((e.symm (↑v * U (π ^ m)) : ↥(integralClosure _ F)) : F) = θ) ∧
      (∃ v₁ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (U (π ^ (m * n)))) = ↑v₁ * U (π ^ m) ^ n) ∧
      (∃ v₂ : (UVCrossingModel W (π ^ m))ˣ,
        e (algebraMap (UVCrossingModel W (π ^ (m * n))) _ (V (π ^ (m * n)))) = ↑v₂ * V (π ^ m) ^ n) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U.solution
