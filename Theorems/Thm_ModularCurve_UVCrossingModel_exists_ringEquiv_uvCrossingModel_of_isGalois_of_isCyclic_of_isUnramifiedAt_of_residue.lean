import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~exists_ringEquiv_integralClosure_uvCrossingModel_pow_of_pow_eq_unit_mul_U"

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra (UVCrossingModel W (π ^ (1 * n))) B] [Module.Finite (UVCrossingModel W (π ^ (1 * n))) B] [FaithfulSMul (UVCrossingModel W (π ^ (1 * n))) B]
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀] [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F] [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [Algebra B F] [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = n)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (1 * n))) B)).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) 𝔭)
    (hres : ∀ b : B, ∃ w : W, b - algebraMap (UVCrossingModel W (π ^ (1 * n))) B (const (π ^ (1 * n)) w) ∈ IsLocalRing.maximalIdeal B) :
    ∃ e : B ≃+* UVCrossingModel W π,
      ∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (1 * n))) B (const (π ^ (1 * n)) w)) = const π w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue.solution
