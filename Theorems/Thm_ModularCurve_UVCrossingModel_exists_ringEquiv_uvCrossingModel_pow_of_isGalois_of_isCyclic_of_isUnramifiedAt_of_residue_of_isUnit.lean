import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hmW : IsUnit (m : W))
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra (UVCrossingModel W (π ^ (m * n))) B] [Module.Finite (UVCrossingModel W (π ^ (m * n))) B]
    [FaithfulSMul (UVCrossingModel W (π ^ (m * n))) B]
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀] [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    [Algebra B F] [IsScalarTower (UVCrossingModel W (π ^ (m * n))) B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = n)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime],
      (𝔭.comap (algebraMap (UVCrossingModel W (π ^ (m * n))) B)).height = 1 →
        Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (m * n))) 𝔭)
    (hres : ∀ b : B, ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w) ∈ IsLocalRing.maximalIdeal B) :
    ∃ e : B ≃+* UVCrossingModel W (π ^ m),
      ∀ w : W, e (algebraMap (UVCrossingModel W (π ^ (m * n))) B (const (π ^ (m * n)) w)) = const (π ^ m) w := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_uvCrossingModel_pow_of_isGalois_of_isCyclic_of_isUnramifiedAt_of_residue_of_isUnit.solution
