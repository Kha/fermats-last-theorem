import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (1 * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (1 * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (1 * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (1 * n))) K₀ F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F))
    (hdeg : Module.finrank K₀ F = n)
    [IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)]
    (hunr : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (1 * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F))).height = 1 →
      Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (1 * n))) Q)
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (1 * n))) _ (const (π ^ (1 * n)) w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W (π ^ (1 * n))) F)) :
    ∃ (u : (UVCrossingModel W (π ^ (1 * n)))ˣ) (θ : F),
      θ ^ n = algebraMap (UVCrossingModel W (π ^ (1 * n))) F (↑u * U (π ^ (1 * n))) ∧
      IntermediateField.adjoin K₀ {θ} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_thicknessOne.solution
