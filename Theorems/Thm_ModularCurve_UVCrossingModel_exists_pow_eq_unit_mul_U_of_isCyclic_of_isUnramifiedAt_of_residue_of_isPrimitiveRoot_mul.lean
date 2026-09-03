import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hμ : ∃ ζ : W, IsPrimitiveRoot ζ n)
    (hmnW : IsUnit ((m * n : ℕ) : W)) (hμ' : ∃ ζ : W, IsPrimitiveRoot ζ (m * n))
    (K₀ : Type*) [Field K₀] [Algebra (UVCrossingModel W (π ^ (m * n))) K₀]
    [IsFractionRing (UVCrossingModel W (π ^ (m * n))) K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra (UVCrossingModel W (π ^ (m * n))) F]
    [IsScalarTower (UVCrossingModel W (π ^ (m * n))) K₀ F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F))
    (hdeg : Module.finrank K₀ F = n)
    [IsLocalRing ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F)]
    (hunr : ∀ (Q : Ideal ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F)) [Q.IsPrime],
      (Q.comap (algebraMap (UVCrossingModel W (π ^ (m * n)))
        ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F))).height = 1 →
      Algebra.IsUnramifiedAt (UVCrossingModel W (π ^ (m * n))) Q)
    (hres : ∀ b : ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F), ∃ w : W,
      b - algebraMap (UVCrossingModel W (π ^ (m * n))) _ (const (π ^ (m * n)) w) ∈
        IsLocalRing.maximalIdeal ↥(integralClosure (UVCrossingModel W (π ^ (m * n))) F)) :
    ∃ (u : (UVCrossingModel W (π ^ (m * n)))ˣ) (θ : F),
      θ ^ n = algebraMap (UVCrossingModel W (π ^ (m * n))) F (↑u * U (π ^ (m * n))) ∧
      IntermediateField.adjoin K₀ {θ} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul.solution
