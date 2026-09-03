import Definitions.Def_AlgebraicCurve_Pic0BaseChange
import Definitions.Def_DrinfeldCurve_MapConstants
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq

set_option autoImplicit false

open AlgebraicCurve DrinfeldCurve
attribute [local instance 10] constantsAlgebraCoordRing functionFieldConstantsAlgebra in
attribute [local instance] isIntegral_functionFieldMapConstants in

theorem DrinfeldCurve.exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq
    (q : ℕ) [Fact q.Prime] (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) K] [IsScalarTower (GaloisField q 2) k K]
    [IsDomain (CoordRing q k)] [IsDomain (CoordRing q K)] [HasPrincipalDivisors K (drinfeldFunctionField q K)]
    [ConstantFieldDegreeFormula k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)]
    (hβ : Function.Injective (Pic0.baseChange k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)))
    (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
    (hJ : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (Pic0 k (drinfeldFunctionField q k)) ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r)
    (hJ' : ∀ n : ℕ,
      Nat.card (Submodule.torsionBy ℤ (Pic0 K (drinfeldFunctionField q K)) ((ℓ ^ n : ℕ) : ℤ)) = (ℓ ^ n) ^ r) :
    ∃ e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) ≃ₗ[ℚ_[ℓ]]
        ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K)),
      (∀ v,
        e v = ModularCurve.vpMap ℓ (Pic0.baseChange k K (drinfeldFunctionField q k) (drinfeldFunctionField q K)) v) ∧
        ∀ h : hSubgroup q,
          (e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]]
              ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K))) ∘ₗ
            ModularCurve.rationalGaloisRep ℓ (Pic0 k (drinfeldFunctionField q k))
              (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) (hFunctionFieldAction q k h) =
          ModularCurve.rationalGaloisRep ℓ (Pic0 K (drinfeldFunctionField q K))
              (drinfeldFunctionField q K ≃ₐ[K] drinfeldFunctionField q K) (hFunctionFieldAction q K h) ∘ₗ
            (e : ModularCurve.RationalTateModule ℓ (Pic0 k (drinfeldFunctionField q k)) →ₗ[ℚ_[ℓ]]
              ModularCurve.RationalTateModule ℓ (Pic0 K (drinfeldFunctionField q K))) := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_exists_rationalTateModule_linearEquiv_baseChange_of_injective_of_card_torsionBy_eq.solution
