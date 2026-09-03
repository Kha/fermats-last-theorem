import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (L : Type) [Field L] [CharZero L] (ι₀ : L₀ →+* L)
    (hι : ∃ ι : L →+* ℂ, ι (ι₀ ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :

    (∀ x : ↥K₀, ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ((ι₀ ξ₀) ^ ℓ) q (q ^ 2 * M') H₁ γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ q (ξ₀ ^ ℓ) q (q ^ 2 * M') H₁ γ⁻¹ K₀ τ₀ ∧
          ∀ (x : ↥K₀) (hx : ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K),
            ((τ ⟨_, hx⟩ : ↥K) : LaurentSeries L) = ModularCurve.coeffMap ι₀ ((τ₀ x : ↥K₀) : LaurentSeries L₀)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt_of_isPrimitiveRoot_mul_of_dvd.solution
