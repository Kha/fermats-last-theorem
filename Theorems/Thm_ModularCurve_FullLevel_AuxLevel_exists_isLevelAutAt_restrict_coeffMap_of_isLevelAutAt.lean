import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (L : Type) [Field L] [CharZero L] (ι₀ : L₀ →+* L)
    (hι : ∃ ι : L →+* ℂ, ι (ι₀ ξ₀) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :

    (∀ x : ↥K₀, ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K) ∧

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) (ι₀ ξ₀) (q * ℓ) ((q * ℓ) ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ →
        ∃ τ₀ : ↥K₀ ≃ₐ[L₀] ↥K₀,
          ModularCurve.FullLevel.IsLevelAutAt L₀ (q * ℓ) ξ₀ (q * ℓ) ((q * ℓ) ^ 2 * M')
            (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K₀ τ₀ ∧
          ∀ (x : ↥K₀) (hx : ModularCurve.coeffMap ι₀ ((x : ↥K₀) : LaurentSeries L₀) ∈ K),
            ((τ ⟨_, hx⟩ : ↥K) : LaurentSeries L) = ModularCurve.coeffMap ι₀ ((τ₀ x : ↥K₀) : LaurentSeries L₀)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt.solution
