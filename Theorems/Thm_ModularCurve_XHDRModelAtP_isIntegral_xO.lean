import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_isIntegral_xO

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~isIntegral_of_mem_nonZeroDivisors_of_isIntegral_basicOpen~map_appTop_mem_nonZeroDivisors_of_flat ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isIntegral_xO
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (ρO : R p →+* O) :
    IsIntegral (XO (ΓM M H) hj ρO) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_isIntegral_xO.solution
