import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ q)
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ξ q (q ^ 2 * M') H₁ γ K 1 →
      ((γ 1 1 : ℤ) : ZMod ℓg) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_intCast_apply_eq_one_of_isLevelAutAt_one_of_eq_levelH_inf_ker.solution
