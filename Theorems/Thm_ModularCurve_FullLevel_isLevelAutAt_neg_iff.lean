import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_isLevelAutAt_neg_iff

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isLevelAutAt_neg_iff
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K) :
    ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H (-γ) K τ ↔
      ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K τ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_isLevelAutAt_neg_iff.solution
