import Mathlib
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv
    (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L))
    (σL : L ≃+* L) (τc : ↥K ≃+* ↥K)
    (hτc : ∀ x : ↥K, ((τc x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L))
    (σ : ↥K ≃ₐ[L] ↥K) (hσ : ModularCurve.FullLevel.IsLevelAutAt L n ζ m N₀ H γ K σ) :
    ∃ σ' : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L n (σL ζ) m N₀ H γ K σ' ∧
      ∀ x : ↥K, σ' x = τc (σ (τc.symm x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_apply_conj_of_coeffMap_ringEquiv.solution
