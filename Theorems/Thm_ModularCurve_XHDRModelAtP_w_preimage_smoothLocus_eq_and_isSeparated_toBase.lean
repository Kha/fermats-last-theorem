import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_w_preimage_smoothLocus_eq_and_isSeparated_toBase

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.w_preimage_smoothLocus_eq_and_isSeparated_toBase
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) :
    𝔛.w.hom ⁻¹ᵁ 𝔛.smoothLocus = 𝔛.smoothLocus ∧ IsSeparated (toBase p (ΓM M H) hj) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_w_preimage_smoothLocus_eq_and_isSeparated_toBase.solution
