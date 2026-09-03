import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
attribute [-simp] CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ D₀ : ℕ, D₀ ≠ 0 ∧ ∀ n : ℕ, IsIntegral ℤ ((D₀ : ℂ) * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))).coeff n) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.solution
