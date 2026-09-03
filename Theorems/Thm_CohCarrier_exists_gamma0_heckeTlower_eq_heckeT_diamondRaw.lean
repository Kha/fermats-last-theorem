import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw
attribute [-simp] CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.exists_gamma0_heckeTlower_eq_heckeT_diamondRaw
    {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ∃ τ : Gamma0 N, ((((τ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = q) ∧
      ∀ φ : H1 N H A, heckeTlower N H q A φ = heckeT N H q A (diamondRaw N H A τ φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw.solution
