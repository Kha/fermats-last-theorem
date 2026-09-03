import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import P2M.Util
import P2M.Sol.S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1

set_option autoImplicit false

theorem CohCarrier.frickeH1_heckeTlower_eq_heckeT_frickeH1
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (q : ℕ) [NeZero q]
    (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N H A) :
    CohCarrier.frickeH1 N H A (CohCarrier.heckeTlower N H q A φ) =
      CohCarrier.heckeT N H q A (CohCarrier.frickeH1 N H A φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1.solution
