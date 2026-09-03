import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.exists_gamma0_heckeT_iDeg_interchange_diamondRaw
    {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (H : Subgroup (ZMod N)ˣ) (H' : Subgroup (ZMod (N * q))ˣ)
    (h₁ : LevelLE N (N * q) H H' 1) (hq : LevelLE N (N * q) H H' q) :
    ∃ σ : Gamma0 N, ((((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = q) ∧
      ∀ φ : H1 N H A,
        heckeT (N * q) H' q A (iDeg' N (N * q) H H' 1 A h₁ φ)
          = iDeg' N (N * q) H H' 1 A h₁ (heckeT N H q A φ)
              - iDeg' N (N * q) H H' q A hq (diamondRaw N H A σ φ) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw.solution
