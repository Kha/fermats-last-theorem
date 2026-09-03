import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_CuspForm_mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (z : CuspForm (CohCarrier.GammaH M H) 2)
    (hz : z ∈ CuspForm.twoCuspIntegralSet M H 2 p ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)))
    (a : ℕ) (ha : ((p : ℂ) ^ a) • z ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    z ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_twoCuspLattice_bot_of_mem_twoCuspIntegralSet_ratLocalizedAt_of_pow_smul_mem.solution
