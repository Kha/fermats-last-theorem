import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    y ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice.solution
