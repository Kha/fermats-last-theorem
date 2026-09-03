import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le
    (L : ℕ) [NeZero L] (A : Type*) [AddCommGroup A]
    (H H' : Subgroup (ZMod L)ˣ) (h : CohCarrier.LevelLE L L H' H 1)
    (r : ℕ) (hrL : r ∣ L) (hr : 4 ≤ r)
    (hH' : ∀ u ∈ H', ZMod.castHom hrL (ZMod r) (u : ZMod L) = 1) :
    Function.Surjective (CohCarrier.jDeg L L H' H 1 A h) ∧
    ∀ φ : CohCarrier.H1 L H A, CohCarrier.jDeg L L H' H 1 A h φ = 0 ↔
      φ ∈ AddSubgroup.closure {y : CohCarrier.H1 L H A |
        ∃ σ : ↥(CongruenceSubgroup.Gamma0 L), (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH L H' ∧
          ∃ x : CohCarrier.H1 L H A, y = CohCarrier.diamondRaw L H A σ x - x} := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_surjective_jDeg_one_and_jDeg_eq_zero_iff_of_four_le.solution
