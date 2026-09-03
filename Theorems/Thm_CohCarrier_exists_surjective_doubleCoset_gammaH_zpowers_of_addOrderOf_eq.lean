import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq

open scoped MatrixGroups

theorem CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ c : {v : Fin 2 → ZMod M // addOrderOf v = M} →
        DoubleCoset.Quotient (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
          (Subgroup.zpowers g : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      Function.Surjective c ∧
      ∀ v v', c v = c v' ↔ ∃ (k : ℤ) (h : (ZMod M)ˣ), h ∈ H ∧
        v'.1 = (h : ZMod M) •
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g ^ k)).1.mulVec v.1) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq.solution
