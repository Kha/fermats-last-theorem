import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod

open scoped MatrixGroups
theorem Ihara.commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod
    (hP1 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 → commutator (SL(2, ZMod (p ^ n))) = ⊤)
    (hP2 : ∀ p n : ℕ, p.Prime → 5 ≤ p → n ≠ 0 →
      Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (p ^ n))))
    (m : ℕ) (hm : ∀ p : ℕ, p.Prime → p ∣ m → 5 ≤ p) :
    commutator (SL(2, ZMod m)) = ⊤ ∧ Ihara.HasTrivialSchurMultiplier (SL(2, ZMod m)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_commutator_eq_top_and_hasTrivialSchurMultiplier_SL2_ZMod.solution
