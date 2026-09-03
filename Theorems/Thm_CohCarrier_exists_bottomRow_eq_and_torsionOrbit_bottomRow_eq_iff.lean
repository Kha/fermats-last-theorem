import Mathlib
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff

open scoped MatrixGroups

theorem CohCarrier.exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (∀ v : ZMod M × ZMod M, addOrderOf v = M →
      ∃ a : SL(2, ℤ), ((a 1 0 : ℤ) : ZMod M) = v.1 ∧ ((a 1 1 : ℤ) : ZMod M) = v.2) ∧
    (∀ a : SL(2, ℤ), addOrderOf ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M) = M) ∧
    (∀ a b : SL(2, ℤ),
      {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((a 1 0 : ℤ) : ZMod M), ((a 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} =
        {w : ZMod M × ZMod M | ∃ u : (ZMod M)ˣ, u ∈ H ⊔ Subgroup.zpowers (-1) ∧
          w = (u : ZMod M).val • ((((b 1 0 : ℤ) : ZMod M), ((b 1 1 : ℤ) : ZMod M)) : ZMod M × ZMod M)} ↔
      b * a⁻¹ ∈ CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)) := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff.solution
