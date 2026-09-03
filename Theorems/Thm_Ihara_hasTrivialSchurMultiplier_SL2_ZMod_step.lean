import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_step (q m : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hm : 3 ≤ m) (hperf : commutator SL(2, ZMod (q ^ m)) = ⊤)
    (IH : Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ (m - 1)))) :
    Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ m)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step.solution
