import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq

open scoped MatrixGroups
theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_sq (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hperf : commutator SL(2, ZMod (q ^ 2)) = ⊤)
    (IH : Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))) :
    Ihara.HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq.solution
