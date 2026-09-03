import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime

open scoped MatrixGroups
theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime
    {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q) :
    Ihara.HasTrivialSchurMultiplier (SL(2, ZMod q)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime.solution
