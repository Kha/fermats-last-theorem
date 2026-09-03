import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow

open scoped MatrixGroups
theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    {n : ℕ} (hn : n ≠ 0) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow.solution
