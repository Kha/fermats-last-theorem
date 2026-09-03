import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Definitions.Def_SchurMultiplierTrivial
import P2M.Util
import P2M.Sol.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow

open scoped MatrixGroups

theorem Ihara.hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (n : ℕ) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_odd_prime_pow.solution
