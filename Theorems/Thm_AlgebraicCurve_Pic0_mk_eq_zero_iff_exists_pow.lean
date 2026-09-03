import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.mk_eq_zero_iff_exists_pow {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → u ∈ (algebraMap K F).range)
    {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0) {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) :
    Pic0.mk D = 0 ↔ ∃ h : F, h ≠ 0 ∧ f = h ^ n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff_exists_pow.solution
