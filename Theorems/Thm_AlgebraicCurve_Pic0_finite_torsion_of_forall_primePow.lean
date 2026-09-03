import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k))) (n : ℕ) (hn : 0 < n) :
    Finite (Pic0.torsion K F n) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.solution
