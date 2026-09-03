import Definitions.Def_AlgebraicCurve_CycleChowForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_bddAbove_chowLogAt_range

theorem AlgebraicCurve.bddAbove_chowLogAt_range {F : Type} [Field F]
    [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → F)
    (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) :
    BddAbove (Set.range
      fun a : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0} =>
        ‖σ (MvPolynomial.eval a.1 (chowForm s Z))‖
          / (⨆ i, ‖σ (a.1 i)‖) ^ (Z.sum fun _ n => n.toNat)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_bddAbove_chowLogAt_range.solution
