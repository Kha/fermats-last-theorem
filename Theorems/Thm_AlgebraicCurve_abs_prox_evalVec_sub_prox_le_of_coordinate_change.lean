import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_abs_prox_evalVec_sub_prox_le_of_coordinate_change

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.abs_prox_evalVec_sub_prox_le_of_coordinate_change
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ j, t j ≠ 0)
    (M M' : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ))
    (hM : ∀ j, t j = ∑ i, M j i • s i) (hM' : ∀ i, s i = ∑ j, M' i j • t j)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (C : ℝ) (hC : 1 ≤ C) (hMC : ∀ j i, μ (M j i) ≤ C) (hM'C : ∀ i j, μ (M' i j) ≤ C)
    (P Q : Place (AlgebraicClosure ℚ) F) (hP : P.IsRational) (hQ : Q.IsRational)
    (cP cQ : Fin r)
    (hcP : ∀ j, 0 ≤ P.ord (t j * (t cP)⁻¹)) (hcQ : ∀ j, 0 ≤ Q.ord (t j * (t cQ)⁻¹))
    (hne : ∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) :
    |prox (μ : AlgebraicClosure ℚ → ℝ) (evalVec s P) (evalVec s Q)
        - prox (μ : AlgebraicClosure ℚ → ℝ) (fun j => P.evalAt (t j * (t cP)⁻¹))
            (fun j => Q.evalAt (t j * (t cQ)⁻¹))|
      ≤ 4 * Real.log C := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_abs_prox_evalVec_sub_prox_le_of_coordinate_change.solution
