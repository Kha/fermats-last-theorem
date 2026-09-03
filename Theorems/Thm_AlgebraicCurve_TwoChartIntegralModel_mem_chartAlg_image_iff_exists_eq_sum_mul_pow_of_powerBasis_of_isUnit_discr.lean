import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr

set_option autoImplicit false

open Polynomial AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (F' : Type u) [Field F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (B : PowerBasis F F') (hgen : IsIntegral R B.gen)
    (hdisc : ∃ d : Rˣ, algebraMap R F (d : R) = Algebra.discr F (fun i : Fin B.dim => B.gen ^ (i : ℕ)))
    (S : Set F) :
    (∀ x : F', x ∈ chartAlg R F' (algebraMap F F' '' S) ↔
        ∃ b : Fin B.dim → ↥(chartAlg R F S), x = ∑ i, algebraMap F F' (b i : F) * B.gen ^ (i : ℕ)) ∧
    (∀ b b' : Fin B.dim → ↥(chartAlg R F S),
        (∑ i, algebraMap F F' (b i : F) * B.gen ^ (i : ℕ)) = ∑ i, algebraMap F F' (b' i : F) * B.gen ^ (i : ℕ) → b = b') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr.solution
