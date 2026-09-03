import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero

set_option autoImplicit false

open MeasureTheory

theorem MvPolynomial.measure_setOf_eval_eq_zero_of_ne_zero
    (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F] [T2Space F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F] (hF : ¬ DiscreteTopology F)
    (ι : Type) [Fintype ι] (p : MvPolynomial ι F) (hp : p ≠ 0)
    (μ : Measure (ι → F)) [μ.IsAddHaarMeasure] :
    μ {x : ι → F | MvPolynomial.eval x p = 0} = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_measure_setOf_eval_eq_zero_of_ne_zero.solution
