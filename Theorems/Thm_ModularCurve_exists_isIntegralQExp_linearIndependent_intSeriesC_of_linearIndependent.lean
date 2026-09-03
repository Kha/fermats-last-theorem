import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent
    (κ : Type) [Field κ] (M : ℕ) (k : ℤ) {d : ℕ}
    (g : Fin d → ModularForm (Gamma1 M) k) (pg : Fin d → PowerSeries ℤ)
    (hg : ∀ i, IsIntegralQExp (g i) (pg i)) (hli : LinearIndependent ℂ g) :
    ∃ (g' : Fin d → ModularForm (Gamma1 M) k) (pg' : Fin d → PowerSeries ℤ),
      (∀ i, IsIntegralQExp (g' i) (pg' i)) ∧ LinearIndependent κ (fun i => intSeriesC κ (pg' i)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isIntegralQExp_linearIndependent_intSeriesC_of_linearIndependent.solution
