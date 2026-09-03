import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.valuation_evalAt_param_sub_algebraMap
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F) (P : Place L F) (hP : P ∈ An.dom) (a : L) :
    (A.valuation (P.evalAt An.param) ≠ A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) =
          max (A.valuation (P.evalAt An.param)) (A.valuation a)) ∧
      (A.valuation (P.evalAt An.param) = A.valuation a →
        A.valuation (P.evalAt (An.param - algebraMap L F a)) ≤ A.valuation a ∧
          (a ≠ 0 → ∀ h : a⁻¹ * P.evalAt An.param ∈ A,
            (A.valuation (P.evalAt (An.param - algebraMap L F a)) = A.valuation a ↔
              IsLocalRing.residue A ⟨a⁻¹ * P.evalAt An.param, h⟩ ≠ 1))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_valuation_evalAt_param_sub_algebraMap.solution
