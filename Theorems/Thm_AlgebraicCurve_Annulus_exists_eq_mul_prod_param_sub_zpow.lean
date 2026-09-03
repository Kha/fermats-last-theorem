import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_exists_eq_mul_prod_param_sub_zpow

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.exists_eq_mul_prod_param_sub_zpow
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (f : F) (hf : f ≠ 0) :
    ∃ (s : Finset (Place L F)) (n : Place L F → ℤ) (g : F),
      (↑s ⊆ An.dom) ∧ g ≠ 0 ∧ (∀ P ∈ An.dom, P.ord g = 0) ∧
        f = g * ∏ P ∈ s, (An.param - algebraMap L F (P.evalAt An.param)) ^ n P := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_exists_eq_mul_prod_param_sub_zpow.solution
