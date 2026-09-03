import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Definitions.Def_ModularCurve_EisensteinIdeal
import P2M.Util
import P2M.Sol.S_ModularCurve_eisensteinQuotientRational_closure_locallyTorsion_isTorsion_heckeModuleBar
open ModularCurve AlgebraicCurve
theorem ModularCurve.eisensteinQuotientRational_closure_locallyTorsion_isTorsion_heckeModuleBar
    (p : ℕ) [Fact p.Prime] (hcomm : HeckeOperatorsCommuteBar p)
    (hseam : (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range (heckeOperatorBar p)))).FG)
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ x : JZero p, ∃ y : JZero p, m • y = x)
    (htorsfin : ∀ n : ℕ, 0 < n → JZeroTorsionFinite p n) :
    letI := heckeModuleBar p
    ∀ z ∈ AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)),
      (∀ q : ℕ, q.Prime →
          ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧ IsOfFinAddOrder (s • z)) →
        IsOfFinAddOrder z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eisensteinQuotientRational_closure_locallyTorsion_isTorsion_heckeModuleBar.solution
