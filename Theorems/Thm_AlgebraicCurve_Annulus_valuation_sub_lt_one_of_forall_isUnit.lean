import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Annulus.valuation_sub_lt_one_of_forall_isUnit
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (An : Annulus A F) (f : F) (hf0 : f ≠ 0) (hf : ∀ P ∈ An.dom, P.ord f = 0)
    (m : ℤ) (c : L) (hc : c ≠ 0)
    (hu : ∀ P ∈ An.dom, ∃ h : P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A))
    (P Q : Place L F) (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) :
    A.valuation (P.evalAt f * c⁻¹ * (P.evalAt An.param) ^ (-m) -
      Q.evalAt f * c⁻¹ * (Q.evalAt An.param) ^ (-m)) < 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_valuation_sub_lt_one_of_forall_isUnit.solution
