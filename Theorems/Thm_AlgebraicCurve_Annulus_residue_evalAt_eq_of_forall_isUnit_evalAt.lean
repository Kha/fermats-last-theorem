import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_residue_evalAt_eq_of_forall_isUnit_evalAt

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.residue_evalAt_eq_of_forall_isUnit_evalAt
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (u : F) (hreg : ∀ P ∈ An.dom, u ∈ P.toValuationSubring)
    (hunit : ∀ P ∈ An.dom, ∃ h : P.evalAt u ∈ A, IsUnit (⟨P.evalAt u, h⟩ : A))
    (P Q : Place L F) (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (hPc : A.valuation (P.evalAt An.param) = A.valuation c) (hQc : A.valuation (Q.evalAt An.param) = A.valuation c)
    (hPu : P.evalAt u ∈ A) (hQu : Q.evalAt u ∈ A) :
    IsLocalRing.residue A ⟨P.evalAt u, hPu⟩ = IsLocalRing.residue A ⟨Q.evalAt u, hQu⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_residue_evalAt_eq_of_forall_isUnit_evalAt.solution
