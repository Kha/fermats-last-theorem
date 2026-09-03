import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_residue_eq_zero_of_forall_ord_eq_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes)
    (hord : ∀ P ∈ C.dom, C.placeMap P = Q → P.ord f = 0) :
    Q.ord (C.residue ⟨f, hf⟩) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero.solution
