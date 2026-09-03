import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_eq_of_fibre_of_ord_residue_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (P : Place L F) (hP : P ∈ C.dom) (hord : (C.placeMap P).ord (C.residue ⟨f, hf⟩) = 1)
    (hreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f ∈ w.toValuationSubring)
    (hPz : 0 < P.ord f) :
    P.ord f = 1 ∧ ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → w ≠ P → w.ord f = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_ord_eq_of_fibre_of_ord_residue_eq_one.solution
