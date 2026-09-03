import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (g : F) (hg0 : g ≠ 0) (hg : g ∈ C.integers) (hres : C.residue ⟨g, hg⟩ ≠ 0)
    (hpole : ∀ P ∈ C.dom, 0 ≤ P.ord g)
    (v : Place (ResidueField A) Fbar) (hv : v ∉ C.nodes) :
    0 ≤ v.ord (C.residue ⟨g, hg⟩) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg.solution
