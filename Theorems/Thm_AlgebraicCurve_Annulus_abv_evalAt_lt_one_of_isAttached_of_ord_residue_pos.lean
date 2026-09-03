import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.Annulus.abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar)
    (hatt : An.IsAttached C x)
    (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hx : 0 < x.ord (C.residue ⟨f, hf⟩)) (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, μ (Q.evalAt f) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Annulus_abv_evalAt_lt_one_of_isAttached_of_ord_residue_pos.solution
