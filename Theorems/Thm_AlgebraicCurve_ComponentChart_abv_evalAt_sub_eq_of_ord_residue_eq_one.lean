import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.abv_evalAt_sub_eq_of_ord_residue_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors L F] (C : ComponentChart A F Fbar)
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (P : Place L F) (hP : P ∈ C.dom) (hrat : ∀ w ∈ C.dom, w.IsRational)
    (ρ T : F)
    (hρ : ρ - algebraMap L F (P.evalAt ρ) ∈ C.integers) (hρ0 : C.residue ⟨_, hρ⟩ ≠ 0)
    (hρ1 : (C.placeMap P).ord (C.residue ⟨_, hρ⟩) = 1)
    (hρreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → ρ ∈ w.toValuationSubring)
    (hT : T - algebraMap L F (P.evalAt T) ∈ C.integers) (hT0 : C.residue ⟨_, hT⟩ ≠ 0)
    (hT1 : (C.placeMap P).ord (C.residue ⟨_, hT⟩) = 1)
    (hTreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T ∈ w.toValuationSubring) :
    ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P →
      μ (Q.evalAt T - P.evalAt T) = μ (Q.evalAt ρ - P.evalAt ρ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_abv_evalAt_sub_eq_of_ord_residue_eq_one.solution
