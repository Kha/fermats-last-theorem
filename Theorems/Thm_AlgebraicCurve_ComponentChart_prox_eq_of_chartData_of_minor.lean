import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {r : ℕ} (s : Fin r → F) (hint : ∀ i, s i ∈ C.integers)
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational)
    (hcQ : ∀ P ∈ C.dom, C.residue ⟨s (cQ (C.placeMap P)), hint _⟩ ≠ 0)
    (hratio : ∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
    (hreg : ∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ C.dom, ∀ hmem : s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
      (C.placeMap P).ord (C.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
      ∀ (hmP : ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
        (hmQ : ∀ j, s j * (s (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
      ∃ i j, (C.placeMap P).evalAt (C.residue ⟨_, hmP i⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j⟩)
        ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i⟩)) :
    ∀ μ : AbsoluteValue L ℝ, IsNonarchimedean μ → (∀ a : L, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ C.dom, ∀ Q ∈ C.dom, P ≠ Q →
        (C.placeMap P ≠ C.placeMap Q →
          prox (μ : L → ℝ) (fun i ↦ P.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            (fun i ↦ Q.evalAt (s i * (s (cQ (C.placeMap Q)))⁻¹)) = 0) ∧
        (C.placeMap P = C.placeMap Q →
          prox (μ : L → ℝ) (fun i ↦ P.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            (fun i ↦ Q.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            = -Real.log (μ (Q.evalAt (s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹)
                - P.evalAt (s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor.solution
