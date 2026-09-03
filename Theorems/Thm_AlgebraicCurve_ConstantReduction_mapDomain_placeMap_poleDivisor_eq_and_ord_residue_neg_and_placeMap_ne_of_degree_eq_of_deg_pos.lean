import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (u : F) (hu : u ∈ R.integers)
    (Du : Divisor L F) (hDu : ∀ P : Place L F, Du P = max 0 (-(P.ord u)))
    (Dū : Divisor (ResidueField ↥A) Fbar)
    (hDū : ∀ Q : Place (ResidueField ↥A) Fbar, Dū Q = max 0 (-(Q.ord (R.residue ⟨u, hu⟩))))
    (hdeg : Divisor.degree Dū = Divisor.degree Du) (hnc : Dū ≠ 0)
    (hfin : ∀ P : Place L F, P.ord u < 0 → 0 < P.deg) :
    Finsupp.mapDomain R.placeMap Du = Dū ∧
    (∀ P' : Place L F, P'.ord u < 0 → (R.placeMap P').ord (R.residue ⟨u, hu⟩) < 0) ∧
    (∀ P : Place L F, P.IsRational → u ∈ P.toValuationSubring → P.evalAt u ∈ A →
      ∀ P' : Place L F, P'.ord u < 0 → R.placeMap P' ≠ R.placeMap P) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos.solution
