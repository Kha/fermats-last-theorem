import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_ComponentChart_fibreParam_laws_of_ord_residue_sub_eq_one

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (P : Place L F) (hP : P ∈ C.dom) (hPrat : P.IsRational)
    (hxrat : (C.placeMap P).IsRational) (T : F) (hT : T ∈ C.integers)
    (hreg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → T ∈ w.toValuationSubring)
    (hunif : (C.placeMap P).ord (C.residue ⟨T, hT⟩
        - algebraMap (IsLocalRing.ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨T, hT⟩))) = 1) :
    ∃ h : T - algebraMap L F (P.evalAt T) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap P).ord (C.residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (T - algebraMap L F (P.evalAt T)) ∧
      ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ P → Q.ord (T - algebraMap L F (P.evalAt T)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ComponentChart_fibreParam_laws_of_ord_residue_sub_eq_one.solution
