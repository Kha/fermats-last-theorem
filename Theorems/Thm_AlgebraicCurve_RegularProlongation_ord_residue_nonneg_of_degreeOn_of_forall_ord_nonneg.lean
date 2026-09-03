import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField A) Fbar) (D : Set (Place L F))
    (hdeg : R.DegreeOn Q D)
    (f : R.integers) (hres : R.residue f ≠ 0)

    (hfin : {P : Place L F | P.ord (f : F) ≠ 0}.Finite)

    (hD : ∀ P ∈ D, 0 ≤ P.ord (f : F)) :
    0 ≤ Q.ord (R.residue f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_ord_residue_nonneg_of_degreeOn_of_forall_ord_nonneg.solution
