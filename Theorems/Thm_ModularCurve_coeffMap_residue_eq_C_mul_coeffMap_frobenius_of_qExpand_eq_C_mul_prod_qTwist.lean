import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsLocalRing A] [CharP (IsLocalRing.ResidueField A) p]
    (ζ : Aˣ) (hζ : ζ ^ p = 1) (u : A) (y yU : LaurentSeries A)

    (hlaw : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      qExpand A p yU = HahnSeries.C u * ∏ j ∈ Finset.range p, qTwist (ζ ^ j) y) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    coeffMap (IsLocalRing.residue A) yU =
      HahnSeries.C (IsLocalRing.residue A u) * coeffMap (frobenius (IsLocalRing.ResidueField A) p) (coeffMap (IsLocalRing.residue A) y) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_residue_eq_C_mul_coeffMap_frobenius_of_qExpand_eq_C_mul_prod_qTwist.solution
