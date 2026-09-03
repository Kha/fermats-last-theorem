import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_AlgebraicGeometry_FppfH0Identification
import Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace R0ADN

theorem natCard_fppfCohomology_zero_eq_natCard_fppfH_zero
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 0) = Nat.card (FppfCohomologyLES.FppfH X 0) := by
  have i1 : fppfCohomology specInt L 0 ≃+ L.obj.obj (op (fppfTerminal specInt)) :=
    fppfCohomologyZeroAddEquiv specInt L
  have i2 : L.obj.obj (op (fppfTerminal specInt)) ≃+ X.obj.obj (op specInt) :=
    (e.app (op (fppfTerminal specInt))).addCommGroupIsoToAddEquiv
  have i3 : FppfCohomologyLES.FppfH X 0 ≃+ X.obj.obj (op specInt) :=
    EtaleCohomologyLES.fppfHZeroSectionsAddEquiv specZIsTerminal X
  exact Nat.card_congr (i1.trans (i2.trans i3.symm)).toEquiv

end R0ADN

theorem solution
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 0) = Nat.card (FppfCohomologyLES.FppfH X 0) ∧
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) :=
  ⟨R0ADN.natCard_fppfCohomology_zero_eq_natCard_fppfH_zero X L e,
   AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction X L e⟩
