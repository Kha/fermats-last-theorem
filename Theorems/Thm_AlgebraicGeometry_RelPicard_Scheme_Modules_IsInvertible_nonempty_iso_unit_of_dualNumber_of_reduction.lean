import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.RelPicard

theorem Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction
    (Cr : Type u) [CommRing Cr] (M : (Spec (.of (DualNumber Cr))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Cr Cr Cr).toRingHom))).obj M ≅
        SheafOfModules.unit.{u} (Spec (.of Cr)).ringCatSheaf)) :
    Nonempty (M ≅ SheafOfModules.unit.{u} (Spec (.of (DualNumber Cr))).ringCatSheaf) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction.solution

end AlgebraicGeometry.RelPicard
