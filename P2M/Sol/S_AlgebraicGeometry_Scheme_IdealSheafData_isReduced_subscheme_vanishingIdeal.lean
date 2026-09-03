import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom iSup_affineOpens_eq_top IsAffine Scheme Scheme.IdealSheafData.vanishingIdeal IsReduced.of_openCover Scheme.IdealSheafData.vanishingIdeal_ideal IsReduced Scheme.Hom.preimage_iSup isReduced_of_isAffine_isReduced Scheme.IdealSheafData"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom Γ topIso IdealSheafData.vanishingIdeal IdealSheafData.vanishingIdeal_ideal affineOpens openCoverOfIsOpenCover Hom.preimage_iSup Opens IdealSheafData"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "subscheme vanishingIdeal subschemeObjIso vanishingIdeal_ideal ideal subschemeι"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem isReduced_subscheme_of_forall_isRadical' {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  have hcov : TopologicalSpace.IsOpenCover fun U : X.affineOpens => I.subschemeι ⁻¹ᵁ (U : X.Opens) := by
    rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]; rfl
  have hX : ∀ U : X.affineOpens, IsReduced ((I.subscheme.openCoverOfIsOpenCover _ hcov).X U) := fun U => by
    change IsReduced ↑(I.subschemeι ⁻¹ᵁ (U : X.Opens))
    have : IsAffine ↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) := U.2.preimage I.subschemeι
    have hred : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    have : _root_.IsReduced Γ(↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)), ⊤) :=
      isReduced_of_injective ((I.subschemeι ⁻¹ᵁ (U : X.Opens)).topIso.hom ≫ (I.subschemeObjIso U).hom).hom
        (ConcreteCategory.bijective_of_isIso _).1
    exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ (I.subscheme.openCoverOfIsOpenCover _ hcov)

end AlgebraicGeometry.Scheme.IdealSheafData

theorem solution
    {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_of_forall_isRadical' _ fun U => by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_ideal]; exact PrimeSpectrum.isRadical_vanishingIdeal _
