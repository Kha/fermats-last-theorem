import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_eq_of_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

open _root_.AlgebraicGeometry.OModulePresheaf in

theorem solution
    {R : Type} [CommRing R] {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of R))
    (M M' : V.Modules) (e : M ≅ M') (𝒦 : V.OrderedAffineCover) :
    (OModulePresheaf.ofModules π M).eulerChar 𝒦 = (OModulePresheaf.ofModules π M').eulerChar 𝒦 := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso π e 𝒦
  have h : ∀ i, (ofModules π M).cechFinrank 𝒦 i = (ofModules π M').cechFinrank 𝒦 i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e'⟩ := hS j; exact e'.finrank_eq
  rw [eulerChar_def, eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]
