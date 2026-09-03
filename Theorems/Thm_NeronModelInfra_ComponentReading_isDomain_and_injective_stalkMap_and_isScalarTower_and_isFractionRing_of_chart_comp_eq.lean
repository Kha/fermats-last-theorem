import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData
import P2M.Util
import P2M.Sol.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite open AlgebraicGeometry hiding isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict open NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)}
    (T T' : ComponentReading R K gK d ω)
    (W : T.Y.Opens) (hyW : T.y ∈ W) (u : SchemeHomOver (W.ι ≫ T.f) T'.f)
    (hu : (genericFibreRestrict R K T'.f (W.ι ≫ T.f) u).1 ≫ T'.e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    letI := T.algebra
    letI φ : T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩) ⟶ T.Y.presheaf.stalk T.y :=
      u.1.stalkMap ⟨T.y, hyW⟩ ≫ (W.stalkIso ⟨T.y, hyW⟩).hom
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) := φ.hom.toAlgebra
    letI : Algebra (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) :=
      ((algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y))).comp φ.hom).toAlgebra
    letI : Algebra R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) := stalkAlgebra T'.f (u.1.base ⟨T.y, hyW⟩)
    IsDomain (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) ∧
      Function.Injective φ.hom ∧
      IsScalarTower R (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (T.Y.presheaf.stalk T.y) ∧
      IsFractionRing (T'.Y.presheaf.stalk (u.1.base ⟨T.y, hyW⟩)) (FractionRing (T.Y.presheaf.stalk T.y)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_ComponentReading_isDomain_and_injective_stalkMap_and_isScalarTower_and_isFractionRing_of_chart_comp_eq.solution
