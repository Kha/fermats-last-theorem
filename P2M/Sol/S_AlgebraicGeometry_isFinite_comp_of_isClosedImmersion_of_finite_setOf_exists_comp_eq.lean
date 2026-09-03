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
import Definitions.Def_AlgebraicGeometry_RiemannForm
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isFinite_comp_of_isClosedImmersion_of_finite_setOf_exists_comp_eq

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A K : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [LocallyOfFiniteType f]
    (ι : K ⟶ A) [IsClosedImmersion ι]
    (hfin : {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f | ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1}.Finite) :
    IsFinite (ι ≫ f) := by
  classical
  haveI : LocallyOfFiniteType (ι ≫ f) := inferInstance
  haveI : QuasiCompact (ι ≫ f) := inferInstance
  haveI : JacobsonSpace ↥K := LocallyOfFiniteType.jacobsonSpace (ι ≫ f)

  have hcl : (closedPoints ↥K).Finite := by
    haveI : Finite ↥{x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f | ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1} :=
      hfin.to_subtype
    let F : {p : Spec (CommRingCat.of k) ⟶ K // p ≫ (ι ≫ f) = 𝟙 _} →
        ↥{x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f | ∃ y : Spec (CommRingCat.of k) ⟶ K, y ≫ ι = x.1} :=
      fun p => ⟨⟨p.1 ≫ ι, by rw [Category.assoc]; exact p.2⟩, p.1, rfl⟩
    have hF : Function.Injective F := by
      intro p q hpq
      apply Subtype.ext
      have h1 : p.1 ≫ ι = q.1 ≫ ι := congrArg (fun z => z.1.1) hpq
      exact (cancel_mono ι).mp h1
    haveI : Finite {p : Spec (CommRingCat.of k) ⟶ K // p ≫ (ι ≫ f) = 𝟙 _} := Finite.of_injective F hF
    haveI : Finite ↥(closedPoints ↥K) := Finite.of_equiv _ (pointEquivClosedPoint (ι ≫ f))
    exact Set.toFinite _
  haveI : DiscreteTopology ↥K := JacobsonSpace.discreteTopology hcl
  haveI : Finite ↥K := by
    have huniv : closedPoints ↥K = Set.univ := closedPoints_eq_univ
    exact Set.finite_univ_iff.mp (huniv ▸ hcl)
  haveI : LocallyQuasiFinite (ι ≫ f) :=
    locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun _ => Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite (ι ≫ f)
