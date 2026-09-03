import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_point_specializes_base_closedPoint

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace Ws23C2cE

theorem main (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (z : A) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f, z ⤳ x.1.base (IsLocalRing.closedPoint K) := by
  haveI := hA.proper
  haveI : CompactSpace A := by
    constructor
    have h := QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ
    simpa using h
  obtain ⟨z₁, hz₁, hcl⟩ :=
    (isClosed_closure (s := ({z} : Set A))).exists_closed_singleton ⟨z, subset_closure rfl⟩
  refine ⟨⟨pointOfClosedPoint f z₁ hcl, pointOfClosedPoint_comp f z₁ hcl⟩, ?_⟩
  rw [specializes_iff_mem_closure]
  change (pointOfClosedPoint f z₁ hcl) (IsLocalRing.closedPoint K) ∈ closure {z}
  rw [pointOfClosedPoint_apply]
  exact hz₁

end Ws23C2cE

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (z : A) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f, z ⤳ x.1.base (IsLocalRing.closedPoint K) :=
  Ws23C2cE.main K f hA z
