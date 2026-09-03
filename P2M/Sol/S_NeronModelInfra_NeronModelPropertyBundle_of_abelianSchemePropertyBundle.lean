import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact
import Theorems.Thm_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact
import P2M.Util
namespace P2MW.S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    NeronModelInfra.NeronModelPropertyBundle R K f := by
  haveI : IsProper f := hA.proper
  have hsep : IsSeparated f := inferInstance
  refine ⟨hA.smooth, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  haveI := ht
  haveI := hqc
  haveI : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    hA.genericFibreRestrict_surjective_of_quasiCompact R K t⟩
