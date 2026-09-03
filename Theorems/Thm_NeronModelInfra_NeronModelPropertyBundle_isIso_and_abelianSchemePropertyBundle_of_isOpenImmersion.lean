import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.NeronModelPropertyBundle.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion.solution
