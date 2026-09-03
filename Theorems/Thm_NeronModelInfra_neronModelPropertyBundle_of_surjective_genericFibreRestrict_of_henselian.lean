import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_NeronModelInfra_neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
theorem NeronModelInfra.neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw R f)
    (hext : Function.Surjective (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R))))) :
    NeronModelPropertyBundle R K f := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_neronModelPropertyBundle_of_surjective_genericFibreRestrict_of_henselian.solution
