import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.existsUnique_extension_hom_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (LA : RelativeGroupLaw R f)
    {t : T ⟶ Spec (CommRingCat.of R)} [Smooth t] (LT : RelativeGroupLaw R t)
    (φK : SchemeHomOver (RelativeGroupLaw.genericFibreStr K t) (RelativeGroupLaw.genericFibreStr K f))
    (hφK : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver s (RelativeGroupLaw.genericFibreStr K t)),
        NeronModelInfra.schemeHomOverComp ((LT.genericFibre K).mul s x y) φK =
          (LA.genericFibre K).mul s (NeronModelInfra.schemeHomOverComp x φK)
            (NeronModelInfra.schemeHomOverComp y φK)) :
    ∃! φ : SchemeHomOver t f,
      genericFibreRestrict R K f t φ = φK ∧
      ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s t),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) φ =
          LA.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_existsUnique_extension_hom_of_genericFibre.solution
