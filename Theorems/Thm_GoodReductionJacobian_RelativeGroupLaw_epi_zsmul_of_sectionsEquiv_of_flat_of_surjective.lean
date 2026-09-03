import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra
  GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.epi_zsmul_of_sectionsEquiv_of_flat_of_surjective
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
    (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f)
    (he : ∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (n : ℕ)
    (hn : ∀ (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
        (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n)
    [Flat (G.schemeNsmul n)] [Surjective (G.schemeNsmul n)] [LocallyOfFinitePresentation (G.schemeNsmul n)] :
    Epi ((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_epi_zsmul_of_sectionsEquiv_of_flat_of_surjective.solution
