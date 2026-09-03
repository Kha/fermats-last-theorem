import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra
  GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (hG : G.IsCommutative) :
    ∃ (𝒢 : Sheaf (smallFppfTopology (Spec (CommRingCat.of R))) Ab.{u + 1})
      (e : ∀ U : (Spec (CommRingCat.of R)).Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom f),
      (∀ (U : (Spec (CommRingCat.of R)).Fppf) (s s' : 𝒢.1.obj (op U)),
          e U (s + s') = G.mul U.hom (e U s) (e U s')) ∧
      (∀ {U V : (Spec (CommRingCat.of R)).Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
          e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s)) ∧
      (∀ (n : ℕ) (U : (Spec (CommRingCat.of R)).Fppf) (s : 𝒢.1.obj (op U)),
          (e U (((n : ℤ) • 𝟙 𝒢 : 𝒢 ⟶ 𝒢).1.app (op U) s)).1 = (e U s).1 ≫ G.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_sheaf_smallFppfTopology_sectionsEquiv_of_isCommutative.solution
