import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal NeronModelInfra

theorem WeierstrassCurve.DrinfeldGlobal.existsUnique_section_comp_eq_of_isFractionRing
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (W₀ : WeierstrassCurve R₀)
    (s : Spec (CommRingCat.of K) ⟶ projModelCR W₀)
    (hs : s ≫ projModelStrCR W₀ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K))) :
    ∃! P₀ : Section W₀, Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) ≫ P₀.1 = s := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_existsUnique_section_comp_eq_of_isFractionRing.solution
