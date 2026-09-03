import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_map_hom_eq_of_pullback_section_trivial
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (N : A.Modules)
    (hNe : Nonempty ((Scheme.Modules.pullback e).obj N ≅ SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf))
    (μ : (Scheme.Modules.pullback e).obj N ≅ (Scheme.Modules.pullback e).obj N) :
    ∃ θ : N ≅ N, (Scheme.Modules.pullback e).map θ.hom = μ.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_map_hom_eq_of_pullback_section_trivial.solution
