import Mathlib
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import P2M.Util
import P2M.Sol.S_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

theorem CategoryTheory.Functor.exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map
    {S U : Scheme.{u}} (j : U ⟶ S) [IsOpenImmersion j]
    (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
    {Y : Scheme.{u}} (p : Y ⟶ U) (e : ((Over.map j).op ⋙ G).RepresentableBy (Over.mk p)) :
    ∃ φ : uliftYoneda.{u + 1}.obj Y ⟶ G.overTotal,
      (∀ {T : Scheme.{u}} (y : T ⟶ Y),
        uliftYonedaEquiv (uliftYoneda.{u + 1}.map y ≫ φ) =
          ⟨(y ≫ p) ≫ j, e.homEquiv (Over.homMk y rfl : Over.mk (y ≫ p) ⟶ Over.mk p)⟩) ∧
      MorphismProperty.relative uliftYoneda.{u + 1} @IsOpenImmersion φ ∧
      ∀ {T : Scheme.{u}} (x : uliftYoneda.{u + 1}.obj T ⟶ G.overTotal),
        Set.range ((uliftYonedaEquiv x).1).base ⊆ Set.range j.base →
        ∃ ψ : T ⟶ Y, uliftYoneda.{u + 1}.map ψ ≫ φ = x := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_Functor_exists_overTotal_chart_relative_isOpenImmersion_of_representableBy_over_map.solution
