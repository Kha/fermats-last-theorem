import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.isClosedImmersion_of_iff_exists_comp_eq_of_injective
    {k : Type u} [Field k] [IsAlgClosed k] {G D K : Scheme.{u}}
    (g : G ⟶ Spec (CommRingCat.of k)) [IsReduced G] [LocallyOfFiniteType g] [Flat g] [IsSeparated g]
    (d : D ⟶ Spec (CommRingCat.of k)) (f : SchemeHomOver g d) (j : K ⟶ D) [IsClosedImmersion j]
    (hpts : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t d),
      (∃ b : T ⟶ K, b ≫ j = a.1) ↔ ∃ y : SchemeHomOver t g, NeronModelInfra.schemeHomOverComp y f = a)
    (hinj : ∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g,
      NeronModelInfra.schemeHomOverComp y f = NeronModelInfra.schemeHomOverComp y' f → y = y') :
    IsClosedImmersion f.1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_isClosedImmersion_of_iff_exists_comp_eq_of_injective.solution
