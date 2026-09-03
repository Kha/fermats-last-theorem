import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring
    {L : Type u} [Field L] (O : ValuationSubring L)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (s : Spec (CommRingCat.of ↥O) ⟶ Y) (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype) ≫ s) :
    ∃! xt : SchemeHomOver s f, Spec.map (CommRingCat.ofHom O.subtype) ≫ xt.1 = x := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring.solution
