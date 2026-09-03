import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.closure_image_preimage_closure_eq_closure_singleton
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)} (a : PartialAction k f p)
    (Z : Set ↥P) (ζ : ↥(pullback f p)) (hζ : ζ ∈ a.dom)
    (hζcl : closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure Z) :
    closure (a.hom.base '' ((a.dom.ι ≫ pullback.snd f p).base ⁻¹' closure Z)) =
      closure ({a.hom.base ⟨ζ, hζ⟩} : Set ↥P) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_PartialAction_closure_image_preimage_closure_eq_closure_singleton.solution
