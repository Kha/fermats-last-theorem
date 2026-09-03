import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) :
    ∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))),
      IsIndexOneExtension R (Z.presheaf.stalk ζ) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes.solution
