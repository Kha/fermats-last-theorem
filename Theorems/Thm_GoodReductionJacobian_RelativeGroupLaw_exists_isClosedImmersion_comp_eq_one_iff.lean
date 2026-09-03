import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_comp_eq_one_iff
    {k : Type u} [Field k] {D D₁ D₂ : Scheme.{u}}
    {d : D ⟶ Spec (CommRingCat.of k)} {d₁ : D₁ ⟶ Spec (CommRingCat.of k)} {d₂ : D₂ ⟶ Spec (CommRingCat.of k)}
    (L₁ : RelativeGroupLaw k d₁) (L₂ : RelativeGroupLaw k d₂)
    (ν₁ : SchemeHomOver d d₁) (ν₂ : SchemeHomOver d d₂) :
    ∃ (K : Scheme.{u}) (j : K ⟶ D), IsClosedImmersion j ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t d),
        (NeronModelInfra.schemeHomOverComp a ν₁ = L₁.one t ∧ NeronModelInfra.schemeHomOverComp a ν₂ = L₂.one t) ↔
          ∃ b : T ⟶ K, b ≫ j = a.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_comp_eq_one_iff.solution
