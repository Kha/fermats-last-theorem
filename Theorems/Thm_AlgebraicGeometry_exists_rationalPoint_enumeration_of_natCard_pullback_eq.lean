import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq
    (κ : Type u) [Field κ] [IsAlgClosed κ]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
    {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)} [LocallyOfFiniteType c₁] [LocallyOfFiniteType c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s) :
    ∃ (p₁ : Fin s → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : Fin s → SchemeHomOver (𝟙 (Spec (.of κ))) c₂),
      (Function.Injective fun j => (p₁ j).1.base (IsLocalRing.closedPoint κ)) ∧
      (∀ j, (p₁ j).1 ≫ i₁.1 = (p₂ j).1 ≫ i₂.1) ∧
      ∀ (q₁ : C₁) (q₂ : C₂), i₁.1.base q₁ = i₂.1.base q₂ →
        ∃ j, q₁ = (p₁ j).1.base (IsLocalRing.closedPoint κ) ∧ q₂ = (p₂ j).1.base (IsLocalRing.closedPoint κ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq.solution
