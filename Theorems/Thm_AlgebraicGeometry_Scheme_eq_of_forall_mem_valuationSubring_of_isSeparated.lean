import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated
    {O : Type u} [CommRing O] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (V : ValuationSubring X.functionField) (c₁ c₂ : X)
    (h₁ : ∀ s : X.presheaf.stalk c₁, algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V)
    (h₁' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₁),
      algebraMap (X.presheaf.stalk c₁) X.functionField s ∈ V.nonunits)
    (h₂ : ∀ s : X.presheaf.stalk c₂, algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V)
    (h₂' : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c₂),
      algebraMap (X.presheaf.stalk c₂) X.functionField s ∈ V.nonunits) :
    c₁ = c₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated.solution
