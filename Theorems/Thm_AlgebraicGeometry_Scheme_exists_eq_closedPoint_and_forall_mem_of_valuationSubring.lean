import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring
    {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of O)) [UniversallyClosed f]
    (V : ValuationSubring X.functionField)
    (hOV : ∀ a : O, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ V)
    (hmV : ∀ a ∈ IsLocalRing.maximalIdeal O, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ V.nonunits) :
    ∃ c : X, f.base c = IsLocalRing.closedPoint O ∧
      (∀ s : X.presheaf.stalk c, algebraMap (X.presheaf.stalk c) X.functionField s ∈ V) ∧
      (∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c),
        algebraMap (X.presheaf.stalk c) X.functionField s ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring.solution
