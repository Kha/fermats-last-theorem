import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
    {C : Type u} [CommRing C] [IsNoetherianRing C] (hfin : ∀ (m : Ideal C) [m.IsMaximal], Finite (C ⧸ m))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g]
    (x : X) (t : ↥(Spec (CommRingCat.of C))) (ht : IsClosed ({t} : Set ↥(Spec (CommRingCat.of C))))
    (hxt : g.base x ⤳ t) (hne : g.base x ≠ t)
    (hcov : ∀ p : Ideal C, p.IsPrime → (g.base x).asIdeal ≤ p → p ≤ t.asIdeal → p = (g.base x).asIdeal ∨ p = t.asIdeal) :
    ∃ S : ValuativeCommSq g, IsDiscreteValuationRing S.R ∧ Finite (IsLocalRing.ResidueField S.R) ∧
      S.i₂.base (IsLocalRing.closedPoint S.R) = t ∧ Set.range S.i₁.base ⊆ closure {x} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes.solution
