import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import P2M.Util
import P2M.Sol.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Set.Finite {ξ : Y | f.base ξ = IsLocalRing.closedPoint R ∧
        ∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ} ∧
    (∀ y : Y, f.base y = IsLocalRing.closedPoint R →
      ∃! ξ : Y, (f.base ξ = IsLocalRing.closedPoint R ∧
        (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ)) ∧ ξ ⤳ y) ∧
    (∀ ξ : Y, f.base ξ = IsLocalRing.closedPoint R →
      (∀ y' : Y, y' ⤳ ξ → f.base y' = IsLocalRing.closedPoint R → y' = ξ) →
      ∃ V : Y.Opens, ξ ∈ V ∧ (∀ y' : Y, f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V) ∧
        (∀ y' : Y, y' ∈ V → f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y') ∧
        (∀ y' : Y, f.base y' = IsLocalRing.closedPoint R → ξ ⤳ y' → y' ∈ V)) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens.solution
