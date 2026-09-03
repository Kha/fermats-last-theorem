import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed
    {A₀ : Type u} [CommRing A₀]
    {X₀ : Scheme.{u}} (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsLocallyNoetherian X₀] [UniversallyClosed toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    {F₀ : Type v} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)
    (t : F₀) [Algebra.IsAlgebraic ↥(Algebra.adjoin A₀ ({t} : Set F₀)) F₀]
    (O : ValuationSubring F₀)
    (hAO : ∀ a : A₀, algebraMap A₀ F₀ a ∈ O)
    (hAO' : ∀ a : A₀, algebraMap A₀ F₀ a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ O) :
    ∃ x : X₀, SemistableModel.localRing X₀ φ₀ x = O.toSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_localRing_eq_valuationSubring_of_isIntegrallyClosed_of_universallyClosed.solution
