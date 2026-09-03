import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {L : Type} [Field L] [CharZero L] (ι₀ : A₀ →+* L) (hι₀ : Function.Injective ι₀)
    (K₀ : Subfield L) (hK₀A : ∀ a : A₀, ι₀ a ∈ K₀)
    (hK₀ : ∀ x : L, x ∈ K₀ → ∃ a b : A₀, b ≠ 0 ∧ x * ι₀ b = ι₀ a)

    (hLK₀ : ∀ x : L, IsAlgebraic ↥K₀ x)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]

    (hLalg : ∀ x : F, IsAlgebraic L x → x ∈ Set.range (algebraMap L F))
    (F₀ : Subfield F)
    (hconst : ∀ c : L, algebraMap L F c ∈ F₀ ↔ c ∈ K₀)
    (hspan : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (g : Fin n → ↥F₀) (d : Fin n → L) (g' : Fin n → ↥F₀),
      (∑ i, d i • (g' i : F)) ≠ 0 ∧ f * (∑ i, d i • (g' i : F)) = ∑ i, c i • (g i : F))

    (j₀ : A₀ →+* ↥F₀) (hj₀ : ∀ a : A₀, ((j₀ a : ↥F₀) : F) = algebraMap L F (ι₀ a))
    :
    letI : Algebra A₀ ↥F₀ := j₀.toAlgebra
    letI : Algebra A₀ ↥K₀ := (ι₀.codRestrict K₀ hK₀A).toAlgebra
    letI : Algebra ↥K₀ ↥F₀ :=
      (((algebraMap L F).comp K₀.subtype).codRestrict F₀ (fun c => (hconst (c : L)).mpr c.2)).toAlgebra
    IsFractionRing A₀ ↥K₀ ∧ IsScalarTower A₀ ↥K₀ ↥F₀ ∧
    (∃ t : ↥F₀, Transcendental A₀ t) ∧
    (∀ t : ↥F₀, Transcendental A₀ t →
      FiniteDimensional ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀ ∧
      Algebra.IsSeparable ↥(IntermediateField.adjoin ↥K₀ ({t} : Set ↥F₀)) ↥F₀) ∧
    IsIntegrallyClosedIn A₀ ↥F₀ := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver.solution
