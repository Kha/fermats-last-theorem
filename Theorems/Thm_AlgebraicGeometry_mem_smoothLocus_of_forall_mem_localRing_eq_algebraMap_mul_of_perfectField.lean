import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve

theorem AlgebraicGeometry.mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField
    {A₀ : Type} [CommRing A₀] [IsLocalRing A₀] [PerfectField (IsLocalRing.ResidueField A₀)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    {X₀ : Scheme.{0}} (f : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [Flat f] [LocallyOfFinitePresentation f]
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField f a)
    (η : X₀) (hη : f.base η = IsLocalRing.closedPoint A₀)
    (H : ∀ g ∈ SemistableModel.localRing X₀ φ₀ η, g⁻¹ ∉ SemistableModel.localRing X₀ φ₀ η →
      ∃ h ∈ SemistableModel.localRing X₀ φ₀ η, g = algebraMap A₀ F₀ ϖ₀ * h) :
    η ∈ f.smoothLocus := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_mem_smoothLocus_of_forall_mem_localRing_eq_algebraMap_mul_of_perfectField.solution
