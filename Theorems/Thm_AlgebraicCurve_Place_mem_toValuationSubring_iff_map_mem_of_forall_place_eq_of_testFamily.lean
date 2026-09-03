import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (x : F) [FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →ₐ[K] E) (s : AlgebraicCurve.Place K F) (w : AlgebraicCurve.Place K E)
    (T : Set F)

    (hT : ∀ t ∈ T, φ t ∈ w.toValuationSubring)

    (hvan : ∀ t ∈ T, ∀ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits →
      φ t - algebraMap K E c ∈ w.toValuationSubring.nonunits)

    (hO : ∃ t ∈ T, ∃ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits ∧ t ≠ algebraMap K F c)

    (hsep : ∀ s' : AlgebraicCurve.Place K F, (∀ t ∈ T, t ∈ s'.toValuationSubring) →
      (∀ t ∈ T, ∀ c : K, t - algebraMap K F c ∈ s.toValuationSubring.nonunits →
        t - algebraMap K F c ∈ s'.toValuationSubring.nonunits) → s' = s)
    (g : F) :
    g ∈ s.toValuationSubring ↔ φ g ∈ w.toValuationSubring := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_iff_map_mem_of_forall_place_eq_of_testFamily.solution
