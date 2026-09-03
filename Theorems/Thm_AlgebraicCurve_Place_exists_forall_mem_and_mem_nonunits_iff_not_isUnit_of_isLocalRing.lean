import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Subring F) [IsLocalRing D] (hK : ∀ a : K, algebraMap K F a ∈ D)
    (hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d) :
    ∃ Q : AlgebraicCurve.Place K F, (∀ d : F, d ∈ D → d ∈ Q.toValuationSubring) ∧
      ∀ d : D, ((d : F) ∈ Q.toValuationSubring.nonunits ↔ ¬ IsUnit d) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing.solution
