import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_isFractionRing_surjective_comp_of_finiteDimensional_of_isAdicComplete

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_isFractionRing_surjective_comp_of_finiteDimensional_of_isAdicComplete
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (k : Type) [Field k] [IsAlgClosed k] (φ : R →+* k) (hφ : Function.Surjective φ)
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : Algebra R' K') (_ : IsFractionRing R' K') (φ' : R' →+* k),
      Function.Surjective φ' ∧ φ'.comp (algebraMap R R') = φ ∧
      (algebraMap R' K').comp (algebraMap R R') = (algebraMap K K').comp (algebraMap R K) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_isFractionRing_surjective_comp_of_finiteDimensional_of_isAdicComplete.solution
