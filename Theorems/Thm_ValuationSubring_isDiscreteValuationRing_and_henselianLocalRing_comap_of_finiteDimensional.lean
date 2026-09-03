import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
    {F E : Type} [Field F] [Field E] [CharZero F] [Algebra F E] (halg : Algebra.IsAlgebraic F E)
    (A : ValuationSubring E) (k₀ : IntermediateField F E)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ E)))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ E)))
    (K : IntermediateField ↥k₀ E) (hK : FiniteDimensional ↥k₀ ↥K) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K E)) ∧ HenselianLocalRing ↥(A.comap (algebraMap ↥K E)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional.solution
