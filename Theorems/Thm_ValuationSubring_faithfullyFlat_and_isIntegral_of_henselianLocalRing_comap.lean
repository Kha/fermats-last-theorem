import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap

set_option autoImplicit false

universe u v

theorem ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L)
    [HenselianLocalRing ↥(A.comap (algebraMap K L))] [IsDiscreteValuationRing ↥(A.comap (algebraMap K L))]
    [Algebra ↥(A.comap (algebraMap K L)) ↥A]
    (halg : ∀ x : ↥(A.comap (algebraMap K L)),
      ((algebraMap ↥(A.comap (algebraMap K L)) ↥A x : ↥A) : L) = algebraMap K L (x : K)) :
    Module.FaithfullyFlat ↥(A.comap (algebraMap K L)) ↥A ∧
      Algebra.IsIntegral ↥(A.comap (algebraMap K L)) ↥A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap.solution
