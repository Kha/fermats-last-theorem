import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq

set_option autoImplicit false

universe u

theorem ValuationSubring.henselianLocalRing_comap_of_forall_comap_eq_imp_eq
    {K : Type u} [Field K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (hAtop : A ≠ ⊤)
    (huniq : ∀ B : ValuationSubring Ω,
      B.comap (algebraMap K Ω) = A.comap (algebraMap K Ω) → B = A) :
    HenselianLocalRing ↥(A.comap (algebraMap K Ω)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_henselianLocalRing_comap_of_forall_comap_eq_imp_eq.solution
