import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective

set_option autoImplicit false

theorem Algebra.QuasiFiniteAt.exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective
    {R S K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] [Field K]
    [Algebra R S] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsScalarTower R S K]
    (hSK : Function.Injective (algebraMap S K)) [Algebra.FiniteType R S]
    (𝔔 : Ideal S) [𝔔.IsPrime] [Algebra.QuasiFiniteAt R 𝔔] :
    ∀ s : S, ∃ a b : R, b ∉ 𝔔.comap (algebraMap R S) ∧ algebraMap R S b * s = algebraMap R S a := by p2m_exact_reverting @_root_.P2MW.S_Algebra_QuasiFiniteAt_exists_algebraMap_mul_eq_of_isIntegrallyClosed_of_injective.solution
