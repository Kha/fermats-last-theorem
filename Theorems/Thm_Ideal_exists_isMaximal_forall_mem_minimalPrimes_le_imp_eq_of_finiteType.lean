import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Ideal.exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (𝔪₀ : Ideal R) [𝔪₀.IsMaximal]
    (I : Ideal A) (hI : Ideal.map (algebraMap R A) 𝔪₀ ≤ I)
    (𝔮 : Ideal A) (h𝔮 : 𝔮 ∈ I.minimalPrimes) (hnm : ¬ 𝔮.IsMaximal)

    (hdim : ∀ P : Ideal A, P.IsPrime → 𝔮 < P → P.IsMaximal) :
    ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ 𝔮 ≤ 𝔪 ∧ ∀ 𝔮' ∈ I.minimalPrimes, 𝔮' ≤ 𝔪 → 𝔮' = 𝔮 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType.solution
