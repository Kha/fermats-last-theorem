import Mathlib
import P2M.Util
import P2M.Sol.S_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing

set_option autoImplicit false

universe u v

open IsLocalRing

theorem HenselianLocalRing.exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    {A : Type v} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    (hRA : Function.Injective (algebraMap R A))
    (𝔪 : Ideal A) [𝔪.IsMaximal] (hϖ𝔪 : algebraMap R A ϖ ∈ 𝔪)
    (t : A) (ht : t ∈ 𝔪)

    (hisol : ∀ P : Ideal A, P.IsPrime → t ∈ P → algebraMap R A ϖ ∈ P → P ≤ 𝔪 → P = 𝔪)

    (hreg : ∀ a : A, t * a ∈ Ideal.span {algebraMap R A ϖ} →
      ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {algebraMap R A ϖ}) :
    ∃ I : Ideal A,
      (∀ a : A, a ∈ I ↔ ∃ s : A, s ∉ 𝔪 ∧ s * a ∈ Ideal.span {t}) ∧
      t ∈ I ∧ I ≤ 𝔪 ∧
      Module.Finite R (A ⧸ I) ∧
      (∀ y : A ⧸ I, algebraMap R (A ⧸ I) ϖ * y = 0 → y = 0) ∧
      (∀ P : Ideal A, P.IsPrime → I ≤ P → P ≤ 𝔪) := by p2m_exact_reverting @_root_.P2MW.S_HenselianLocalRing_exists_ideal_moduleFinite_quotient_of_forall_isPrime_imp_eq_of_isDiscreteValuationRing.solution
