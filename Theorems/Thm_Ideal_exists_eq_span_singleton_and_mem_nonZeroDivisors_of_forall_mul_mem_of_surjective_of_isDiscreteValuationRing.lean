import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing

set_option autoImplicit false

theorem Ideal.exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S₁ : Type*} [CommRing S₁] [IsDomain S₁] [IsDiscreteValuationRing S₁]
    {S₂ : Type*} [CommRing S₂] [IsDomain S₂]
    (f₁ : R →+* S₁) (hf₁ : Function.Surjective f₁) (f₂ : R →+* S₂)
    (t s ϖ : R) (w : Rˣ) (hker₁ : RingHom.ker f₁ = Ideal.span {t}) (hker₂ : RingHom.ker f₂ = Ideal.span {s})
    (hts : t ∉ Ideal.span {s}) (hprod : t * s = ϖ * w) (hϖ : ϖ ∈ nonZeroDivisors R)
    (P : Ideal R) (hP : ∀ r : R, ϖ * r ∈ P → r ∈ P) (hPt : ¬ P ≤ Ideal.span {t}) (hPs : ¬ P ≤ Ideal.span {s}) :
    ∃ π : R, P = Ideal.span {π} ∧ π ∈ nonZeroDivisors R ∧
      (∀ r : R, π * r ∈ Ideal.span {t} → r ∈ Ideal.span {t}) ∧
      (∀ r : R, π * r ∈ Ideal.span {s} → r ∈ Ideal.span {s}) ∧
      (∀ r : R, π * r ∈ Ideal.span {t * s} → r ∈ Ideal.span {t * s}) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing.solution
