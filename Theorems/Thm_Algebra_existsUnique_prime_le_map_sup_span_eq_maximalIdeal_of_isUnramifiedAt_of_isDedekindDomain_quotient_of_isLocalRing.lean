import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing

set_option autoImplicit false

universe u

p2m_open "IsLocalRing~uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient"

theorem Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (ϖ t : R) (hϖ0 : ϖ ≠ 0) (hmax : maximalIdeal R = Ideal.span {ϖ, t})
    [hϖp : (Ideal.span ({ϖ} : Set R)).IsPrime] (hϖ : IsDiscreteValuationRing (R ⧸ Ideal.span ({ϖ} : Set R)))
    (htp : (Ideal.span ({t} : Set R)).IsPrime) [CharZero (R ⧸ Ideal.span ({t} : Set R))]
    (hfib : IsDedekindDomain (S ⧸ Ideal.span ({algebraMap R S ϖ} : Set S)))
    (x : Ideal S) [x.IsMaximal]
    (hunr : ∀ (𝔔 : Ideal S) [𝔔.IsPrime], 𝔔 ≤ x → 𝔔.height = 1 → algebraMap R S t ∉ 𝔔 → Algebra.IsUnramifiedAt R 𝔔) :
    ∃ 𝔔 : Ideal S, 𝔔.IsPrime ∧ 𝔔 ≤ x ∧ algebraMap R S t ∈ 𝔔 ∧ algebraMap R S ϖ ∉ 𝔔 ∧
      (∀ (O : Type u) [CommRing O] [IsLocalRing O] [Algebra S O] [IsLocalization.AtPrime O x],
        Ideal.map (algebraMap S O) 𝔔 ⊔ Ideal.span {algebraMap S O (algebraMap R S ϖ)} = maximalIdeal O) ∧
      ∀ 𝔔' : Ideal S, 𝔔'.IsPrime → 𝔔' ≤ x → algebraMap R S t ∈ 𝔔' → algebraMap R S ϖ ∉ 𝔔' → 𝔔' = 𝔔 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient_of_isLocalRing.solution
