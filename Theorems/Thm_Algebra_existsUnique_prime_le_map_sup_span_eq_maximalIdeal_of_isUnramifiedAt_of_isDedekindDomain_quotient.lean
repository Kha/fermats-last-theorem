import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient

set_option autoImplicit false

universe u

open IsLocalRing

theorem Algebra.existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient
    (A' : Type u) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (K' : Type u) [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A' B] [Module.Finite A' B] [FaithfulSMul A' B]
    (L' : Type u) [Field L'] [Algebra B L'] [IsFractionRing B L'] [Algebra K' L'] [Algebra A' L']
    [IsScalarTower A' K' L'] [IsScalarTower A' B L'] [Algebra.IsSeparable K' L']
    (ϖ t : A') (htp : (Ideal.span ({t} : Set A')).IsPrime) [CharZero (A' ⧸ Ideal.span ({t} : Set A'))]
    (hfib : IsDedekindDomain (B ⧸ Ideal.span ({algebraMap A' B ϖ} : Set B)))
    (y : Ideal B) [y.IsMaximal]
    (hmax : y.comap (algebraMap A' B) = Ideal.span {ϖ, t})
    (hreg : IsRegularLocalRing (Localization.AtPrime (y.comap (algebraMap A' B))))
    (hdim : ringKrullDim (Localization.AtPrime (y.comap (algebraMap A' B))) = 2)
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ y → Q.height = 1 → algebraMap A' B t ∉ Q → Algebra.IsUnramifiedAt A' Q) :
    ∃ 𝔔 : Ideal B, 𝔔.IsPrime ∧ 𝔔 ≤ y ∧ algebraMap A' B t ∈ 𝔔 ∧ algebraMap A' B ϖ ∉ 𝔔 ∧
      (∀ (O : Type u) [CommRing O] [IsLocalRing O] [Algebra B O] [IsLocalization.AtPrime O y],
        Ideal.map (algebraMap B O) 𝔔 ⊔ Ideal.span {algebraMap B O (algebraMap A' B ϖ)} = maximalIdeal O) ∧
      ∀ 𝔔' : Ideal B, 𝔔'.IsPrime → 𝔔' ≤ y → algebraMap A' B t ∈ 𝔔' → algebraMap A' B ϖ ∉ 𝔔' → 𝔔' = 𝔔 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_existsUnique_prime_le_map_sup_span_eq_maximalIdeal_of_isUnramifiedAt_of_isDedekindDomain_quotient.solution
