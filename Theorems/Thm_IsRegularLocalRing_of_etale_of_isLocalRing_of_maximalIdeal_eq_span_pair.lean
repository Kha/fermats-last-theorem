import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing Polynomial

universe u v

theorem IsRegularLocalRing.of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (R₁ : Type v) [CommRing R₁] [IsLocalRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Algebra.Etale R R₁] :
    IsRegularLocalRing R₁ ∧ ringKrullDim R₁ = 2 ∧
      maximalIdeal R₁ = Ideal.span {algebraMap R R₁ ϖ, algebraMap R R₁ s} ∧
      IsAdicComplete (maximalIdeal R₁) R₁ := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_of_etale_of_isLocalRing_of_maximalIdeal_eq_span_pair.solution
