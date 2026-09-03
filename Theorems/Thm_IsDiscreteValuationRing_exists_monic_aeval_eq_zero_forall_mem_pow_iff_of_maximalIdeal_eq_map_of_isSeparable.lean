import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsDiscreteValuationRing.exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] [Algebra A₀ W₀] [IsLocalHom (algebraMap A₀ W₀)]
    (hW₀ : IsLocalRing.maximalIdeal W₀ = (IsLocalRing.maximalIdeal A₀).map (algebraMap A₀ W₀))
    [Module.Finite (ResidueField A₀) (ResidueField W₀)]
    [Algebra.IsSeparable (ResidueField A₀) (ResidueField W₀)] :
    ∃ (P : Polynomial A₀) (θ : W₀), P.Monic ∧ Irreducible (P.map (residue A₀)) ∧
      (P.map (residue A₀)).Separable ∧ aeval θ P = 0 ∧
      (∀ n : ℕ, ∀ w : W₀, ∃ g : Polynomial A₀, w - aeval θ g ∈ IsLocalRing.maximalIdeal W₀ ^ n) ∧
      (∀ n : ℕ, ∀ g : Polynomial A₀, aeval θ g ∈ IsLocalRing.maximalIdeal W₀ ^ n ↔
        g ∈ Ideal.span {P} ⊔ (IsLocalRing.maximalIdeal A₀ ^ n).map (Polynomial.C : A₀ →+* Polynomial A₀)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_forall_mem_pow_iff_of_maximalIdeal_eq_map_of_isSeparable.solution
