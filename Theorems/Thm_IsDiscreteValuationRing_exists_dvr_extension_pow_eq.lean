import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_dvr_extension_pow_eq

set_option autoImplicit false

universe u

theorem IsDiscreteValuationRing.exists_dvr_extension_pow_eq
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (n : ℕ) (hn : IsUnit ((n : ℕ) : R₀)) (hn0 : 0 < n) (π : R₀) (hπ : π ≠ 0) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K')
      (A' : Type u) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A')
      (_ : Algebra A' K') (_ : IsFractionRing A' K') (f : R₀ →+* A'),
      (algebraMap A' K').comp f = (algebraMap K K').comp (algebraMap R₀ K) ∧
      (∀ x : K, algebraMap K K' x ∈ Set.range (algebraMap A' K') → x ∈ Set.range (algebraMap R₀ K)) ∧
      ∃ ϖ : A', (algebraMap A' K' ϖ) ^ n = algebraMap K K' (algebraMap R₀ K π) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_dvr_extension_pow_eq.solution
