import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one
    (K : Type) [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ T : Finset (HeightOneSpectrum (𝓞 K)), T₀ ⊆ T →
      (∏ v : InfinitePlace K, v x ^ v.mult) *
          ∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) x‖ = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_finset_forall_prod_infinitePlace_pow_mul_prod_norm_algebraMap_adicCompletion_eq_one.solution
