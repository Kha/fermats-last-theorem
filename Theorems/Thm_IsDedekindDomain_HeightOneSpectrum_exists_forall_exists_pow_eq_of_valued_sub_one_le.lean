import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∀ a : v.adicCompletion K,
      Valued.v (a - 1) ≤ WithZero.exp (-(m : ℤ)) → ∃ c : v.adicCompletion K, c ^ n = a := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le.solution
