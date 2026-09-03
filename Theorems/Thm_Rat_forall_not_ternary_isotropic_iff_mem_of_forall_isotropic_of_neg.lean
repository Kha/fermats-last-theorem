import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg
    (a b : ℚ) (ha : a < 0) (hb : b < 0) (q : ℕ) (hq : q.Prime)
    (hiso : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∉ v.asIdeal →
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
          z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0) ↔
        (q : 𝓞 ℚ) ∈ v.asIdeal := by p2m_exact_reverting @_root_.P2MW.S_Rat_forall_not_ternary_isotropic_iff_mem_of_forall_isotropic_of_neg.solution
