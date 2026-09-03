import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem Rat.exists_ternary_isotropic_adicCompletion_of_intCast_notMem
    (m n : ℤ) (v : HeightOneSpectrum (𝓞 ℚ))
    (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (hm : ((m : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) (hn : ((n : ℤ) : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
      z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ)) * x ^ 2
        - (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) * y ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rat_exists_ternary_isotropic_adicCompletion_of_intCast_notMem.solution
