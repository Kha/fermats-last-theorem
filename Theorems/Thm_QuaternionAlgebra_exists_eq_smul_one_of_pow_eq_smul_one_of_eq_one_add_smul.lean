import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star

set_option autoImplicit false

open scoped Quaternion
p2m_open "QuaternionAlgebra~nrd~trd"

theorem QuaternionAlgebra.exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul
    {a b : ℚ} (ha : a < 0) (hb : b < 0) (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : IsOrder L)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (s : ℕ) (hs : ¬ ℓ ∣ s)
    (γ y : ℍ[ℚ, a, b]) (hy : (s : ℚ) • y ∈ L) (hγ : γ = 1 + (ℓ : ℚ) • y)
    (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : γ ^ n = c • (1 : ℍ[ℚ, a, b])) :
    ∃ c' : ℚ, γ = c' • (1 : ℍ[ℚ, a, b]) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_eq_smul_one_of_pow_eq_smul_one_of_eq_one_add_smul.solution
