import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_nrd_mul_pow_eq_pow_of_mem_awayUnits
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : (ℍ[ℚ, a, b])ˣ) (hγ : γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R v) :
    ∃ i j : ℕ, nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((r : ℚ) ^ i) = (r : ℚ) ^ j ∨
      nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((r : ℚ) ^ i) = -((r : ℚ) ^ j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits.solution
