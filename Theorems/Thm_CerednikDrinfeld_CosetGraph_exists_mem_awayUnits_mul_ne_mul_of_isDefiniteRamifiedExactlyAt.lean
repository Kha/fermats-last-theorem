import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra hiding nrd open IsDedekindDomain CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt
    {rbar : ℕ} [Fact rbar.Prime]
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (hrr : rbar ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R v, ∃ y ∈ CerednikDrinfeld.CosetGraph.awayUnits R v,
      (x : ℍ[ℚ, a₁, b₁]) * (y : ℍ[ℚ, a₁, b₁]) ≠ (y : ℍ[ℚ, a₁, b₁]) * (x : ℍ[ℚ, a₁, b₁]) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_mul_ne_mul_of_isDefiniteRamifiedExactlyAt.solution
