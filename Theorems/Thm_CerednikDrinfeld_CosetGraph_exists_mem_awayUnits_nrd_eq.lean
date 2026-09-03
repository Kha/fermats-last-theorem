import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ γ : (ℍ[ℚ, a, b])ˣ, γ ∈ CosetGraph.awayUnits R v ∧ QuaternionAlgebra.nrd (γ : ℍ[ℚ, a, b]) = (r : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq.solution
