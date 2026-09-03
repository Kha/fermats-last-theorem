import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.exists_units_nrd_eq_prime_forall_mem_localBox
    {a b : ℚ} {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq : r ≠ q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓN : ¬ ℓ ∣ N) :
    ∃ s : (ℍ[ℚ, a, b])ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        ((CosetGraph.toLoc w s : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox R w) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        CosetGraph.toLoc w s ∈ Submodule.localBoxUnits R w) ∧
      QuaternionAlgebra.nrd (s : ℍ[ℚ, a, b]) = (ℓ : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_units_nrd_eq_prime_forall_mem_localBox.solution
