import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.padicValRat_nrd_eq_zero_of_mem_awayUnits
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    (∀ γ ∈ CosetGraph.awayUnits R v, ∀ p : ℕ, p.Prime → p ≠ r →
        padicValRat p (nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 0) ∧
      (∀ c : ℚˣ, (∀ p : ℕ, p.Prime → p ≠ r → padicValRat p (c : ℚ) = 0) →
        Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c ∈ CosetGraph.awayUnits R v) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits.solution
