import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val

set_option autoImplicit false

open CerednikDrinfeld QuaternionAlgebra IsDedekindDomain
open scoped Quaternion NumberField

theorem CerednikDrinfeld.CosetGraph.exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ w : (ℍ[ℚ, a₁, b₁])ˣ, w ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v ∧ nrd (w : ℍ[ℚ, a₁, b₁]) = (r : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_exists_mem_awayUnits_nrd_eq_of_le_isMaximalOrder.solution
