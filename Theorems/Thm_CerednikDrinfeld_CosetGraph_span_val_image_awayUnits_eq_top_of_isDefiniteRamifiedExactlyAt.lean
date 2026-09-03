import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain CerednikDrinfeld

theorem CerednikDrinfeld.CosetGraph.span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt
    {rbar N : ℕ} [Fact rbar.Prime]
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₁ : IsEichlerOrder R₁ N)
    (r : ℕ) [Fact r.Prime] (hrr : rbar ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Submodule.span ℚ (Units.val '' (CerednikDrinfeld.CosetGraph.awayUnits R₁ v : Set (ℍ[ℚ, a₁, b₁])ˣ)) =
      (⊤ : Submodule ℚ ℍ[ℚ, a₁, b₁]) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_span_val_image_awayUnits_eq_top_of_isDefiniteRamifiedExactlyAt.solution
