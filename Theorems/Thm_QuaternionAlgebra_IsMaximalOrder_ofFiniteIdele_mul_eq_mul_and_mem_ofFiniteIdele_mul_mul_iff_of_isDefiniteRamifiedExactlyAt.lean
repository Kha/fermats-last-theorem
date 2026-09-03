import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hπv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (π : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hπP : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ π ↔
      h ∈ Λ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.ofFiniteIdele Λ (x * π) = Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π ∧
    (∀ z : ℍ[ℚ, a, b], z ∈ Submodule.ofFiniteIdele Λ (x * π * π) ↔
      ∃ y ∈ Submodule.ofFiniteIdele Λ x, z = (q' : ℚ) • y) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt.solution
