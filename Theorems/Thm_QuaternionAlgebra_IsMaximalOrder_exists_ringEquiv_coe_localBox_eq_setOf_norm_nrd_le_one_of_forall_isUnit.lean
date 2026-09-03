import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    [Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ))] :
    ∃ Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
        ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v],
          (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]), (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])],
      (∀ c : v.adicCompletion ℚ, Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v c) •
          (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v],
            (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]), (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])])) ∧
      ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) =
        {x | ‖QuaternionAlgebra.nrd (Θ x)‖ ≤ 1} := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit.solution
