import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "IsDedekindDomain NumberField QuaternionAlgebra~nrd_eq_det_of_ringEquiv"

theorem QuaternionAlgebra.IsMaximalOrder.exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : (q : 𝓞 ℚ) ∉ v.asIdeal) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal)
    {N : ℕ} (hNv : (N : 𝓞 ℚ) ∈ v.asIdeal)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ s ∈ Submodule.localBox Λ v,
      (∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
            algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
              ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
                algebraMap ℚ (v.adicCompletion ℚ) b])) →
        nrd (ψ s) = 1) ∧
      ∃ z ∈ Submodule.localBox Λ v, s = c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) + (N : ℚ) • z := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul.solution
