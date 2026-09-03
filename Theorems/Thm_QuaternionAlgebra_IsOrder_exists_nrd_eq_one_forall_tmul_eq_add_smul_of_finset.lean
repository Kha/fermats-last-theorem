import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (s : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)
    (hs : ∀ w ∈ T,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ (s w)) = 1)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = 1 ∧
      ∀ w ∈ T, ∃ z ∈ Submodule.localBox O w,
        γ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s w + (M : ℚ) • z := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset.solution
