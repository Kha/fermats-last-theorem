import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one
    {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (v w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v)
    (hsplit : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x)
    (hs : ∃ s : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, s ≠ 1 ∧ s ≠ -1 ∧
      (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ s) = 1) ∧
      ∀ M : ℕ, M ≠ 0 →
        ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
          (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → w' ≠ w →
            ∃ z ∈ Submodule.localBox O w',
              β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
          (∃ z ∈ Submodule.localBox O w,
              β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s + (M : ℚ) • z))
    (s' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)
    (hs' : ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ s') = 1) :
    ∀ M : ℕ, M ≠ 0 →
      ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
        (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → w' ≠ w →
          ∃ z ∈ Submodule.localBox O w',
            β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
        (∃ z ∈ Submodule.localBox O w,
            β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s' + (M : ℚ) • z) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one.solution
