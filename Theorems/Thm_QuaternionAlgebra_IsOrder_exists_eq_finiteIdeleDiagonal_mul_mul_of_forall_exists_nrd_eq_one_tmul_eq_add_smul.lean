import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
attribute [-simp] QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
    {a b : ℚ} (ha : a < 0) (hb : b < 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hdense : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      (∃ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 ∧ ¬ IsUnit x) →
      ∀ s' : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
        (∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
            ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
          (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
            φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
              algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
              algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
                ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                  algebraMap ℚ (w.adicCompletion ℚ) b])) →
          QuaternionAlgebra.nrd (φ s') = 1) →
        ∀ M : ℕ, M ≠ 0 →
          ∃ β : ℍ[ℚ, a, b], QuaternionAlgebra.nrd β = 1 ∧
            (∀ w' : HeightOneSpectrum (𝓞 ℚ), w' ≠ v → w' ≠ w →
              ∃ z ∈ Submodule.localBox O w',
                β ⊗ₜ[ℚ] (1 : w'.adicCompletion ℚ) = 1 + (M : ℚ) • z) ∧
            (∃ z ∈ Submodule.localBox O w,
                β ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s' + (M : ℚ) • z))
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hy : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1) :
    ∃ (β : (ℍ[ℚ, a, b])ˣ) (g u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      u ∈ Submodule.finiteIdeleStabilizer O ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      y = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * g * u := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul.solution
