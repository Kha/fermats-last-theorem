import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import P2M.Util
import P2M.Sol.S_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.GL2Real.exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe :
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
      ∃ x : GL (Fin 2) ℝ,
        (∃ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) ∨
        (∃ (r θ : ℝ) (hr : 0 < r), 0 < θ ∧ θ < Real.pi ∧ x⁻¹ * γ * x = ellipticElt r θ hr)) ∧
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (upperTriangular a₁ a₂ 0 h) δ₁ 1 →
          (0 < a₁ ∧ 0 < a₂) ∧
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (ellipticElt r θ hr) δ₁ 1 →
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
                ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
      ∃ (x : GL (Fin 2) ℝ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0),
        a₁ ≠ a₂ ∧ (a₁ < 0 ∨ a₂ < 0) ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe.solution
