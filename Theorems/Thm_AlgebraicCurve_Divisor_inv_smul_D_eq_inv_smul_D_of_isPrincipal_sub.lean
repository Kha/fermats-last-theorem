import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub

theorem AlgebraicCurve.Divisor.inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub
    (K F : Type*) [Field K] [Field F] [Algebra K F] (p : ℕ) [CharP K p]
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : AlgebraicCurve.Place K F, v.ord u = 0) →
      u ∈ (algebraMap K F).range)
    (D₁ D₂ : AlgebraicCurve.Divisor K F) (h : AlgebraicCurve.Divisor.IsPrincipal (D₁ - D₂))
    (f₁ f₂ : F) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (h₁ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₁ v = v.ord f₁)
    (h₂ : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D₂ v = v.ord f₂) :
    f₁⁻¹ • KaehlerDifferential.D K F f₁ = f₂⁻¹ • KaehlerDifferential.D K F f₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_inv_smul_D_eq_inv_smul_D_of_isPrincipal_sub.solution
