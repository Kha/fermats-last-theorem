import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.cutOut_smul_of_cutOut_vcFun
    (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (M' : ℕ) [NeZero M'] (h : ↥M'.primeFactors → Polynomial K)
    (hmonic : ∀ p, (h p).Monic) (hdeg : ∀ p : ↥M'.primeFactors, (h p).natDegree ≤ ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
    (g' : (C • W).toAffine.Point)
    (hg : (addOrderOf (WeierstrassCurve.Affine.Point.vcFun C W g') = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (W).toAffine.Nonsingular x₁ y₁),
          n • (WeierstrassCurve.Affine.Point.vcFun C W g') = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • (WeierstrassCurve.Affine.Point.vcFun C W g')) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (h p).IsRoot x₁)) :
    (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (C • W).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (h p)).IsRoot x₁) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun.solution
