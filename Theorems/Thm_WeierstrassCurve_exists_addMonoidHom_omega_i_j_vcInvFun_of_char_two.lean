import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two
    {K : Type*} [Field K] [DecidableEq K] [CharP K 2] (ω : Kˣ)
    (hω : (ω : K) ^ 2 + ω + 1 = 0) :
    ∃ σ i j : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨ω, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (σ T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 1, ω⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (i T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, ω, (ω : K) ^ 2, ω⟩ : VariableChange K)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (j T)) ∧
      (∀ T, σ (σ (σ T)) = T) ∧ (∀ T, i (i T) = -T) ∧ (∀ T, j (j T) = -T) ∧
      (∀ T, i (j T) = -(j (i T))) ∧ (∀ T, σ (i T) = j (σ T)) ∧
      (∀ T, σ (j T) = j (i (σ T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 1, 0, 0⟩ →
        ∃ m : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
              m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
              m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
              m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = σ ∨ m = σ.comp σ ∨
              m = i ∨ m = i.comp σ ∨ m = i.comp (σ.comp σ) ∨
              m = j ∨ m = j.comp σ ∨ m = j.comp (σ.comp σ) ∨
              m = i.comp j ∨ m = (i.comp j).comp σ ∨ m = (i.comp j).comp (σ.comp σ)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 1, 0, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addMonoidHom_omega_i_j_vcInvFun_of_char_two.solution
