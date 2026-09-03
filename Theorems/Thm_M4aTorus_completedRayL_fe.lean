import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import P2M.Util
import P2M.Sol.S_M4aTorus_completedRayL_fe
set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors
theorem M4aTorus.completedRayL_fe
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
      (∀ s : ℂ, 1 < s.re →
        G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ h𝔣' : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
        M4aP2.IsPrimitiveMod K 𝔣 χ →
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          F (1 - s) = (-Complex.I) ^ S.card *
            (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by p2m_exact_reverting @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution
