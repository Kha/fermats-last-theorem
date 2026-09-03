import Mathlib
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import P2M.Util
import P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

theorem NumberField.exists_continuousOn_exp_eq_rayClassLSeries
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
      (∀ s : ℝ, 1 < s → Summable fun v : HeightOneSpectrum (𝓞 K) =>
          M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 1 < s →
        ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
            M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution
