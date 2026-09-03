import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Topology

theorem NumberField.exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (Z : ℂ → ℂ) (κ : ℂ), κ ≠ 0 ∧
      MeromorphicOn Z Set.univ ∧
      AnalyticOnNhd ℂ Z {w : ℂ | w ≠ 1} ∧
      (∀ w : ℂ, 1 < w.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) ∧
        Z w * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) = 1) ∧
      Tendsto (fun w : ℂ => (w - 1) * Z w) (𝓝[≠] (1 : ℂ)) (𝓝 κ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul.solution
