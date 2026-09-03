import Mathlib
import Theorems.Thm_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem
import P2M.Util
namespace P2MW.S_NumberField_exists_finset_forall_ramificationIdx_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S₀ → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  classical
  obtain ⟨c, hc0, hc⟩ := IsDedekindDomain.exists_ne_zero_forall_isUnramifiedAt_of_notMem (𝓞 E) (𝓞 K)

  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {c}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hc0)
  refine ⟨hfin.toFinset, fun w hw => ?_⟩
  have hcw : algebraMap (𝓞 E) (𝓞 K) c ∉ w.asIdeal := by
    intro hmem
    apply hw
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact hmem
  haveI := hc w.asIdeal hcw
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal]; infer_instance
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := (w.under (𝓞 E)).asIdeal) (q := w.asIdeal)
    (w.under (𝓞 E)).ne_bot]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
