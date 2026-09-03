import Definitions.Def_DedekindDomain_IntegralClosure
import P2M.Util
import P2M.Sol.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
    (K : Type) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K)
    (F : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (p₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)),
      p₀ ∉ F ∧ w₀.1 ≠ w₂.1 ∧
      p₀.asIdeal.inertiaDeg' w₀.1.asIdeal = 1 ∧
      ∀ w : p₀.Extension (𝓞 K), Ideal.ramificationIdx' p₀.asIdeal w.1.asIdeal = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one.solution
