import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import P2M.Util
import P2M.Sol.S_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le

set_option autoImplicit false

theorem RegularSingular.hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le
    {ι : Type*} [Fintype ι] (r : ℕ) (e : ι → ℂ) (n : ι → ℕ)
    (hinj : Function.Injective fun i => (e i, n i)) (θ : ℝ) (hθ : ∀ i, (e i).re < θ)
    (F Fz : ℝ → ℝ → (Fin r → ℂ)) (c g : ι → ℝ → (Fin r → ℂ))
    (hF : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Set.Ioc (0 : ℝ) 2, HasDerivAt (fun z => F y z) (Fz y z) z)
    (hFz : ∀ y ∈ Set.Ioc (0 : ℝ) 1, ContinuousOn (fun z => Fz y z) (Set.Ioc 0 2))
    (hg : ∀ i, ContinuousOn (g i) (Set.Ioc 0 2))
    (hexpF : ∀ z ∈ Set.Ioc (0 : ℝ) 2, ∃ K : ℝ, ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) • c i z‖ ≤ K * y ^ θ)
    (hexpFz : ∀ z₀ ∈ Set.Ioc (0 : ℝ) 2, ∃ K ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Ioc (0 : ℝ) 2, |z - z₀| < ε →
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖Fz y z - ∑ i, ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ n i) • g i z‖ ≤ K * y ^ θ) :
    ∀ i, ∀ z ∈ Set.Ioo (0 : ℝ) 2, HasDerivAt (c i) (g i z) z := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_hasDerivAt_expLogCoeff_of_hasDerivAt_of_norm_sub_sum_le.solution
