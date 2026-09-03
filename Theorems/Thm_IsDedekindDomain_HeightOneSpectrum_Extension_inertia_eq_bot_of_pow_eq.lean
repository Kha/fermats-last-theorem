import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_pow_eq

set_option autoImplicit false
theorem IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {n : ℕ} (u : E) (α : M) (hα : α ^ n = algebraMap E M u)
    (hgen : ∀ σ : M ≃ₐ[E] M, σ α = α → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hu : v.valuation E u = 1)
    (hnv : ((n : ℕ) : NumberField.RingOfIntegers E) ∉ v.asIdeal)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    w.1.asIdeal.inertia (M ≃ₐ[E] M) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_pow_eq.solution
