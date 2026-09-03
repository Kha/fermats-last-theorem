import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_forall_pow_eq

set_option autoImplicit false
theorem IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_forall_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {ι : Type*} {n : ℕ} (u : ι → E) (α : ι → M) (hα : ∀ i, α i ^ n = algebraMap E M (u i))
    (hgen : ∀ σ : M ≃ₐ[E] M, (∀ i, σ (α i) = α i) → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hu : ∀ i, v.valuation E (u i) = 1)
    (hnv : ((n : ℕ) : NumberField.RingOfIntegers E) ∉ v.asIdeal)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    w.1.asIdeal.inertia (M ≃ₐ[E] M) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_forall_pow_eq.solution
