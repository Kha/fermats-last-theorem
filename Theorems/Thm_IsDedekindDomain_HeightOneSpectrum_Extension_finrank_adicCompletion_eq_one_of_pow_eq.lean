import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq

set_option autoImplicit false
theorem IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq
    (E M : Type*) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M] [IsGalois E M]
    {n : ℕ} (hζ : (primitiveRoots n E).Nonempty) (u : E) (α : M) (hα : α ^ n = algebraMap E M u)
    (hgen : ∀ σ : M ≃ₐ[E] M, σ α = α → σ = 1)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hb : ∃ b : v.adicCompletion E, algebraMap E (v.adicCompletion E) u = b ^ n)
    (w : v.Extension (NumberField.RingOfIntegers M)) :
    Module.finrank (v.adicCompletion E) (w.1.adicCompletion M) = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq.solution
