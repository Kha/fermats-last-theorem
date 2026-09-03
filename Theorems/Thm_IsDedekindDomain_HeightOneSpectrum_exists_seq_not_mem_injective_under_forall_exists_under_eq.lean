import Mathlib
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_seq_not_mem_injective_under_forall_exists_under_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (SL : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ rec : ℕ → HeightOneSpectrum (𝓞 L), (∀ k, rec k ∉ SL) ∧
      (Function.Injective fun k => HeightOneSpectrum.under (𝓞 K) (rec k)) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
        ∃ k, HeightOneSpectrum.under (𝓞 K) (rec k) = HeightOneSpectrum.under (𝓞 K) w := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_seq_not_mem_injective_under_forall_exists_under_eq.solution
