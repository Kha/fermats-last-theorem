import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange
import P2M.Util
import P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot

set_option autoImplicit false
theorem IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : v.Extension (NumberField.RingOfIntegers L))
    (hI : w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥)
    (u : v.adicCompletion K) (hu : Valued.v u = 1) :
    ∃ y : w.1.adicCompletion L, Valued.v y = 1 ∧ Algebra.norm (v.adicCompletion K) y = u := by p2m_exact_reverting @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot.solution
