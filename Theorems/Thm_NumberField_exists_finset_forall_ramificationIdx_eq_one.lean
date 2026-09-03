import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_finset_forall_ramificationIdx_eq_one

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.exists_finset_forall_ramificationIdx_eq_one (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S₀ → (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_finset_forall_ramificationIdx_eq_one.solution
