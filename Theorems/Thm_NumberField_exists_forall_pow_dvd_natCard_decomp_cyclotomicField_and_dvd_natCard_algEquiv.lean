import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain

theorem NumberField.exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime] (N : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      p ^ N ∣ Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) ∧
      ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 (CyclotomicField (p ^ k) E)), w.under (𝓞 E) = v →
        p ^ N ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E (CyclotomicField (p ^ k) E) w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv.solution
