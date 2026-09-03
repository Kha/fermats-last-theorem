import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd
    (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K) → Prop) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) //
        Ideal.absNorm I = n ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} : ℂ)) s ∧
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // p v} =>
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => (Nat.card {I : Ideal (𝓞 K) //
        Ideal.absNorm I = n ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → p v} : ℂ)) s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_lSeries_card_ideal_of_forall_dvd.solution
