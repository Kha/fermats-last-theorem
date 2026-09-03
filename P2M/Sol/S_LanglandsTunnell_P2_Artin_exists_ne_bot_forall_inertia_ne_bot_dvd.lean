import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin

theorem solution
    (E L' : Type*) [Field E] [NumberField E] [Field L'] [NumberField L'] [Algebra E L'] [IsGalois E L'] :
    ∃ 𝔯 : Ideal (𝓞 E), 𝔯 ≠ ⊥ ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (Q : Ideal (𝓞 L')), Q.IsMaximal → Q.under (𝓞 E) = v.asIdeal →
        Q.inertia (L' ≃ₐ[E] L') ≠ ⊥ → v.asIdeal ∣ 𝔯 := by
  classical
  refine ⟨(differentIdeal (𝓞 E) (𝓞 L')).under (𝓞 E), ?_, fun v Q hQ hQv hv => ?_⟩
  · intro h
    exact differentIdeal_ne_bot (A := 𝓞 E) (B := 𝓞 L') (Ideal.eq_bot_of_comap_eq_bot h)
  · haveI := hQ
    haveI : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
    have hQbot : Q ≠ ⊥ := ne_bot_of_under_eq E L' v hQv
    haveI := v.isMaximal
    letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Field (𝓞 L' ⧸ Q) := Ideal.Quotient.field Q
    haveI : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    haveI : PerfectField (𝓞 E ⧸ v.asIdeal) := PerfectField.ofFinite
    haveI : Algebra.IsSeparable (𝓞 E ⧸ v.asIdeal) (𝓞 L' ⧸ Q) := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have hcard : Nat.card (Q.inertia (L' ≃ₐ[E] L')) ≠ 1 := fun h => hv (Subgroup.eq_bot_of_card_eq _ h)
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L' ≃ₐ[E] L')] at hcard
    have hram : ¬ Algebra.IsUnramifiedAt (𝓞 E) Q := by
      rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
      exact hcard
    have hdvd : Q ∣ differentIdeal (𝓞 E) (𝓞 L') := dvd_differentIdeal_iff.mpr hram
    rw [Ideal.dvd_iff_le] at hdvd ⊢
    rw [← hQv]
    exact Ideal.comap_mono hdvd
