import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
namespace P2MW.S_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd

set_option autoImplicit false
open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

theorem solution
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (𝔣 : Ideal (𝓞 E)) (h𝔣 : 𝔣 ≠ ⊥)
    (hram : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥ → v.asIdeal ∣ 𝔣) (n : ℕ) :
    ∃ 𝔣' : Ideal (𝓞 E), 𝔣 ∣ 𝔣' ∧ (∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣) ∧
      NumberField.NormIndex.IsAdmissibleModulusOfDegree E F n 𝔣' := by
  classical

  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ 𝔣}.Finite := Ideal.finite_factors h𝔣
  set N : ℕ := 1 + hfin.toFinset.sup (fun v => NumberField.NormIndex.admissibleExpOfDegree E n v) with hN
  have hN1 : 1 ≤ N := Nat.le_add_right _ _
  refine ⟨𝔣 ^ N, dvd_pow_self 𝔣 (by omega), fun v hv => ?_, ?_, fun v hv => ?_⟩
  · exact (Ideal.prime_of_isPrime v.ne_bot v.isPrime).dvd_of_dvd_pow hv
  · exact pow_ne_zero _ h𝔣
  · have hv𝔣 : v.asIdeal ∣ 𝔣 := hram v hv
    have hle : NumberField.NormIndex.admissibleExpOfDegree E n v ≤ N := by
      have : NumberField.NormIndex.admissibleExpOfDegree E n v
          ≤ hfin.toFinset.sup (fun v => NumberField.NormIndex.admissibleExpOfDegree E n v) :=
        Finset.le_sup (f := fun v => NumberField.NormIndex.admissibleExpOfDegree E n v) (hfin.mem_toFinset.mpr hv𝔣)
      omega
    exact (pow_dvd_pow _ hle).trans (pow_dvd_pow_of_dvd hv𝔣 N)
