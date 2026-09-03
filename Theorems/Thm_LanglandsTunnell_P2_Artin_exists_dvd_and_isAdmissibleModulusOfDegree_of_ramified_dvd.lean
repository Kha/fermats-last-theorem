import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (𝔣 : Ideal (𝓞 E)) (h𝔣 : 𝔣 ≠ ⊥)
    (hram : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥ → v.asIdeal ∣ 𝔣) (n : ℕ) :
    ∃ 𝔣' : Ideal (𝓞 E), 𝔣 ∣ 𝔣' ∧ (∀ v : HeightOneSpectrum (𝓞 E), v.asIdeal ∣ 𝔣' → v.asIdeal ∣ 𝔣) ∧
      NumberField.NormIndex.IsAdmissibleModulusOfDegree E F n 𝔣' := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd.solution
