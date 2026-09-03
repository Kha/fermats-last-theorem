import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem LanglandsTunnell.P2.Artin.exists_admissibleModulus_supported (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    ∃ 𝔣₀ : Ideal (𝓞 K), LanglandsTunnell.P2.Artin.IsAdmissibleModulus K L 𝔣₀ ∧
      ∀ v₀ : HeightOneSpectrum (𝓞 K), v₀.asIdeal ∣ 𝔣₀ →
        ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v₀.asIdeal ∧
          Q.inertia (L ≃ₐ[K] L) ≠ ⊥ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_exists_admissibleModulus_supported.solution
