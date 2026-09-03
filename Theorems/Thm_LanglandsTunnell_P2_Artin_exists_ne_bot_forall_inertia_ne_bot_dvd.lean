import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.exists_ne_bot_forall_inertia_ne_bot_dvd
    (E L' : Type*) [Field E] [NumberField E] [Field L'] [NumberField L'] [Algebra E L'] [IsGalois E L'] :
    ∃ 𝔯 : Ideal (𝓞 E), 𝔯 ≠ ⊥ ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (Q : Ideal (𝓞 L')), Q.IsMaximal → Q.under (𝓞 E) = v.asIdeal →
        Q.inertia (L' ≃ₐ[E] L') ≠ ⊥ → v.asIdeal ∣ 𝔯 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_ne_bot_dvd.solution
