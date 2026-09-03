import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd

set_option autoImplicit false
open NumberField IsDedekindDomain HeckeCharacter LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.unitIdeles_le_unitIdeles_of_dvd
    (F : Type*) [Field F] [NumberField F] {𝔪 𝔪' : Ideal (𝓞 F)} (h' : 𝔪' ≠ ⊥) (h : 𝔪 ∣ 𝔪') :
    unitIdeles F 𝔪' ≤ unitIdeles F 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_unitIdeles_le_unitIdeles_of_dvd.solution
