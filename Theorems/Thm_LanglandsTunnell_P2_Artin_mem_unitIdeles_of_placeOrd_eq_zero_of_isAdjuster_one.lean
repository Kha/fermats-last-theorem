import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_P2_Artin_mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem LanglandsTunnell.P2.Artin.mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 K), placeOrd K (projFin K z) w = 0) (hadj : IsAdjuster K 𝔣 z 1) :
    z ∈ unitIdeles K 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_P2_Artin_mem_unitIdeles_of_placeOrd_eq_zero_of_isAdjuster_one.solution
