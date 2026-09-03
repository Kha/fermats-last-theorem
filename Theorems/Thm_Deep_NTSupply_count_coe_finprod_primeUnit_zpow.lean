import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem Deep.NTSupply.count_coe_finprod_primeUnit_zpow
    (K : Type*) [Field K] [NumberField K]
    (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : (Function.support n).Finite) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      (((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ n v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) :
        FractionalIdeal ((𝓞 K)⁰) K) = n w := by p2m_exact_reverting @_root_.P2MW.S_Deep_NTSupply_count_coe_finprod_primeUnit_zpow.solution
