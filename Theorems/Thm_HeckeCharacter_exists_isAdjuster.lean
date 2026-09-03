import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_isAdjuster

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.exists_isAdjuster
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_isAdjuster.solution
