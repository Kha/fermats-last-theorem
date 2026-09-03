import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_archRealProjTau_unitsMap_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.archRealProjTau_unitsMap_algebraMap
    (K : Type*) [Field K] [NumberField K] (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α) = τ α := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_archRealProjTau_unitsMap_algebraMap.solution
