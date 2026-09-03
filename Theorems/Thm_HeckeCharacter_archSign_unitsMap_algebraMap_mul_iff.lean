import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.archSign_unitsMap_algebraMap_mul_iff
    (K : Type*) [Field K] [NumberField K] (τ : K →+* ℝ) (α : Kˣ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α * u) ↔
      (0 < τ α ↔ archSign K τ u) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_archSign_unitsMap_algebraMap_mul_iff.solution
