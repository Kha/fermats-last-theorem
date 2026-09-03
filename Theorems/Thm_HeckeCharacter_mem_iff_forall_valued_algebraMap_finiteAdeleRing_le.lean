import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem HeckeCharacter.mem_iff_forall_valued_algebraMap_finiteAdeleRing_le
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (r : 𝓞 K) :
    r ∈ 𝔣 ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (r : K)) v) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_mem_iff_forall_valued_algebraMap_finiteAdeleRing_le.solution
