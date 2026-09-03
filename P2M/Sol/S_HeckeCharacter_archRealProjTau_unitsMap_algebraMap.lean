import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
namespace P2MW.S_HeckeCharacter_archRealProjTau_unitsMap_algebraMap

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

theorem solution
    (K : Type*) [Field K] [NumberField K] (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) α) = τ α := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  simp only [placeOf, InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl
