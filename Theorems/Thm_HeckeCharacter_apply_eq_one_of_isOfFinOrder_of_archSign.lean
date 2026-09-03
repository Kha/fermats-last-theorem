import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import P2M.Util
import P2M.Sol.S_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem HeckeCharacter.apply_eq_one_of_isOfFinOrder_of_archSign
    (K : Type*) [Field K] [NumberField K] {M : Type*} [CommMonoid M]
    (η : (AdeleRing (𝓞 K) K)ˣ →* M) (hη : IsOfFinOrder η)
    (u : (AdeleRing (𝓞 K) K)ˣ) (hfin : (u : AdeleRing (𝓞 K) K).2 = 1)
    (hpos : ∀ τ : K →+* ℝ, HeckeCharacter.archSign K τ u) :
    η u = 1 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_apply_eq_one_of_isOfFinOrder_of_archSign.solution
