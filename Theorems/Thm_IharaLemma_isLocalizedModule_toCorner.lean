import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.Algebra.Module.LocalizedModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_isLocalizedModule_toCorner

set_option autoImplicit false

theorem IharaLemma.isLocalizedModule_toCorner {B : Type} [CommRing B] {M : Type}
    [AddCommGroup M] [Module B M] {e : B} (he : IsIdempotentElem e) (𝔪 : Ideal B)
    [h𝔪 : 𝔪.IsMaximal] (hem : e ∉ 𝔪) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) :
    IsLocalizedModule 𝔪.primeCompl (IharaLemma.toCorner (M := M) e) := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_isLocalizedModule_toCorner.solution
