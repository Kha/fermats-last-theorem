import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.Etale.finite_etale_faithfullyFlat_away_of_isIdempotentElem
    {S C : Type} [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] [Algebra.Etale S C]
    (e : C) (he : IsIdempotentElem e)
    (hsurj : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → ∃ 𝔭 : Ideal C, 𝔭.IsPrime ∧ 𝔭.comap (algebraMap S C) = 𝔮 ∧ e ∉ 𝔭) :
    Module.Finite S (Localization.Away e) ∧ Algebra.Etale S (Localization.Away e) ∧
      Module.FaithfullyFlat S (Localization.Away e) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem.solution
