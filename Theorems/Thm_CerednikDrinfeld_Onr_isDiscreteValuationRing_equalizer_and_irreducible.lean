import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible

set_option autoImplicit false
theorem CerednikDrinfeld.Onr.isDiscreteValuationRing_equalizer_and_irreducible
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hπ0 : algebraMap 𝒪 Onr π ≠ 0)
    (F : Onr ≃ₐ[𝒪] Onr) :
    IsDiscreteValuationRing ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ∧ Irreducible (algebraMap 𝒪 ↥(AlgHom.equalizer (F : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Onr_isDiscreteValuationRing_equalizer_and_irreducible.solution
