import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_Onr_faithfullyFlat

set_option autoImplicit false

theorem CerednikDrinfeld.Onr.faithfullyFlat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr]
    (hinj : Function.Injective (algebraMap 𝒪 Onr)) (hproper : Ideal.span {algebraMap 𝒪 Onr π} ≠ ⊤) :
    Module.FaithfullyFlat 𝒪 Onr := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_Onr_faithfullyFlat.solution
