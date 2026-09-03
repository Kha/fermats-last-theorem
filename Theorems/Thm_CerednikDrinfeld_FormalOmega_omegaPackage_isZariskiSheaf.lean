import Mathlib
import Definitions.Def_CerednikDrinfeld_OmegaModuliPackage
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_omegaPackage_isZariskiSheaf

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalOmega.omegaPackage_isZariskiSheaf
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {O : Type} [CommRing O]
    (p : ℕ) [Fact p.Prime] (π : 𝒪) (c : 𝒪 →+* O) :
    (omegaPackage (K := K) p π c).IsZariskiSheaf := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_omegaPackage_isZariskiSheaf.solution
