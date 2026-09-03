import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL

set_option autoImplicit false

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.Omega.action_scalarGL
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    (B : Type) [CommRing B] [Algebra 𝒪 B] (c : Kˣ) (d : (Omega K π).obj B) :
    (Omega.action K π).act B (scalarGL c) d = d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL.solution
