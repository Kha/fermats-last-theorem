import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_forall_map_algClosed_eq_of_isReduced
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] [IsReduced B]
    (d d' : DeligneDatum (K := K) π B)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra 𝒪 Ω] (f : B →ₐ[𝒪] Ω),
      DeligneDatum.map (K := K) π f d = DeligneDatum.map (K := K) π f d') :
    d = d' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_forall_map_algClosed_eq_of_isReduced.solution
