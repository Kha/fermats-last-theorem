import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    {Q : DrinfeldDatum (K := K) π B} {Q' Q'' : DrinfeldDatum (K := K) π B'}
    (h : Q.IsBaseChangeAlong f Q') (e : Q'.IsIsomorphic Q'') : Q.IsBaseChangeAlong f Q'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isBaseChangeAlong_of_isBaseChangeAlong_of_isIsomorphic.solution
