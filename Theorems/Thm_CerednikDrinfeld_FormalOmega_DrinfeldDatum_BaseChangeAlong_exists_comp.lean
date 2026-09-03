import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_comp

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.BaseChangeAlong.exists_comp
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    {B'' : Type} [CommRing B''] [Algebra 𝒪 B''] (g : B →ₐ[𝒪] B') (h : B' →ₐ[𝒪] B'')
    {Q : DrinfeldDatum (K := K) π B} {Q' : DrinfeldDatum (K := K) π B'} {Q'' : DrinfeldDatum (K := K) π B''}
    (W : Q.BaseChangeAlong g Q') (W' : Q'.BaseChangeAlong h Q'') :
    ∃ W'' : Q.BaseChangeAlong (h.comp g) Q'',
      (∀ t, W''.τ₀ t = W'.τ₀ (W.τ₀ t)) ∧ (∀ t, W''.τ₁ t = W'.τ₁ (W.τ₁ t)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_BaseChangeAlong_exists_comp.solution
