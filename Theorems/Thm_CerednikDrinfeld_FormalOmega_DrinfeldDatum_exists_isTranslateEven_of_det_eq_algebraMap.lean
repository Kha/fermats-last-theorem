import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_of_det_eq_algebraMap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateEven_of_det_eq_algebraMap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c : Kˣ) (e : 𝒪ˣ)
    (hdet : ((Matrix.GeneralLinearGroup.det (scalarGL c * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e) :
    ∃ Q' : DrinfeldDatum (K := K) π B, Q.IsTranslateEven g c Q' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateEven_of_det_eq_algebraMap.solution
