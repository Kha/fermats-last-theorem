import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_isTranslateOdd_of_det_mul_eq_algebraMap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (g : Matrix.GeneralLinearGroup (Fin 2) K) (c₀ c₁ : Kˣ) (e : 𝒪ˣ)
    (hc : (c₀ : K) = algebraMap 𝒪 K π * c₁)
    (hdet : algebraMap 𝒪 K π * ((Matrix.GeneralLinearGroup.det (scalarGL c₁ * g⁻¹) : Kˣ) : K) = algebraMap 𝒪 K e) :
    ∃ Q' : DrinfeldDatum (K := K) π B, Q.IsTranslateOdd g c₀ c₁ Q' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_isTranslateOdd_of_det_mul_eq_algebraMap.solution
