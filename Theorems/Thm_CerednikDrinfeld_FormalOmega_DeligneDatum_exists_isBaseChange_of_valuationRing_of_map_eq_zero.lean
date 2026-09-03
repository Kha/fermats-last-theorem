import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~Omega"

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_isBaseChange_of_valuationRing_of_map_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) :
    ∃ d₀ : DeligneDatum (K := K) π V,
      DeligneDatum.IsBaseChange (K := K) (π := π) (IsScalarTower.toAlgHom 𝒪 V L) d₀ d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isBaseChange_of_valuationRing_of_map_eq_zero.solution
