import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega~Omega"

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_edge_nondeg_saturation_of_valuationRing
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra 𝒪 V] (hV : algebraMap 𝒪 V π = 0)
    (L : Type) [Field L] [Algebra 𝒪 L] [Algebra V L] [IsScalarTower 𝒪 V L] [IsFractionRing V L]
    (d : DeligneDatum (K := K) π L) (𝔭 : Ideal V) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : V) ⊗ₜ[𝒪] v ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M |
            LinearMap.rTensor (↥M.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : V) ⊗ₜ[𝒪] v' ∉ Submodule.span V {x : latticeBaseChange 𝒪 K V M' |
            LinearMap.rTensor (↥M'.1) (IsScalarTower.toAlgHom 𝒪 V L).toLinearMap x ∈ d.line M'}
          ⊔ (𝔭 • ⊤ : Submodule V (latticeBaseChange 𝒪 K V M'))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_edge_nondeg_saturation_of_valuationRing.solution
