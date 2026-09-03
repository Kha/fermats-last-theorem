import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : DeligneDatum (K := K) π B) :
    ∃ (k : ℕ) (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤) (M' M : Fin k → FullLattice 𝒪 K),
      ∀ i : Fin k, (M' i).1 ≤ (M i).1 ∧ (∀ v ∈ (M i).1, algebraMap 𝒪 K π • v ∈ (M' i).1) ∧ HasDetIndex π (M' i).1 0 ∧
        (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i)))).InEdgeChart π (M' i) (M i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_finite_cover_inEdgeChart_hasDetIndex_of_isNilpotent.solution
