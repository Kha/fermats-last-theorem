import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DeligneDatum.exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) [𝔭.IsPrime] (h𝔭 : algebraMap 𝒪 B π ∈ 𝔭)
    (M A₀ A₁ : FullLattice 𝒪 K) (hM : d.VertexNondegAt π 𝔭 M) (hA : d.EdgeNondegAt π 𝔭 A₀ A₁) :
    ∃ c : Kˣ, latticeMap (scalarGL c) M.1 = A₀.1 ∨ latticeMap (scalarGL c) M.1 = A₁.1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_latticeMap_scalarGL_eq_or_of_vertexNondegAt_of_edgeNondegAt.solution
