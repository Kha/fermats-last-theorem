import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.isHopfGalois_of_isHopfGalois_baseChange_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    [Module.Flat ↥(HopfAlgebra.hopfKer qc) H]
    (hK : HopfAlgebra.IsHopfGalois
      (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H')) :
    HopfAlgebra.IsHopfGalois qc := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isHopfGalois_of_isHopfGalois_baseChange_of_flat.solution
