import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective

theorem HopfAlgebra.isHopfGalois_of_isCocomm_of_finiteType_of_surjective
    (k : Type) [Field k]
    (H : Type) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [Coalgebra.IsCocomm k H]
    (H' : Type) [CommRing H'] [HopfAlgebra k H']
    (qc : H →ₐc[k] H') (hqc : Function.Surjective qc) :
    HopfAlgebra.IsHopfGalois qc := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isHopfGalois_of_isCocomm_of_finiteType_of_surjective.solution
