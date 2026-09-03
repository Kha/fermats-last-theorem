import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite

universe u v w

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (H : Type v) [CommRing H] [HopfAlgebra R H]
    (H' : Type w) [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing_of_moduleFinite.solution
