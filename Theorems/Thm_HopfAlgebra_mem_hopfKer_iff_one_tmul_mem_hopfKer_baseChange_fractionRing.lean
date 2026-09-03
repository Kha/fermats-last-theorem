import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (x : H) :
    x ∈ HopfAlgebra.hopfKer qc ↔
      (1 : K) ⊗ₜ[R] x ∈ HopfAlgebra.hopfKer
        (Bialgebra.TensorProduct.map (BialgHom.id K K) qc : K ⊗[R] H →ₐc[K] K ⊗[R] H') := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_mem_hopfKer_iff_one_tmul_mem_hopfKer_baseChange_fractionRing.solution
