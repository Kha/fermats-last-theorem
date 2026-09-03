import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual

theorem HopfAlgebra.finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual
    (k : Type) [Field k] (B : Type) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
    [Module.Finite k B] {ι : Type} (ψ : ι → (B →ₐc[k] B))
    (hI : ∀ i, RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)) ≤
      (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B))).comap
        (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B)) :
    Module.finrank k (↥(primitives k B) ⧸
        ⨆ i, ((primitives k B).map (ψ i).toLinearMap).comap (primitives k B).subtype)
      = Module.finrank k ↥(⨅ i, LinearMap.ker
          (Ideal.mapCotangent (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k B)))
            (CartierDual.map (ψ i) : CartierDual k B →ₐ[k] CartierDual k B) (hI i))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_primitives_quot_iSup_map_eq_finrank_iInf_ker_mapCotangent_cartierDual.solution
