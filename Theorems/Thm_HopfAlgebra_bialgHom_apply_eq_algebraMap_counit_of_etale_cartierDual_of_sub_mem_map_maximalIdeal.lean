import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal

universe u v w

theorem HopfAlgebra.bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    (H : Type v) [CommRing H] [Bialgebra R H] [Coalgebra.IsCocomm R H]
    [Module.Finite R H] [Module.Free R H]
    [Algebra.Etale R (CartierDual R H)]
    (H' : Type w) [CommRing H'] [Bialgebra R H'] [Coalgebra.IsCocomm R H']
    [Module.Finite R H'] [Module.Free R H']
    (φ : H' →ₐc[R] H)
    (hφ : ∀ a : H', φ a - algebraMap R H (Coalgebra.counit a) ∈
      (IsLocalRing.maximalIdeal R).map (algebraMap R H)) :
    ∀ a : H', φ a = algebraMap R H (Coalgebra.counit a) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bialgHom_apply_eq_algebraMap_counit_of_etale_cartierDual_of_sub_mem_map_maximalIdeal.solution
