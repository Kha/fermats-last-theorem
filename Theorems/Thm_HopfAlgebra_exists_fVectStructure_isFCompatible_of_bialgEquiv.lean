import Definitions.Def_HopfAlgebra_FVectStructure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_fVectStructure_isFCompatible_of_bialgEquiv

universe u v w x
theorem HopfAlgebra.exists_fVectStructure_isFCompatible_of_bialgEquiv
    {F : Type w} [Field F] {R : Type u} [CommRing R]
    {H : Type v} [CommRing H] [Bialgebra R H] {H' : Type x} [CommRing H'] [Bialgebra R H']
    (σ : HopfAlgebra.FVectStructure F R H) (e : H ≃ₐc[R] H') :
    ∃ σ' : HopfAlgebra.FVectStructure F R H',
      (∀ a : F, σ'.act a = (e : H →ₐc[R] H').comp ((σ.act a).comp (e.symm : H' →ₐc[R] H))) ∧
      HopfAlgebra.IsFCompatible σ σ' (e : H →ₐc[R] H') := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_fVectStructure_isFCompatible_of_bialgEquiv.solution
