import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top

set_option autoImplicit false
theorem MonoidAlgebra.quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] {G : Type} [CommGroup G] [Fintype G]
    (ι : MonoidAlgebra 𝒪 G →ₐ[𝒪] A) (Mn : Type) [AddCommGroup Mn] [Module A Mn]
    [Module (MonoidAlgebra 𝒪 G) Mn] [Module 𝒪 Mn] [IsScalarTower 𝒪 (MonoidAlgebra 𝒪 G) Mn]
    (hι : ∀ (c : MonoidAlgebra 𝒪 G) (x : Mn), c • x = ι c • x) (x : Mn) :
    (Submodule.Quotient.mk x :
        Mn ⧸ (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) •
          (⊤ : Submodule (MonoidAlgebra 𝒪 G) Mn))) = 0 ↔
      x ∈ (Ideal.map ι (RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)))) • (⊤ : Submodule A Mn) := by p2m_exact_reverting @_root_.P2MW.S_MonoidAlgebra_quotient_mk_eq_zero_iff_mem_map_augmentation_smul_top.solution
