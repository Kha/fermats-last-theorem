import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ ψ' : H →ₐc[R] AddMonoidAlgebra R M)
    (h : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ' : H →ₐ[R] AddMonoidAlgebra R M)) :
    ψ = ψ' := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq.solution
