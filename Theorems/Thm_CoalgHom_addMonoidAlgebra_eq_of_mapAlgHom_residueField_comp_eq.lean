import Mathlib
import P2M.Util
import P2M.Sol.S_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]
    (M : Type w) [AddCommGroup M] [Finite M]
    (f f' : B →ₗc[R] AddMonoidAlgebra R M)
    (h : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f.toLinearMap =
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f'.toLinearMap) :
    f = f' := by p2m_exact_reverting @_root_.P2MW.S_CoalgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq.solution
