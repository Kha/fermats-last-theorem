import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ ψ : H →ₐc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
        ((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M).restrictScalars R).comp
          Algebra.TensorProduct.includeRight := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing.solution
