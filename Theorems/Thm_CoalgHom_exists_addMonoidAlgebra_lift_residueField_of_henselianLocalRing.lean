import Mathlib
import P2M.Util
import P2M.Sol.S_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] [Coalgebra.IsCocomm R B]
    (M : Type w) [AddCommGroup M] [Finite M]
    (f₀ : ResidueField R ⊗[R] B →ₗc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ f : B →ₗc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).toLinearMap ∘ₗ f.toLinearMap =
        (f₀.toLinearMap.restrictScalars R) ∘ₗ
          (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R) (B := B)).toLinearMap := by p2m_exact_reverting @_root_.P2MW.S_CoalgHom_exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing.solution
