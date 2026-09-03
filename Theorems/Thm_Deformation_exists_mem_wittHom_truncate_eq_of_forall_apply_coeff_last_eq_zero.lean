import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import P2M.Util
import P2M.Sol.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

universe u v

theorem Deformation.exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (m : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (x : TruncatedWittVector p (m + 1) A) (hx : x ∈ Deformation.wittHom k p (m + 1) A)
    (hlast : ∀ β : WithConv (A →ₗ[k] k), β ^ p = 0 → β.ofConv (x.coeff (Fin.last m)) = 0) :
    ∃ y : TruncatedWittVector p (m + 2) A,
      y ∈ Deformation.wittHom k p (m + 2) A ∧
        TruncatedWittVector.truncate (Nat.le_succ (m + 1)) y = x := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_mem_wittHom_truncate_eq_of_forall_apply_coeff_last_eq_zero.solution
