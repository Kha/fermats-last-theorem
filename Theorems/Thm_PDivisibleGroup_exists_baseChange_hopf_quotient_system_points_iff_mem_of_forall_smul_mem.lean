import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option Elab.async false

open scoped TensorProduct

theorem PDivisibleGroup.exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K'] [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
    [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)] :
    ∃ (C : ℕ → Type) (_ : ∀ v, CommRing (C v)) (_ : ∀ v, HopfAlgebra K' (C v))
      (πK : ∀ v, K' ⊗[PadicAlgCl.ringOfIntegers p K] G.level v →ₐc[K'] C v),
      (∀ v, Function.Surjective (πK v)) ∧
      (∀ (v : ℕ) (a : G.level (v + 1)),
        πK (v + 1) ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a) = 0 →
          πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] G.transition v a) = 0) ∧
      (∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g'' : C v →ₐ[K'] PadicAlgCl p, ∀ a : G.level v,
            g'' (πK v ((1 : K') ⊗ₜ[PadicAlgCl.ringOfIntegers p K] a)) = PDivisibleGroup.Point.toAlgHom g a) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem.solution
