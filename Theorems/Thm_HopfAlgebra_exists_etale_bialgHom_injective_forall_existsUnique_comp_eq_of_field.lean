import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
attribute [-instance] HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field
    (k : Type u) [Field k]
    (L : Type v) [CommRing L] [HopfAlgebra k L] [Coalgebra.IsCocomm k L] [Module.Finite k L] :
    ∃ (E : Type v) (_ : CommRing E) (_ : HopfAlgebra k E) (_ : Coalgebra.IsCocomm k E)
      (_ : Module.Finite k E) (ι : E →ₐc[k] L),
      Function.Injective ι ∧

      Algebra.Etale k E ∧

      (∀ (E' : Type v) [CommRing E'] [HopfAlgebra k E'] [Coalgebra.IsCocomm k E']
          [Module.Finite k E'] [Algebra.Etale k E']
          (f : E' →ₐc[k] L), ∃! g : E' →ₐc[k] E, ι.comp g = f) ∧

      (∀ (K : Type u) [Field K] [Algebra k K]
          (E' : Type v) [CommRing E'] [HopfAlgebra K E'] [Coalgebra.IsCocomm K E']
          [Module.Finite K E'] [Algebra.Etale K E']
          (f : E' →ₐc[K] K ⊗[k] L),
            ∃! g : E' →ₐc[K] K ⊗[k] E,
              (Bialgebra.TensorProduct.map (BialgHom.id K K) ι).comp g = f) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_field.solution
