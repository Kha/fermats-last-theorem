import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions
attribute [-simp] HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul mem_flatClosure_iff

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

universe u v w

open scoped TensorProduct in

theorem CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A] :
    ∃ e : CartierDual S (S ⊗[R] A) ≃ₐc[S] S ⊗[R] CartierDual R A,
      ∀ (s t : S) (φ : CartierDual R A) (a : A),
        CartierDual.pairing S (S ⊗[R] A) (e.symm (s ⊗ₜ[R] φ)) (t ⊗ₜ[R] a) =
          s * t * algebraMap R S (CartierDual.pairing R A φ a) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_bialgEquiv_baseChange_forall_pairing_symm_tmul.solution
