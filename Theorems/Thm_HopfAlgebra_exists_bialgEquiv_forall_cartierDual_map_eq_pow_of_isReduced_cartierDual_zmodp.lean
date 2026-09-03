import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
attribute [-instance] PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat
attribute [-simp] PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
    (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]
    (hred : IsReduced (CartierDual (ZMod p) A)) :
    ∃ V : A ≃ₐc[ZMod p] A, ∀ χ : CartierDual (ZMod p) A, CartierDual.map (V : A →ₐc[ZMod p] A) χ = χ ^ p := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp.solution
