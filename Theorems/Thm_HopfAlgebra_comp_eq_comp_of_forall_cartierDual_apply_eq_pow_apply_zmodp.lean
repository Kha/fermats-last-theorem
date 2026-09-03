import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import P2M.Util
import P2M.Sol.S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp

set_option autoImplicit false

theorem HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
    (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp.solution
