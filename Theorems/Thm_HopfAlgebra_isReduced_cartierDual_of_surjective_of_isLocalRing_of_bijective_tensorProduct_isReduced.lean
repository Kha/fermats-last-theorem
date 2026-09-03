import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced
    (p : ℕ) [Fact p.Prime]
    (C : Type) [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C]
    [Module.Finite (ZMod p) C] [Module.Free (ZMod p) C]
    (M : Type) [CommRing M] [HopfAlgebra (ZMod p) M] [Module.Finite (ZMod p) M] [Module.Free (ZMod p) M]
    (E : Type) [CommRing E] [HopfAlgebra (ZMod p) E]
    (Θ : C →ₐc[ZMod p] M ⊗[ZMod p] E) (hΘ : Function.Bijective Θ)
    (hE : IsReduced E) (hM : IsReduced (CartierDual (ZMod p) M))
    (L : Type) [CommRing L] [HopfAlgebra (ZMod p) L] [Coalgebra.IsCocomm (ZMod p) L]
    [Module.Finite (ZMod p) L] [Module.Free (ZMod p) L]
    (r : C →ₐc[ZMod p] L) (hr : Function.Surjective r) (hL : IsLocalRing L) :
    IsReduced (CartierDual (ZMod p) L) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isReduced_cartierDual_of_surjective_of_isLocalRing_of_bijective_tensorProduct_isReduced.solution
