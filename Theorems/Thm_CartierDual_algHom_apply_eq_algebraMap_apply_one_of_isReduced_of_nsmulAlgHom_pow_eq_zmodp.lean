import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_CartierDual_algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
    (p : ℕ) [Fact p.Prime]
    (E : Type) [CommRing E] [HopfAlgebra (ZMod p) E] [Coalgebra.IsCocomm (ZMod p) E] [Module.Finite (ZMod p) E]

    (N : ℕ) (hkill : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) E (p ^ N) =
      (Algebra.ofId (ZMod p) E).comp (Bialgebra.counitAlgHom (ZMod p) E))
    (hE : IsReduced E)
    (κ : Type) [CommRing κ] [Algebra (ZMod p) κ] [IsReduced κ]
    (χ : CartierDual (ZMod p) E →ₐ[ZMod p] κ) (φ : CartierDual (ZMod p) E) :
    χ φ = algebraMap (ZMod p) κ (φ 1) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_algHom_apply_eq_algebraMap_apply_one_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp.solution
