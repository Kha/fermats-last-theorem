import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp
    (p : ℕ) [Fact p.Prime]
    (B : Type) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
    (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
    (qc : B →ₐc[ZMod p] Gc) (πe : B →ₐc[ZMod p] Ge) (Θ : B →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hqc : Function.Surjective qc) (hπe : Function.Surjective πe) (hΘ : Function.Bijective Θ)
    (hΘΔ : ∀ b, Θ b = Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (πe : B →ₐ[ZMod p] Ge) (Coalgebra.comul (R := ZMod p) b))

    (N : ℕ) (hkill : PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) Ge (p ^ N) =
      (Algebra.ofId (ZMod p) Ge).comp (Bialgebra.counitAlgHom (ZMod p) Ge))
    (hGe : IsReduced Ge)
    (κ : Type) [CommRing κ] [Algebra (ZMod p) κ] [IsReduced κ]
    (χ : CartierDual (ZMod p) B →ₐ[ZMod p] κ)
    (g₁ g₂ : B →ₐc[ZMod p] B)
    (hg : (qc : B →ₐ[ZMod p] Gc).comp (g₁ : B →ₐ[ZMod p] B) = (qc : B →ₐ[ZMod p] Gc).comp (g₂ : B →ₐ[ZMod p] B)) :
    χ.comp (CartierDual.map g₁ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) =
      χ.comp (CartierDual.map g₂ : CartierDual (ZMod p) B →ₐ[ZMod p] CartierDual (ZMod p) B) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_algHom_comp_map_eq_of_comp_eq_comp_of_bijective_tensorProduct_of_isReduced_of_nsmulAlgHom_pow_eq_zmodp.solution
