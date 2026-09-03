import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import P2M.Util
import P2M.Sol.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem MvFormalGroup.cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    {d : ℕ} (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hε : ∀ j, Coalgebra.counit (R := ZMod p) ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = 0)
    (δ δ' : CartierDual (ZMod p) (ZMod p ⊗[𝓞] R))
    (hδ : ∀ a b : ZMod p ⊗[𝓞] R, δ (a * b) =
      δ a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ b)
    (hδ' : ∀ a b : ZMod p ⊗[𝓞] R, δ' (a * b) =
      δ' a * Coalgebra.counit (R := ZMod p) b + Coalgebra.counit (R := ZMod p) a * δ' b)
    (h : ∀ j, δ ((1 : ZMod p) ⊗ₜ[𝓞] π (X j)) = δ' ((1 : ZMod p) ⊗ₜ[𝓞] π (X j))) :
    δ = δ' := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_cartierDual_eq_of_forall_apply_tmul_eq_of_map_mul.solution
