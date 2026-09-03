import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank

set_option autoImplicit false

open scoped TensorProduct

theorem TensorProduct.exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (K : Type*) [Field K] [Algebra (ZMod p) K]
    {W : Type*} [AddCommGroup W] [Module K W] [Module (ZMod p) W] [IsScalarTower (ZMod p) K W]
    (Θ : V →ₗ[ZMod p] W)
    (hcard : Nat.card V = p ^ Module.finrank K (Submodule.span K (Set.range Θ))) :
    ∃ e : K ⊗[ZMod p] V ≃ₗ[K] Submodule.span K (Set.range Θ),
      ∀ (c : K) (v : V), (e (c ⊗ₜ[ZMod p] v) : W) = c • Θ v := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_exists_linearEquiv_span_range_apply_tmul_of_natCard_eq_pow_finrank.solution
