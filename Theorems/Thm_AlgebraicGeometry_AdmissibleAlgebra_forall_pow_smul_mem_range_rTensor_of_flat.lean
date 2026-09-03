import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat

set_option autoImplicit false

open TensorProduct

universe u v w

theorem AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
    {B : Type u} [CommRing B] {M N P : Type v} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (f : M →ₗ[B] N) (g : N →ₗ[B] P) (hfg : g.comp f = 0) (t : B) (e : ℕ)
    (h : ∀ n : N, g n = 0 → (∃ k : ℕ, t ^ k • n ∈ LinearMap.range f) → t ^ e • n ∈ LinearMap.range f)
    (S : Type v) [AddCommGroup S] [Module B S] [Module.Flat B S]
    (n : N ⊗[B] S) (hn : LinearMap.rTensor S g n = 0) (hk : ∃ k : ℕ, t ^ k • n ∈ LinearMap.range (LinearMap.rTensor S f)) :
    t ^ e • n ∈ LinearMap.range (LinearMap.rTensor S f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat.solution
