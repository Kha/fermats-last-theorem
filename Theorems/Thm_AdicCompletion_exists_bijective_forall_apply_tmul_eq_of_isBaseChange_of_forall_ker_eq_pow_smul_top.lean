import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem AdicCompletion.exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top
    {B₀ : Type u} [CommRing B₀] {B : Type u} [CommRing B] [Algebra B₀ B] [IsNoetherianRing B]
    (I₀ : Ideal B₀) (hI₀ : I₀.FG)
    (M₀ : ℕ → Type v) [∀ n, AddCommGroup (M₀ n)] [∀ n, Module B₀ (M₀ n)]
    (t₀ : ∀ n : ℕ, M₀ (n + 1) →ₗ[B₀] M₀ n)
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module B (M n)] [∀ n, Module B₀ (M n)]
    [∀ n, IsScalarTower B₀ B (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[B] M n)
    (κ : ∀ n : ℕ, M₀ n →ₗ[B₀] M n) (hκ : ∀ n : ℕ, IsBaseChange B (κ n))
    (hκt : ∀ (n : ℕ) (x : M₀ (n + 1)), t n (κ (n + 1) x) = κ n (t₀ n x))

    (L₀ : Type v) [AddCommGroup L₀] [Module B₀ L₀] [Module (AdicCompletion I₀ B₀) L₀]
    [IsScalarTower B₀ (AdicCompletion I₀ B₀) L₀] [Module.Finite (AdicCompletion I₀ B₀) L₀]
    (pr₀ : ∀ n : ℕ, L₀ →ₗ[B₀] M₀ n)
    (hpr₀c : ∀ (n : ℕ) (x : L₀), t₀ n (pr₀ (n + 1) x) = pr₀ n x)
    (hpr₀i : ∀ x : L₀, (∀ n : ℕ, pr₀ n x = 0) → x = 0)
    (hpr₀t : ∀ m : ∀ n : ℕ, M₀ n, (∀ n : ℕ, t₀ n (m (n + 1)) = m n) → ∃ x : L₀, ∀ n : ℕ, pr₀ n x = m n)
    (hpr₀s : ∀ n : ℕ, Function.Surjective (pr₀ n))
    (hpr₀k : ∀ n : ℕ, LinearMap.ker (pr₀ n) = I₀ ^ (n + 1) • (⊤ : Submodule B₀ L₀))

    (L : Type v) [AddCommGroup L] [Module B L] [Module (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    [IsScalarTower B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    [Module.Finite (AdicCompletion (I₀.map (algebraMap B₀ B)) B) L]
    (pr : ∀ n : ℕ, L →ₗ[B] M n)
    (hprc : ∀ (n : ℕ) (x : L), t n (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprt : ∀ m : ∀ n : ℕ, M n, (∀ n : ℕ, t n (m (n + 1)) = m n) → ∃ x : L, ∀ n : ℕ, pr n x = m n)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I₀.map (algebraMap B₀ B)) ^ (n + 1) • (⊤ : Submodule B L))

    (f : AdicCompletion I₀ B₀ →+* AdicCompletion (I₀.map (algebraMap B₀ B)) B)
    (hf : ∀ b : B₀, f (algebraMap B₀ (AdicCompletion I₀ B₀) b)
      = algebraMap B (AdicCompletion (I₀.map (algebraMap B₀ B)) B) (algebraMap B₀ B b)) :
    letI := f.toAlgebra
    ∃ e : AdicCompletion (I₀.map (algebraMap B₀ B)) B ⊗[AdicCompletion I₀ B₀] L₀
        →ₗ[AdicCompletion (I₀.map (algebraMap B₀ B)) B] L,
      Function.Bijective e ∧
      ∀ (n : ℕ) (x₀ : L₀), pr n (e ((1 : AdicCompletion (I₀.map (algebraMap B₀ B)) B) ⊗ₜ x₀)) = κ n (pr₀ n x₀) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_bijective_forall_apply_tmul_eq_of_isBaseChange_of_forall_ker_eq_pow_smul_top.solution
