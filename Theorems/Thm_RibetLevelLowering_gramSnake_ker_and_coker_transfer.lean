import Mathlib
import P2M.Util
import P2M.Sol.S_RibetLevelLowering_gramSnake_ker_and_coker_transfer

set_option autoImplicit false

theorem RibetLevelLowering.gramSnake_ker_and_coker_transfer
    {R : Type*} [CommRing R]
    {Y L X Yd Ld Xd : Type*}
    [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L] [AddCommGroup X] [Module R X]
    [AddCommGroup Yd] [Module R Yd] [AddCommGroup Ld] [Module R Ld] [AddCommGroup Xd] [Module R Xd]
    (ι : Y →ₗ[R] L) (δ : L →ₗ[R] X) (hδι : ∀ y : Y, δ (ι y) = 0)
    (σ : X →ₗ[R] L) (η : R) (hσ : ∀ x : X, δ (σ x) = η • x)
    (κd : Xd →ₗ[R] Ld) (ρd : Ld →ₗ[R] Yd) (hρd : Function.Surjective ρd)
    (hdc : ∀ φ : Xd, ρd (κd φ) = 0) (hexd : ∀ l : Ld, ρd l = 0 → ∃ φ : Xd, κd φ = l)
    (gL : L →ₗ[R] Ld) (hgL : Function.Injective gL) (gX : X →ₗ[R] Xd) (gY : Y →ₗ[R] Yd)
    (hsq : ∀ x : X, gL (σ x) = κd (gX x))
    (hres : ∀ y : Y, gY y = ρd (gL (ι y))) :
    let Θ : L →ₗ[R] (Yd ⧸ LinearMap.range gY) := (LinearMap.range gY).mkQ ∘ₗ ρd ∘ₗ gL
    (∀ y : Y, Θ (ι y) = 0) ∧
    (∀ x : X, Θ (σ x) = 0) ∧
    (∀ u : R, (∀ φ : Xd, ∃ x : X, u • φ = gX x) →
        ∀ l : L, Θ l = 0 → ∃ x₁ : X, u • δ l = η • x₁) ∧
    (∀ u : R, (∀ m : Ld, ∃ l : L, u • m = gL l) →
        ∀ ψ : Yd ⧸ LinearMap.range gY, ∃ l : L, u • ψ = Θ l) := by p2m_exact_reverting @_root_.P2MW.S_RibetLevelLowering_gramSnake_ker_and_coker_transfer.solution
