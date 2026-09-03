import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsMulLeftInvariant]
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (τ g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (m : (AdeleRing (𝓞 L) L)ˣ)
    (hg : g⁻¹ * τ * AutomorphicForm.sigmaAdelicAct K L D σ g = τ * AutomorphicForm.centralScalar (𝓞 L) L m) :
    ∫ z, ((ξ z : ℂˣ) : ℂ) *
        φ ((g * y)⁻¹ * τ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (g * y))) ∂ν =
      ((ξ (D.unitsAct σ⁻¹ m))⁻¹ : ℂˣ) *
        ∫ z, ((ξ z : ℂˣ) : ℂ) *
          φ (y⁻¹ * τ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂ν := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar.solution
