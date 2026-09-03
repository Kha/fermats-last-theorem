import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (F : UpperHalfPlane → ℂ)
    (hFx : ∀ τ : UpperHalfPlane, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ x (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => (g : UpperHalfPlane → ℂ) (σ • τ) / (h : UpperHalfPlane → ℂ) (σ • τ))
        atImInfty (𝓝 L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.solution
