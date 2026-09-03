import Mathlib
import Definitions.Def_ModularCurve_AbelFibreSumOf
import P2M.Util
import P2M.Sol.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hnc : ∀ (t : ℂ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≠ ⊤)
    (t₀ : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t₀ ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∀ᶠ t in 𝓝 t₀,
      ModularCurve.abelFibreSumOf Γ F t - ModularCurve.abelFibreSumOf Γ F t₀ ∈
        ModularCurve.periodLatticeOf Γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eventually_abelFibreSumOf_sub_mem_periodLatticeOf.solution
