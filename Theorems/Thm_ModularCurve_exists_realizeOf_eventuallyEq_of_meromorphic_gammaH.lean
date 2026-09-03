import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (F : UpperHalfPlane → ℂ)
    (hmer : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO UpperHalfPlane.atImInfty (fun τ : UpperHalfPlane => F (σ • τ))
        fun τ : UpperHalfPlane => Real.exp (C * τ.im)) :
    ∃ x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H),
      ∀ τ : UpperHalfPlane, (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) x (UpperHalfPlane.ofComplex z) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH.solution
