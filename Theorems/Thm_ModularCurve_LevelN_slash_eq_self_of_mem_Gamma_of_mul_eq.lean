import Mathlib
import Definitions.Def_ModularCurve_LevelNFunctionField
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem ModularCurve.LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
    (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
    (he : e ∈ ModularCurve.LevelN.ring N) (hb0 : b ≠ 0) (he0 : e ≠ 0)
    (h : ∀ τ : UpperHalfPlane, F τ * b τ * e τ ^ 2 =
      a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
        c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    F ∣[(2 : ℤ)] γ = F := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.solution
