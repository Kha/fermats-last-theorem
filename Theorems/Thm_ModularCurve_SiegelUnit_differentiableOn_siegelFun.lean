import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import P2M.Util
import P2M.Sol.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun

set_option autoImplicit false

open ModularCurve
open scoped Manifold in

theorem ModularCurve.SiegelUnit.differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.solution
