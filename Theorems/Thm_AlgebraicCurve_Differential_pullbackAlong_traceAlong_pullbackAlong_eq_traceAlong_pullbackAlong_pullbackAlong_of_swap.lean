import Mathlib
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap

set_option autoImplicit false

open AlgebraicCurve in

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (α β : F →ₐ[K] F') (hα : SeparableAlong K α) (hβ : SeparableAlong K β)
    (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hswapα : ∀ x : F, w' (α x) = β (w x)) (hswapβ : ∀ x : F, w' (β x) = α (w x))
    (ω : Ω[F⁄K]) :
    Differential.pullbackAlong w.toAlgHom (Differential.traceAlong α (Differential.pullbackAlong β ω)) =
      Differential.traceAlong β (Differential.pullbackAlong α (Differential.pullbackAlong w.toAlgHom ω)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap.solution
