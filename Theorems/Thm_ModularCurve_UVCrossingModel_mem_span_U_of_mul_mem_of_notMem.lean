import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.mem_span_U_of_mul_mem_of_notMem
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (m : ℕ) (hm : 1 ≤ m)
    (s f : UVCrossingModel W (ϖ ^ m))
    (hs : s ∉ Ideal.span {const (ϖ ^ m) ϖ, U (ϖ ^ m)})
    (h : s * f ∈ Ideal.span {U (ϖ ^ m)}) :
    f ∈ Ideal.span {U (ϖ ^ m)} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_mem_span_U_of_mul_mem_of_notMem.solution
