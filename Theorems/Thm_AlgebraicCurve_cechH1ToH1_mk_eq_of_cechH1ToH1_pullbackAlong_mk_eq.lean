import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq
    {K : Type*} {F F₁ : Type*} [Field K] [Field F] [Algebra K F] [Field F₁] [Algebra K F₁]
    (θ : F →ₐ[K] F₁) (hθ : θ.toRingHom.IsIntegral) (hbij : Function.Bijective θ)
    {S₀ S₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ)
    (a b : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F)))
    (h : cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk a)) =
      cechH1ToH1 (preimage_restrictAlong_union_eq_univ θ hθ hS) 0
        (cechH1.pullbackAlong θ hθ S₀ S₁ (Submodule.Quotient.mk b))) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk a) = cechH1ToH1 hS 0 (Submodule.Quotient.mk b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_of_cechH1ToH1_pullbackAlong_mk_eq.solution
