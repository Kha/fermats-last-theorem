import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections

namespace AlgebraicCurve

theorem cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {S₀ S₁ T₀ T₁ : Set (Place K F)} (hS : S₀ ∪ S₁ = Set.univ) (hT : T₀ ∪ T₁ = Set.univ)
    (f : ↥(lSpaceOn (S₀ ∩ S₁) (0 : Divisor K F))) (f' : ↥(lSpaceOn (T₀ ∩ T₁) (0 : Divisor K F)))
    (g₀₀ g₀₁ g₁₀ g₁₁ : F)
    (h₀₀ : g₀₀ ∈ lSpaceOn (S₀ ∩ T₀) (0 : Divisor K F)) (h₀₁ : g₀₁ ∈ lSpaceOn (S₀ ∩ T₁) (0 : Divisor K F))
    (h₁₀ : g₁₀ ∈ lSpaceOn (S₁ ∩ T₀) (0 : Divisor K F)) (h₁₁ : g₁₁ ∈ lSpaceOn (S₁ ∩ T₁) (0 : Divisor K F))
    (e₀ : g₀₀ = g₁₀ + (f : F)) (e₁ : g₀₁ = g₁₁ + (f : F)) (e₀' : g₀₁ = g₀₀ + (f' : F)) :
    cechH1ToH1 hS 0 (Submodule.Quotient.mk f) = cechH1ToH1 hT 0 (Submodule.Quotient.mk f') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_cechH1ToH1_mk_eq_cechH1ToH1_mk_of_crossSections.solution
end AlgebraicCurve
