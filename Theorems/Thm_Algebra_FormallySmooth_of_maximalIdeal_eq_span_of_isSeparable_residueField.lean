import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField

set_option autoImplicit false

universe u v

open IsLocalRing Polynomial

theorem Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField
    (K₀ : Type u) [Field K₀] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u})
    [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)] [Algebra.IsSeparable K₀ (ResidueField 𝒪)] :
    Algebra.FormallySmooth K₀ 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.solution
