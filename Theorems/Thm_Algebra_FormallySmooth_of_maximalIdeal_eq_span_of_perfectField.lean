import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField.solution
