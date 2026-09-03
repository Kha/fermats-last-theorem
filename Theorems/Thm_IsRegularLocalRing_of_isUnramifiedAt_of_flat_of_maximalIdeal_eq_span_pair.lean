import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair
    {O O' : Type*} [CommRing O] [IsRegularLocalRing O] [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O']
    [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Flat O O'] [Algebra.EssFiniteType O O']
    [Algebra.IsUnramifiedAt O (maximalIdeal O')]
    (ϖ s : O) (hmax : maximalIdeal O = Ideal.span {ϖ, s}) (hdim : ringKrullDim O = 2)
    {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (π : O →+* D) (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {s}) :
    IsRegularLocalRing O' ∧ ringKrullDim O' = 2 ∧
      maximalIdeal O' = Ideal.span {algebraMap O O' ϖ, algebraMap O O' s} ∧
      (Ideal.span {algebraMap O O' s}).IsPrime ∧
      ∃ (_ : IsDomain (O' ⧸ Ideal.span {algebraMap O O' s})),
        IsDiscreteValuationRing (O' ⧸ Ideal.span {algebraMap O O' s}) := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_of_isUnramifiedAt_of_flat_of_maximalIdeal_eq_span_pair.solution
