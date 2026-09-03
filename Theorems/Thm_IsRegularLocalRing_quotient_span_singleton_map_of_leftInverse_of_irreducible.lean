import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible

set_option autoImplicit false

open IsLocalRing

theorem IsRegularLocalRing.quotient_span_singleton_map_of_leftInverse_of_irreducible
    {R A : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (i : A →+* R) (s : R →+* A) (hs : Function.Surjective s) (hsi : s.comp i = RingHom.id A)
    {ϖ : A} (hϖ : Irreducible ϖ) :
    ∃ _ : IsRegularLocalRing (R ⧸ Ideal.span {i ϖ}),
      (maximalIdeal (R ⧸ Ideal.span {i ϖ})).spanFinrank + 1 = (maximalIdeal R).spanFinrank ∧
        ringKrullDim (R ⧸ Ideal.span {i ϖ}) + 1 = ringKrullDim R := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible.solution
