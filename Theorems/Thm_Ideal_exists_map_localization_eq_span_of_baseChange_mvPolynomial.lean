import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial

set_option autoImplicit false

universe u

theorem Ideal.exists_map_localization_eq_span_of_baseChange_mvPolynomial
    (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']
    (N M : ℕ) (J : Ideal (MvPolynomial (Fin N) k))
    (𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] (h𝔫 : J ≤ 𝔫)
    (𝔫' : Ideal (MvPolynomial (Fin N) k')) [𝔫'.IsMaximal]
    (hover : Ideal.map (MvPolynomial.map (algebraMap k k')) 𝔫 ≤ 𝔫')
    (hgen : ∃ g : Fin M → Localization.AtPrime 𝔫',
      Ideal.map (algebraMap (MvPolynomial (Fin N) k') (Localization.AtPrime 𝔫'))
          (Ideal.map (MvPolynomial.map (algebraMap k k')) J) = Ideal.span (Set.range g)) :
    ∃ g : Fin M → Localization.AtPrime 𝔫, Ideal.map (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫)) (J) = Ideal.span (Set.range g) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_map_localization_eq_span_of_baseChange_mvPolynomial.solution
