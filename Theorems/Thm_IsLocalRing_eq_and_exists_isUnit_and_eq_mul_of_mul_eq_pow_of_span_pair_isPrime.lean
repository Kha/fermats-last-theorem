import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
set_option autoImplicit false

theorem IsLocalRing.eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {p U V X Y w : R} {E E₀ : ℕ} (hE : 1 ≤ E) (hE₀ : 1 ≤ E₀) (hUV : U * V = p ^ E)
    (hP : (Ideal.span {p, U}).IsPrime) (hP' : (Ideal.span {p, V}).IsPrime)
    (hUP' : U ∉ Ideal.span {p, V}) (hVP : V ∉ Ideal.span {p, U})
    (hw : IsUnit w) (hXY : X * Y = p ^ E₀ * w)
    (hX : ∃ γ, IsUnit γ ∧ X - γ * U ∈ Ideal.span {p, V}) (hY : ∃ γ, IsUnit γ ∧ Y - γ * V ∈ Ideal.span {p, U}) :
    E₀ = E ∧ ∃ a b : R, IsUnit a ∧ IsUnit b ∧ X = U * a ∧ Y = V * b := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_eq_and_exists_isUnit_and_eq_mul_of_mul_eq_pow_of_span_pair_isPrime.solution
