import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField

set_option autoImplicit false

universe u

theorem Algebra.exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField
    (k : Type u) [Field k] (C : Type u) [CommRing C] [Algebra k C] [IsLocalRing C]
    (hres : Function.Surjective (algebraMap k (IsLocalRing.ResidueField C)))
    [Module.Finite k C]
    (hsq : ∃ (r : ℕ) (g : Fin r → MvPolynomial (Fin r) k),
      Nonempty (C ≃ₐ[k] (MvPolynomial (Fin r) k ⧸ Ideal.span (Set.range g))))
    (N : ℕ) (ψ : MvPolynomial (Fin N) k →ₐ[k] C) (hψ : Function.Surjective ψ)
    (𝔫 : Ideal (MvPolynomial (Fin N) k)) [𝔫.IsMaximal] (h𝔫 : RingHom.ker ψ ≤ 𝔫) :
    ∃ g : Fin N → Localization.AtPrime 𝔫, Ideal.map (algebraMap (MvPolynomial (Fin N) k) (Localization.AtPrime 𝔫)) (RingHom.ker ψ) = Ideal.span (Set.range g) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_ker_map_localization_eq_span_of_surjective_of_exists_square_presentation_of_surjective_algebraMap_residueField.solution
