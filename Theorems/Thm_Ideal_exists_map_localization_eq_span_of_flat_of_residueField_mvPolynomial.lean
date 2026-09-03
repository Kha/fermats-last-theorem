import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial

set_option autoImplicit false

universe u v

theorem Ideal.exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (N : ℕ) (J : Ideal (MvPolynomial (Fin N) R))
    [Module.Finite R (MvPolynomial (Fin N) R ⧸ J)] [Module.Flat R (MvPolynomial (Fin N) R ⧸ J)]
    (hfib : ∀ (𝔫 : Ideal (MvPolynomial (Fin N) (IsLocalRing.ResidueField R))) [𝔫.IsMaximal],
      Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J ≤ 𝔫 →
      ∃ g : Fin N → MvPolynomial (Fin N) (IsLocalRing.ResidueField R),
        (∀ i, g i ∈ Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J) ∧
        Ideal.map (algebraMap _ (Localization.AtPrime 𝔫)) (Ideal.map (MvPolynomial.map (IsLocalRing.residue R)) J) =
          Ideal.span (Set.range fun i => algebraMap _ (Localization.AtPrime 𝔫) (g i)))
    (𝔫 : Ideal (MvPolynomial (Fin N) R)) [𝔫.IsMaximal] (h𝔫 : J ≤ 𝔫) :
    ∃ g : Fin N → MvPolynomial (Fin N) R, (∀ i, g i ∈ J) ∧
      Ideal.map (algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫)) J =
        Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin N) R) (Localization.AtPrime 𝔫) (g i)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_map_localization_eq_span_of_flat_of_residueField_mvPolynomial.solution
