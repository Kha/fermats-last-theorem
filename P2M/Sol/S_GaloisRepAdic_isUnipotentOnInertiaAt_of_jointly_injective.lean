import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import P2M.Util
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_jointly_injective

namespace LCMazur

private theorem polynomial_eq_of_map_eq_of_jointly_injective {P A B : Type} [CommRing P]
    [CommRing A] [CommRing B] (πA : P →+* A) (πB : P →+* B)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (f g : Polynomial P)
    (hA : f.map πA = g.map πA) (hB : f.map πB = g.map πB) : f = g :=
  Polynomial.ext fun n => sub_eq_zero.mp (hinj _
    (by rw [map_sub, ← Polynomial.coeff_map, ← Polynomial.coeff_map, hA, sub_self])
    (by rw [map_sub, ← Polynomial.coeff_map, ← Polynomial.coeff_map, hB, sub_self]))

end LCMazur

theorem solution {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {q : ℕ}
    (hA : (ρ.baseChangeAlong πA hπA).IsUnipotentOnInertiaAt q)
    (hB : (ρ.baseChangeAlong πB hπB).IsUnipotentOnInertiaAt q) :
    ρ.IsUnipotentOnInertiaAt q := by
  intro P' hP' σ hσ
  refine LCMazur.polynomial_eq_of_map_eq_of_jointly_injective πA πB hinj _ _ ?_ ?_
  · rw [← GaloisRepAdic.charpoly_baseChangeAlong πA hπA, hA P' hP' σ hσ, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  · rw [← GaloisRepAdic.charpoly_baseChangeAlong πB hπB, hB P' hP' σ hσ, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
