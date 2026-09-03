import Mathlib
import Theorems.Thm_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
import Theorems.Thm_Algebra_isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
import P2M.Util
namespace P2MW.S_Algebra_isUnramifiedAt_of_forall_le_height_eq_one_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ P → Q.height = 1 → Algebra.IsUnramifiedAt A Q) :
    Algebra.IsUnramifiedAt A P := by
  by_contra hP
  have hDP : ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ P := by
    by_contra hnle
    exact hP ((Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
      A K B L P).mpr hnle)
  obtain ⟨Q, hQ, hQP, hQ1, hDQ⟩ :=
    Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed A K B L P hDP
  haveI := hQ
  have hunr : Algebra.IsUnramifiedAt A Q := h Q hQP hQ1
  exact ((Algebra.isUnramifiedAt_iff_not_le_comap_one_div_traceDual_of_free_of_isIntegrallyClosed
    A K B L Q).mp hunr) hDQ

#print axioms solution
