import Mathlib
import Theorems.Thm_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
import P2M.Util
namespace P2MW.S_IsArtinianRing_exists_isArtinianRing_faithfullyFlat_map_maximalIdeal_eq_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing

theorem solution
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    ∃ (D : Type) (_ : CommRing D) (_ : IsLocalRing D) (_ : IsArtinianRing D) (_ : Algebra C D),
      Module.FaithfullyFlat C D ∧ IsLocalHom (algebraMap C D) ∧
      Ideal.map (algebraMap C D) (maximalIdeal C) = maximalIdeal D ∧
      IsAlgClosed (ResidueField D) := by
  classical

  obtain ⟨B, iB, iLB, iNB, iAlg, iLoc, hFF, hmap, ⟨e⟩⟩ :=
    IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
      C (AlgebraicClosure (ResidueField C))
  letI : CommRing B := iB
  haveI : IsLocalRing B := iLB
  haveI : IsNoetherianRing B := iNB
  letI : Algebra C B := iAlg
  haveI : IsLocalHom (algebraMap C B) := iLoc

  have hnilC : IsNilpotent (maximalIdeal C) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hnilB : IsNilpotent (maximalIdeal B) := by
    obtain ⟨n, hn⟩ := hnilC
    refine ⟨n, ?_⟩
    rw [← hmap, ← Ideal.map_pow, hn]
    simp
  haveI : IsArtinianRing B := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mpr hnilB
  haveI : IsAlgClosed (ResidueField B) :=
    IsAlgClosed.of_ringEquiv (AlgebraicClosure (ResidueField C)) (ResidueField B) e.symm.toRingEquiv
  exact ⟨B, iB, iLB, inferInstance, iAlg, hFF, iLoc, hmap, inferInstance⟩
