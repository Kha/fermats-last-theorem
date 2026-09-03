import Mathlib
import Definitions.Def_Deformations_IsProartinian
import Theorems.Thm_IsArtinianRing_finite_of_finite_residueField
import P2M.Util
namespace P2MW.S_IsProartinian_finite_quotient_of_isOpen

universe u
open IsLocalRing

theorem solution {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsProartinian R] [Finite (IsLocalRing.ResidueField R)]
    (I : Ideal R) (hI : IsOpen (I : Set R)) :
    Finite (R ⧸ I) := by
  by_cases hI' : I = ⊤
  · have : Subsingleton (R ⧸ I) := Ideal.Quotient.subsingleton_iff.mpr hI'
    exact Finite.of_subsingleton
  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) := .of_surjective _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (ResidueField.map (Ideal.Quotient.mk I)) := by
    have hcomp : Function.Surjective
        (ResidueField.map (Ideal.Quotient.mk I) ∘ residue R) := by
      rw [show ResidueField.map (Ideal.Quotient.mk I) ∘ residue R
            = residue (R ⧸ I) ∘ Ideal.Quotient.mk I from
          funext fun r ↦ ResidueField.map_residue _ r]
      exact (residue_surjective).comp Ideal.Quotient.mk_surjective
    exact hcomp.of_comp
  have : Finite (ResidueField (R ⧸ I)) := .of_surjective _ hsurj
  exact IsArtinianRing.finite_of_finite_residueField (R ⧸ I)
