import Mathlib
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_GaloisRep_ratLocalizedAt_exists_specMap_comp_eq_fromSpecResidueField

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

theorem GaloisRep.ratLocalizedAt.exists_specMap_comp_eq_fromSpecResidueField
    (ℓ : ℕ) [Fact ℓ.Prime] (s : Spec (CommRingCat.of ℤ)) (hs : s.asIdeal = Ideal.span {(ℓ : ℤ)}) :
    ∃ φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* (Spec (CommRingCat.of ℤ)).residueField s,
      Function.Surjective φ ∧ φ (ℓ : ↥(GaloisRep.ratLocalizedAt ℓ)) = 0 ∧
      Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))) =
        (Spec (CommRingCat.of ℤ)).fromSpecResidueField s := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_ratLocalizedAt_exists_specMap_comp_eq_fromSpecResidueField.solution
