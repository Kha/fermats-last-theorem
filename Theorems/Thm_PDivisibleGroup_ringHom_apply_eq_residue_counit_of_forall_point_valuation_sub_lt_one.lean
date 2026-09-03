import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one

set_option autoImplicit false

theorem PDivisibleGroup.ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one
    (p : ℕ) [Fact p.Prime]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    {t : ℕ} (𝒯 : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p t)
    (hred : ∀ (v : ℕ) (y : 𝒯.Point (AlgebraicClosure ℚ) v) (c : 𝒯.level v),
      Pl.valuation (PDivisibleGroup.Point.toAlgHom y c -
        algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)
          (Coalgebra.counit c)) < 1)
    (v : ℕ) (f : 𝒯.level v →+* IsLocalRing.ResidueField ↥Pl)
    (hf : f.comp (algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (𝒯.level v)) =
      (IsLocalRing.residue ↥Pl).comp
        ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
          Pl (fun r => r.2.1)))
    (c : 𝒯.level v) :
    f c = IsLocalRing.residue ↥Pl
      ((algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ)).codRestrict
        Pl (fun r => r.2.1) (Coalgebra.counit c)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_ringHom_apply_eq_residue_counit_of_forall_point_valuation_sub_lt_one.solution
