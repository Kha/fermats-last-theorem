import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_GroupCohomology_GaloisSUnits
import Definitions.Def_NumberField_SUnitsMax
import P2M.Util
import P2M.Sol.S_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
attribute [-instance] groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup

set_option autoImplicit false
open CategoryTheory Module groupCohomology NumberField.LevelArith

theorem groupCohomology.bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    (φ : sUnitsMaxRep S L →ₗ[ℤ] Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
    (hφv : ∀ x : sUnitsMaxRep S L,
      ((Additive.toMul (φ x) : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = sUnitsMaxRep.val S L x)
    (hφ : ∀ (g : ↥L.fixingSubgroup) (a : sUnitsMaxRep S L),
      φ ((sUnitsMaxRep S L).ρ g a) = (Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S)).ρ g (φ a)) :
    Function.Bijective
      (continuousH2SrMap (rH := L.fixingSubgroup.subtype) (rG := L.fixingSubgroup.subtype)
        (A := sUnitsMaxRep S L) (B := Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
        (MonoidHom.id ↥L.fixingSubgroup) (fun _ => rfl) S φ hφ) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep.solution
