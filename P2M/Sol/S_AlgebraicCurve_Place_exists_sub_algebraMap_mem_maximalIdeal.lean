import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F]
    [Algebra K F] (u : AlgebraicCurve.Place K F) (hdeg : u.deg = 1) (b : u.toValuationSubring) :
    ∃ c : K, b - algebraMap K u.toValuationSubring c
      ∈ IsLocalRing.maximalIdeal u.toValuationSubring := by
  obtain ⟨c, hc⟩ := ((Place.deg_eq_one_iff_surjective_algebraMap_residueField u).mp hdeg)
    (IsLocalRing.residue _ b)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero,
    IsScalarTower.algebraMap_apply K u.toValuationSubring u.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

#print axioms solution
