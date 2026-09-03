import Mathlib
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_DrinfeldCurve_isDedekindDomain_coordRing
import Theorems.Thm_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
import P2M.Util
namespace P2MW.S_DrinfeldCurve_exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place

set_option autoImplicit false

open DrinfeldCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] [IsAlgClosed κ] [Algebra (GaloisField q 2) κ]
    [IsDomain (CoordRing q κ)] (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (z : drinfeldFunctionField q κ) (hzC : z ∈ DrinfeldCurve.quotField q κ C)
    (hz : ∀ v : AlgebraicCurve.Place κ (drinfeldFunctionField q κ),
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (x q κ) ∈ v.toValuationSubring →
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (y q κ) ∈ v.toValuationSubring →
      z ∈ v.toValuationSubring) :
    ∃ b : CoordRing q κ,
      (∀ ζ : ↥C, muAction q κ (ζ : rootsOfUnity (q + 1) (GaloisField q 2)) b = b) ∧
      algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) b = z := by
  classical
  haveI : IsDedekindDomain (CoordRing q κ) := DrinfeldCurve.isDedekindDomain_coordRing q κ

  have hzR : z ∈ (algebraMap (CoordRing q κ) (drinfeldFunctionField q κ)).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (drinfeldFunctionField q κ) z
    intro w
    have hX : algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (x q κ) ∈
        (AlgebraicCurve.Place.ofHeightOneSpectrum (K := κ) (F := drinfeldFunctionField q κ) w).toValuationSubring := by
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one _
    have hY : algebraMap (CoordRing q κ) (drinfeldFunctionField q κ) (y q κ) ∈
        (AlgebraicCurve.Place.ofHeightOneSpectrum (K := κ) (F := drinfeldFunctionField q κ) w).toValuationSubring := by
      rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one _
    have hmem := hz _ hX hY
    rw [AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff] at hmem
    exact hmem
  obtain ⟨b, hb⟩ := hzR
  refine ⟨b, ?_, hb⟩

  have hiff := (DrinfeldCurve.algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField q κ C).1 b
  rw [hb] at hiff
  exact hiff.mp hzC
