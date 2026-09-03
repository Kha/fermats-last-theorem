import Definitions.Def_ModularCurve_SpecializeModuli
import P2M.Util
namespace P2MW.S_ModularCurve_algebraMap_residueField_charLGeomPlaceOfPoint_surjective

open AlgebraicCurve ModularCurve

theorem solution
    (K : Type*) [Field K] (a : K) :
    Function.Surjective (algebraMap K (ModularCurve.charLGeomPlaceOfPoint K a).ResidueField) := by

  have key : ∀ v : Place K (modularFunctionFieldC K 1), v.deg = 1 →
      Function.Surjective (algebraMap K v.ResidueField) := by
    intro v hv x
    haveI : Module.Free K v.ResidueField := Module.Free.of_divisionRing K v.ResidueField
    have hbt : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hv
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := hbt ▸ Algebra.mem_top
    exact Algebra.mem_bot.mp hx
  exact key _ (ModularCurve.deg_charLGeomPlaceOfPoint K a)
