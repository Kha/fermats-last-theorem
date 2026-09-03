import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import Theorems.Thm_TwoChartCech_exists_fibreH0Family
import Theorems.Thm_CoherentBaseChange_FibreH0Family_isClosed_setOf_le_h0
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
namespace P2MW.S_TwoChartCech_isClosed_setOf_le_finrank_ker_baseChange

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (n : ℕ) :
    IsClosed {x : T | n ≤ Module.finrank (f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))} := by
  obtain ⟨F, hF⟩ := TwoChartCech.exists_fibreH0Family d f
  have : {x : T | n ≤ Module.finrank (f.base x).asIdeal.ResidueField
      (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))} = {x : T | n ≤ F.h0 x} := by
    ext x; simp only [Set.mem_setOf_eq, hF x]
  rw [this]
  exact F.isClosed_setOf_le_h0 n
