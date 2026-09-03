import Definitions.Def_ModularCurve_ComponentGroupOrder
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import P2M.Util
namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_natAbs_det

open ModularCurve Module

theorem solution {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}
    (he : ∀ x, 0 < e x) (c : Basis κ ℤ (characterLattice ι)) :
    Nat.card (componentGroup e) = ((gramMatrixOf e ⇑c).det).natAbs := by
  haveI : Module.Free ℤ (Module.Dual ℤ (characterLattice ι)) :=
    Module.Free.of_basis c.dualBasis
  haveI : Module.Finite ℤ (Module.Dual ℤ (characterLattice ι)) :=
    Module.Finite.of_basis c.dualBasis
  have h := (Submodule.natAbs_det_basis_change c.dualBasis
    (LinearMap.range (gramMap e)) (gramRangeBasisOf he c)).symm
  refine h.trans ?_
  rw [Basis.det_apply, toMatrix_dualBasis_gramRangeOf he c, Matrix.det_transpose]
