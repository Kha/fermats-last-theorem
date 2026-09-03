import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfiniteAdeleRing_measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top
attribute [-instance] FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension
attribute [-simp] M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.InfiniteAdeleRing.measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ν : Measure (InfiniteAdeleRing K)ˣ) [ν.IsHaarMeasure]
    (R : ℝ) (hR : 1 < R) (c : InfinitePlace K → ℝ) (hc : ∀ v, 0 < c v) :
    ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        c v ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R * c v} =
      ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} ∧
    0 < ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} ∧
    ν {p : (InfiniteAdeleRing K)ˣ | ∀ v : InfinitePlace K,
        1 ≤ ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ∧
          ‖((p : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v‖ ≤ R} < ⊤ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfiniteAdeleRing_measure_setOf_forall_le_norm_apply_le_mul_eq_and_pos_and_lt_top.solution
