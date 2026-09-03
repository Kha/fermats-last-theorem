import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_subst_eq_X_and_span_subst_varpi_eq_of_not_and
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_subst_eq_X_and_span_subst_varpi_eq_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))) :
    ∃ α β : Fin 2 → MvPowerSeries (Fin 2) k,
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) ∧ (∀ i, MvPowerSeries.constantCoeff (β i) = 0) ∧
      (∀ i, MvPowerSeries.subst α (β i) = MvPowerSeries.X i) ∧
      (∀ i, MvPowerSeries.subst β (α i) = MvPowerSeries.X i) ∧
      Ideal.span (Set.range fun i => MvPowerSeries.subst α (X₀.varpi i)) =
        Ideal.span ({MvPowerSeries.X 1, MvPowerSeries.X 0 ^ (q ^ 2)} : Set (MvPowerSeries (Fin 2) k)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_subst_eq_X_and_span_subst_varpi_eq_of_not_and.solution
