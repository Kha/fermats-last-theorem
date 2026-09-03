import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
attribute [-instance] NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

theorem AutomorphicForm.WindowedSiegel.exists_isCompact_cover_of_archHeight_le
    (F : Type) [Field F] [NumberField F] (c u T' : ℝ) (hc : 0 < c) :
    ∃ K : Set (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F),
      IsCompact K ∧
        ∀ x ∈ AutomorphicForm.WindowedSiegel.integralWindowedSiegelSet F c u,
          AutomorphicForm.WindowedSiegel.archHeight F
              (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F x) ≤ T' →
            ∃ γ : Matrix.GeneralLinearGroup (Fin 2) F,
              ∃ z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ,
                (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
                  AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * x *
                      AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z ∈ K := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le.solution
