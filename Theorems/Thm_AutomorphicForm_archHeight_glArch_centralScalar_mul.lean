import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archHeight_glArch_centralScalar_mul

theorem AutomorphicForm.archHeight_glArch_centralScalar_mul (F : Type) [Field F] [NumberField F]
    (z : (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    AutomorphicForm.WindowedSiegel.archHeight F
        (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F
          (AutomorphicForm.centralScalar (NumberField.RingOfIntegers F) F z * g))
      = AutomorphicForm.WindowedSiegel.archHeight F
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archHeight_glArch_centralScalar_mul.solution
