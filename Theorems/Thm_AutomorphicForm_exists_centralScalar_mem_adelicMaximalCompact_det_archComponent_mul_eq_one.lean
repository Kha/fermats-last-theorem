import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_AdelicLsXi
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
attribute [-instance] NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (hreal : ∀ w : InfinitePlace F, w.IsReal →
      ((archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1) :
    ∃ z : (AdeleRing (𝓞 F) F)ˣ,
      centralScalar (𝓞 F) F z ∈ adelicMaximalCompact F ∧
      (∀ w : InfinitePlace F, w.IsReal →
        ((archComponent F w (glArch (𝓞 F) F (centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) ∧
      (∀ w : InfinitePlace F,
        ((archComponent F w (glArch (𝓞 F) F (k * centralScalar (𝓞 F) F z)) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det = 1) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_centralScalar_mem_adelicMaximalCompact_det_archComponent_mul_eq_one.solution
