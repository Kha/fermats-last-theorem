import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_archIdent_tmul_apply

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NumberField.LiesOver

theorem AutomorphicForm.archIdent_tmul_apply
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (x : L) (a : InfiniteAdeleRing K) (w : InfinitePlace L) :
    letI : w.1.LiesOver (w.comap (algebraMap K L)).1 := ⟨rfl⟩
    archIdent K L (x ⊗ₜ a) w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion (a (w.comap (algebraMap K L))) *
        algebraMap L w.Completion x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_archIdent_tmul_apply.solution
