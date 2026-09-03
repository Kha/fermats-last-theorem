import Mathlib
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_eq_of_forall_finiteAdeleEvalAt_eq

open scoped TensorProduct
open IsDedekindDomain NumberField

theorem Submodule.eq_of_forall_finiteAdeleEvalAt_eq
    {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D]
    (x y : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt D v x = Submodule.finiteAdeleEvalAt D v y) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_Submodule_eq_of_forall_finiteAdeleEvalAt_eq.solution
