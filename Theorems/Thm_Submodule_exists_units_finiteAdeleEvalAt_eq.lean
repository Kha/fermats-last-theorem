import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import P2M.Util
import P2M.Sol.S_Submodule_exists_units_finiteAdeleEvalAt_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem Submodule.exists_units_finiteAdeleEvalAt_eq
    {D : Type*} [Ring D] [Algebra ℚ D] [Module.Finite ℚ D]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (y : ∀ v : HeightOneSpectrum (𝓞 ℚ), (D ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ β : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      (∀ v ∈ S, Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y v) ∧
      ∀ v ∉ S, Submodule.finiteAdeleEvalAt D v (β : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_units_finiteAdeleEvalAt_eq.solution
