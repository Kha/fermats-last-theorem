import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed

set_option autoImplicit false

theorem Module.End.maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed
    {K : Type} [Field K] [CharZero K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : Module.End K W)
    (Ω₁ : Type) [Field Ω₁] [Algebra K Ω₁] [IsAlgClosed Ω₁]
    (h₁ : ∀ μ : Ω₁, Module.End.maxGenEigenspace (T.baseChange Ω₁) μ ≤
      Module.End.eigenspace (T.baseChange Ω₁) μ)
    (Ω₂ : Type) [Field Ω₂] [Algebra K Ω₂] (μ : Ω₂) :
    Module.End.maxGenEigenspace (T.baseChange Ω₂) μ ≤ Module.End.eigenspace (T.baseChange Ω₂) μ := by p2m_exact_reverting @_root_.P2MW.S_Module_End_maxGenEigenspace_baseChange_le_eigenspace_of_isAlgClosed.solution
