import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import P2M.Util
import P2M.Sol.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul

set_option autoImplicit false

open scoped TensorProduct

theorem Module.End.finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul
    (F : Type) [Field F]
    (V W : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ι κ : Type} (A : ι → Module.End F V) (μ : ι → F) (B : κ → Module.End F W) (ν : κ → F) :
    Module.finrank F
      ↥((⨅ i : ι, Module.End.maxGenEigenspace (TensorProduct.map (A i) (LinearMap.id : W →ₗ[F] W)) (μ i)) ⊓
        (⨅ j : κ, Module.End.maxGenEigenspace (TensorProduct.map (LinearMap.id : V →ₗ[F] V) (B j)) (ν j))) =
    Module.finrank F ↥(⨅ i : ι, Module.End.maxGenEigenspace (A i) (μ i)) *
      Module.finrank F ↥(⨅ j : κ, Module.End.maxGenEigenspace (B j) (ν j)) := by p2m_exact_reverting @_root_.P2MW.S_Module_End_finrank_iInf_maxGenEigenspace_map_tensorProduct_eq_mul.solution
