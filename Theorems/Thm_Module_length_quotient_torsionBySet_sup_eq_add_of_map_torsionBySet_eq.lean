import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dual.Defs
import P2M.Util
import P2M.Sol.S_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq

universe u v w x
theorem Module.length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq
    {𝒪 : Type u} {T T' : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [Algebra 𝒪 T] [CommRing T'] [Algebra 𝒪 T']
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (πT' : T' →ₐ[𝒪] 𝒪) (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪) :
    Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) =
        Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) ∧
      Module.length 𝒪 (M' ⧸ (Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ⊔
          Submodule.torsionBySet T' M' ↑(RingHom.ker πT').annihilator)) =
        Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
          Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)) +
        (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
          Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ}) := by p2m_exact_reverting @_root_.P2MW.S_Module_length_quotient_torsionBySet_sup_eq_add_of_map_torsionBySet_eq.solution
