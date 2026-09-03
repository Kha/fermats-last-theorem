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
import P2M.Util
import P2M.Sol.S_AlgHom_bijective_and_free_of_length_le_of_levelChange

universe u v w x

theorem AlgHom.bijective_and_free_of_length_le_of_levelChange
    {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {T : Type w} [CommRing T] [Algebra 𝒪 T] (πT : T →ₐ[𝒪] 𝒪)
    (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    {R₀ : Type v} [CommRing R₀] [Algebra 𝒪 R₀] (πR₀ : R₀ →ₐ[𝒪] 𝒪)
    (hS : (Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) : ℕ∞) *
        Module.length 𝒪 (RingHom.ker πR₀).Cotangent ≤
      Module.length 𝒪 (M ⧸ (Submodule.torsionBySet T M ↑(RingHom.ker πT) ⊔
        Submodule.torsionBySet T M ↑(RingHom.ker πT).annihilator)))
    {R' : Type v} [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    [IsAdicComplete (IsLocalRing.maximalIdeal R') R'] [Algebra 𝒪 R']
    {T' : Type w} [CommRing T'] [IsLocalRing T'] [Algebra 𝒪 T'] [Module.Finite 𝒪 T'] [Module.Free 𝒪 T']
    (φ' : R' →ₐ[𝒪] T') (hφ' : Function.Surjective φ') (πR' : R' →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪)
    (hπ' : πT'.comp φ' = πR') (hη' : (RingHom.ker πT').annihilator.map πT' ≠ ⊥)
    (M' : Type x) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    [Module.Finite 𝒪 M'] [Module.Free 𝒪 M']
    (B' : M' →ₗ[𝒪] M' →ₗ[𝒪] 𝒪) (hB' : ∀ (t : T') (m n : M'), B' (t • m) n = B' m (t • n))
    (hBb' : Function.Bijective B')
    (hM' : Submodule.torsionBySet T' M' ↑(RingHom.ker πT') ≠ ⊥)
    (hrank' : Module.finrank 𝒪 M' =
      Module.finrank 𝒪 (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')) * Module.finrank 𝒪 T')
    (i : M →ₗ[𝒪] M') (j : M' →ₗ[𝒪] M) (hadj : ∀ (m' : M') (m : M), B (j m') m = B' m' (i m))
    (Δ : T) (hji : ∀ m : M, j (i m) = Δ • m) (hΔ : πT Δ ≠ 0)
    (h℘ : Submodule.map i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
      (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪)
    (hcot : Module.length 𝒪 (RingHom.ker πR').Cotangent ≤
      Module.length 𝒪 (RingHom.ker πR₀).Cotangent + Module.length 𝒪 (𝒪 ⧸ Ideal.span {πT Δ})) :
    Function.Bijective φ' ∧
      (∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪),
        Nonempty ((MvPowerSeries (Fin n) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T')) ∧
      Module.Free T' M' := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_bijective_and_free_of_length_le_of_levelChange.solution
