import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import P2M.Util
import P2M.Sol.S_IharaLemma_map_codRestrict_eq_of_residual

set_option autoImplicit false

theorem IharaLemma.map_codRestrict_eq_of_residual {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] {W : Type} [AddCommGroup W] [Module B W] [Module 𝒪 W]
    [IsScalarTower 𝒪 B W] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [Module.Finite 𝒪 W] [Module.Free 𝒪 W] {V : Type} [AddCommGroup V] [Module 𝒪 V]
    (i : V →ₗ[𝒪] W) (e : B)
    (hmem : ∀ v : V, i v ∈ (IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)
    (hi : Function.Injective i) {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : V) (x : W), i v = ϖ • x → ∃ v₁ : V, v = ϖ • v₁)
    {A : Submodule 𝒪 V} (hA : ∀ (c : 𝒪) (x : V), c ≠ 0 → c • x ∈ A → x ∈ A)
    {Bc : Submodule 𝒪 ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪)}
    (hle : Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A ≤ Bc)
    (hrank : Module.finrank 𝒪 Bc ≤ Module.finrank 𝒪 A) :
    Submodule.map (LinearMap.codRestrict
      ((IharaLemma.cornerSubmodule (M := W) e).restrictScalars 𝒪) i hmem) A = Bc := by p2m_exact_reverting @_root_.P2MW.S_IharaLemma_map_codRestrict_eq_of_residual.solution
