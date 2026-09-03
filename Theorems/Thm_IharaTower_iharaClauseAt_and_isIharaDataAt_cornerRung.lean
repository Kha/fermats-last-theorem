import Definitions.Def_HeckeModule_IharaDataAt
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung

set_option autoImplicit false
open IharaLemma IharaTower.RungAssembly in

theorem IharaTower.iharaClauseAt_and_isIharaDataAt_cornerRung
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
    (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
    (P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀)
      ↥(cornerSubmodule (M := V) (S.e i₀)))
    (P' : IharaTower.LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀')
      ↥(cornerSubmodule (M := V') (S'.e i₀')))
    {n : ℕ}
    (L : LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
      (M := ↥(cornerSubmodule (M := V) (S.e i₀)))
      (M' := ↥(cornerSubmodule (M := V') (S'.e i₀')))
      (𝒪 := 𝒪) P P' n)
    (c : Fin n → S.CornerRing i₀) (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀)
    (πT : S.CornerRing i₀ →ₐ[𝒪] 𝒪)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V) (S.e i₀))]
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := V') (S'.e i₀'))]
    {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    (hres : ∀ (v : ↥(cornerSubmodule (M := V) (S.e i₀)))
      (x : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      iComb L c v = ϖ • x → ∃ v₁, v = ϖ • v₁)
    (hjeq : ∀ (t' : S'.CornerRing i₀') (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))),
      jComb L c (t' • m') = res t' • jComb L c m')
    (hsat' : ∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := V') (S'.e i₀'))), a ≠ 0 →
      a • m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪 →
      m' ∈ (RingHom.ker (πT.comp res) • ⊤ :
        Submodule (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))).restrictScalars 𝒪)
    (hrank : Module.finrank 𝒪
        ((Submodule.torsionBySet (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀'))
          ↑(RingHom.ker (πT.comp res))).restrictScalars 𝒪)
      ≤ Module.finrank 𝒪
        ((Submodule.torsionBySet (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀))
          ↑(RingHom.ker πT)).restrictScalars 𝒪)) :
    IharaTower.IharaClauseAt (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      πT (πT.comp res) ∧
    IharaTower.IsIharaDataAt (IharaTower.cornerRung S S' i₀ i₀' P P' L c res)
      πT (πT.comp res) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_iharaClauseAt_and_isIharaDataAt_cornerRung.solution
