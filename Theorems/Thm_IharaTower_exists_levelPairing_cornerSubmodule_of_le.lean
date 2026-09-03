import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_IharaLemma_IdempotentSplitting
import P2M.Util
import P2M.Sol.S_IharaTower_exists_levelPairing_cornerSubmodule_of_le

theorem IharaTower.exists_levelPairing_cornerSubmodule_of_le
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W : Submodule 𝕋 V) (B : W →ₗ[𝒪] W →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y : W), B (t • x) y = B x (t • y))
    (S : IharaLemma.IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : IharaLemma.cornerSubmodule (M := V) (S.e i) ≤ W) :
    ∃ P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i)
        ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
        P.B x y = B (Submodule.inclusion hle x) (Submodule.inclusion hle y) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_le.solution
