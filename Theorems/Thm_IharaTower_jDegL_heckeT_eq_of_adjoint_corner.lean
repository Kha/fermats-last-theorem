import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import P2M.Util
import P2M.Sol.S_IharaTower_jDegL_heckeT_eq_of_adjoint_corner

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower IharaTower.CornerData CongruenceSubgroup
open scoped MatrixGroups

theorem IharaTower.jDegL_heckeT_eq_of_adjoint_corner
    (N q : ℕ) [NeZero N] [NeZero q] [NeZero (N * q)]
    (Hs : Subgroup (ZMod N)ˣ) (Hs' : Subgroup (ZMod (N * q))ˣ)
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪]
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋' (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋' (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋')
    [Module.Finite 𝒪 cd.cornerModule] [Module.Free 𝒪 cd.cornerModule]
    (hci : ∀ (k : Fin 2) (v : H1 N Hs 𝒪), v ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) →
      ![iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1, iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq'] k v
        ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd'.split.e cd'.idx))
    (hcj : ∀ (k : Fin 2) (v' : H1 (N * q) Hs' 𝒪),
      v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd'.split.e cd'.idx) →
      ![jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq', jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1] k v'
        ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (hadj : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B ⟨![jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq', jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1] k m', hcj k _ m'.2⟩ m =
        cd'.pairing.B m' ⟨![iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1, iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq'] k m, hci k _ m.2⟩)
    (hU : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd'.split.e cd'.idx) →
      heckeT (N * q) Hs' q 𝒪 v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd'.split.e cd'.idx))
    (hUadj : ∀ (x y Ux Uy : cd'.cornerModule),
      (Ux : H1 (N * q) Hs' 𝒪) = heckeT (N * q) Hs' q 𝒪 x → (Uy : H1 (N * q) Hs' 𝒪) = heckeT (N * q) Hs' q 𝒪 y →
      cd'.pairing.B Ux y = cd'.pairing.B x Uy)
    (hdia : ∀ (σ : Gamma0 N) (v : H1 N Hs 𝒪),
      v ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) → diamondRaw N Hs 𝒪 σ v = v)
    (Tq : cd.cornerRing)
    (hTq : ∀ m : cd.cornerModule, ((Tq • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))

    (hUq : ∀ v : H1 N Hs 𝒪, heckeT (N * q) Hs' q 𝒪 (iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v) =
      q • iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v)
    (σ : Gamma0 N)
    (hU1 : ∀ v : H1 N Hs 𝒪, heckeT (N * q) Hs' q 𝒪 (iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v) =
      iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT N Hs q 𝒪 v) - iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (diamondRaw N Hs 𝒪 σ v)) :
    (∀ m' : cd'.cornerModule,
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 (m' : H1 (N * q) Hs' 𝒪)) =
        q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪)) ∧
    (∀ m' : cd'.cornerModule,
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 (m' : H1 (N * q) Hs' 𝒪)) =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪)) -
          jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪)) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_jDegL_heckeT_eq_of_adjoint_corner.solution
