import Definitions.Def_CohCarrier_LevelPairing
import P2M.Util
import P2M.Sol.S_IharaTower_iDegL_one_unitRoot_sub_iDegL_intertwines_heckeT

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower

theorem IharaTower.iDegL_one_unitRoot_sub_iDegL_intertwines_heckeT
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    [Module 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (hdia : ∀ (σ : CongruenceSubgroup.Gamma0 N) (v : H1 N Hs 𝒪),
      v ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx) → diamondRaw N Hs 𝒪 σ v = v)
    (σ : CongruenceSubgroup.Gamma0 N)
    (hU1 : ∀ v : H1 N Hs 𝒪, heckeT (N * q) Hs' q 𝒪 (iDeg' N (N * q) Hs Hs' 1 𝒪 h1 v) =
      iDeg' N (N * q) Hs Hs' 1 𝒪 h1 (heckeT N Hs q 𝒪 v) - iDeg' N (N * q) Hs Hs' q 𝒪 hq' (diamondRaw N Hs 𝒪 σ v))
    (hUq : ∀ v : H1 N Hs 𝒪, heckeT (N * q) Hs' q 𝒪 (iDeg' N (N * q) Hs Hs' q 𝒪 hq' v) =
      q • iDeg' N (N * q) Hs Hs' 1 𝒪 h1 v)
    (m : cd.cornerModule) :
    iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • (αt • m) : cd.cornerModule) : H1 N Hs 𝒪)
        - iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((αt • m : cd.cornerModule) : H1 N Hs 𝒪) =
      heckeT (N * q) Hs' q 𝒪 (iDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • m : cd.cornerModule) : H1 N Hs 𝒪)
        - iDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m : H1 N Hs 𝒪)) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_iDegL_one_unitRoot_sub_iDegL_intertwines_heckeT.solution
