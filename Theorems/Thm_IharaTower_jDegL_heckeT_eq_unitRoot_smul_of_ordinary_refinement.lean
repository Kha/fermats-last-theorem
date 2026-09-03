import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement

set_option autoImplicit false

p2m_open "CohCarrier IharaLemma~eq_zero_of_mem_cornerSubmodule_of_intertwining_nilpotent IharaTower"

theorem IharaTower.jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)
    (hstab : ∀ (t : 𝕋₁) (v : H1 (N * q) Hs' 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      t • v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (mjq : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (mj1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v' ∈ cornerSubmodule (M := H1 N Hs 𝒪) (cd.split.e cd.idx))
    (U : 𝕋₁) (hUact : ∀ v' : H1 (N * q) Hs' 𝒪, U • v' = heckeT (N * q) Hs' q 𝒪 v')
    (tp αt : cd.cornerRing)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 cd.cornerRing (q : 𝒪) = 0)
    (hTp : ∀ m : cd.cornerModule, ((tp • m : cd.cornerModule) : H1 N Hs 𝒪) = heckeT N Hs q 𝒪 (m : H1 N Hs 𝒪))
    (R1 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = q • jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (R2 : ∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx) →
      jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') =
        heckeT N Hs q 𝒪 (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v') - jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v')
    [Module.Finite 𝒪 cd.cornerModule] [Module.Finite 𝒪 cd.cornerRing]
    (hUunit : U ∉ cd₁.split.𝔪 cd₁.idx)
    (hβmem : tp - αt ∈ IsLocalRing.maximalIdeal cd.cornerRing)
    (v' : H1 (N * q) Hs' 𝒪)
    (hva : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
    (hv1 : v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx))
    (jmq jm1 : cd.cornerModule)
    (hjmq : (jmq : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')
    (hjm1 : (jm1 : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v') :
    jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jmq : cd.cornerModule) : H1 N Hs 𝒪) ∧
    jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (heckeT (N * q) Hs' q 𝒪 v') = ((αt • jm1 : cd.cornerModule) : H1 N Hs 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement.solution
