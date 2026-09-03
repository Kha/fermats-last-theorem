import Definitions.Def_CohCarrier_LevelPairing
import Mathlib.RingTheory.Noetherian.Defs
import P2M.Util
import P2M.Sol.S_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement

set_option autoImplicit false

p2m_open "CohCarrier IharaLemma IharaTower~jDegL_heckeT_eq_unitRoot_smul_of_ordinary_refinement"

theorem IharaTower.jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement
    {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)]
    {Hs : Subgroup (ZMod N)ˣ} {Hs' : Subgroup (ZMod (N * q))ˣ}
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] [IsLocalRing 𝒪]
    {𝕋 𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋] [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    [Module 𝕋 (H1 N Hs 𝒪)] [Module 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [Module 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs 𝒪)] [IsScalarTower 𝒪 𝕋ₐ (H1 (N * q) Hs' 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * q) Hs' 𝒪)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs 𝒪 𝕋) (cdₐ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋ₐ)
    (cd₁ : H1CornerData (𝒪 := 𝒪) (N * q) Hs' 𝒪 𝕋₁)
    (hincl : ∀ v : H1 (N * q) Hs' 𝒪, v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
      v ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cdₐ.split.e cdₐ.idx))
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
    (res : cd₁.cornerRing →ₐ[𝒪] cd.cornerRing)
    (hresU : res (cd₁.split.toCornerRing cd₁.idx U) = αt)
    (G : Set cd₁.cornerRing) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ x ∈ G,
      (∃ (A' : H1 (N * q) Hs' 𝒪 → H1 (N * q) Hs' 𝒪) (A : H1 N Hs 𝒪 → H1 N Hs 𝒪),
        (∀ m : cd₁.cornerModule, ((x • m : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) =
          A' (m : H1 (N * q) Hs' 𝒪)) ∧
        (∀ m : cd.cornerModule, ((res x • m : cd.cornerModule) : H1 N Hs 𝒪) = A (m : H1 N Hs 𝒪)) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (A' v') = A (jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' v')) ∧
        (∀ v' : H1 (N * q) Hs' 𝒪, v' ∈ cornerSubmodule (M := H1 (N * q) Hs' 𝒪) (cd₁.split.e cd₁.idx) →
          jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (A' v') = A (jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 v'))) ∨
      x = cd₁.split.toCornerRing cd₁.idx U) :
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' q 𝒪 𝒪 hq' ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) ∧
    (∀ (t₁ : cd₁.cornerRing) (m' : cd₁.cornerModule) (jm jtm : cd.cornerModule),
      (jm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 (m' : H1 (N * q) Hs' 𝒪) →
      (jtm : H1 N Hs 𝒪) = jDegL N (N * q) Hs Hs' 1 𝒪 𝒪 h1 ((t₁ • m' : cd₁.cornerModule) : H1 (N * q) Hs' 𝒪) →
      jtm = res t₁ • jm) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_jDegL_smul_eq_res_smul_jDegL_of_generators_of_ordinary_refinement.solution
