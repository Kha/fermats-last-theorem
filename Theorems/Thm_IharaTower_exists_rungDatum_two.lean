import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower
import P2M.Util
import P2M.Sol.S_IharaTower_exists_rungDatum_two

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower IharaTower.CornerData IharaTower.RungAssembly

theorem IharaTower.exists_rungDatum_two (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (Hs : Subgroup (ZMod N)ˣ) (Hs' : Subgroup (ZMod (N * q))ˣ)
    (h1 : LevelLE N (N * q) Hs Hs' 1) (hq' : LevelLE N (N * q) Hs Hs' q)
    {𝒪 : Type} [CommRing 𝒪] {A : Type} [AddCommGroup A] [Module 𝒪 A]
    {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
    [Module 𝕋 (H1 N Hs A)] [Module 𝕋' (H1 (N * q) Hs' A)]
    [IsScalarTower 𝒪 𝕋 (H1 N Hs A)] [IsScalarTower 𝒪 𝕋' (H1 (N * q) Hs' A)]
    (cd : H1CornerData (𝒪 := 𝒪) N Hs A 𝕋) (cd' : H1CornerData (𝒪 := 𝒪) (N * q) Hs' A 𝕋')
    (hci : ∀ (k : Fin 2) (v : H1 N Hs A), v ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx) →
      ![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k v
        ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx))
    (hcj : ∀ (k : Fin 2) (v' : H1 (N * q) Hs' A),
      v' ∈ cornerSubmodule (M := H1 (N * q) Hs' A) (cd'.split.e cd'.idx) →
      ![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k v'
        ∈ cornerSubmodule (M := H1 N Hs A) (cd.split.e cd.idx))
    (Tq Tl : cd.cornerRing)
    (hTq : ∀ m : cd.cornerModule, ((Tq • m : cd.cornerModule) : H1 N Hs A) = heckeT N Hs q A (m : H1 N Hs A))
    (hTl : ∀ m : cd.cornerModule, ((Tl • m : cd.cornerModule) : H1 N Hs A) = heckeTlower N Hs q A (m : H1 N Hs A))
    (hadj : ∀ (k : Fin 2) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B ⟨![jDegL N (N * q) Hs Hs' q A 𝒪 hq', jDegL N (N * q) Hs Hs' 1 A 𝒪 h1] k m', hcj k _ m'.2⟩ m =
        cd'.pairing.B m' ⟨![iDegL N (N * q) Hs Hs' 1 A 𝒪 h1, iDegL N (N * q) Hs Hs' q A 𝒪 hq'] k m, hci k _ m.2⟩)
    (a : cd.cornerRing) (res : cd'.cornerRing →ₐ[𝒪] cd.cornerRing) :
    ∃ R : RungDatum (𝒪 := 𝒪) cd.cornerRing cd'.cornerRing cd.cornerModule cd'.cornerModule cd.pairing cd'.pairing,
      R.res = res ∧
      (∀ m : cd.cornerModule, (R.i m : H1 (N * q) Hs' A) =
        iDegL N (N * q) Hs Hs' 1 A 𝒪 h1 ((a • m : cd.cornerModule) : H1 N Hs A) - iDegL N (N * q) Hs Hs' q A 𝒪 hq' m) ∧
      (∀ m' : cd'.cornerModule, (R.j m' : H1 N Hs A) =
        ((a • (⟨jDegL N (N * q) Hs Hs' q A 𝒪 hq' m', hcj 0 _ m'.2⟩ : cd.cornerModule) : cd.cornerModule) : H1 N Hs A)
          - jDegL N (N * q) Hs Hs' 1 A 𝒪 h1 m') ∧
      R.Δ = a ^ 2 * (algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' q hq').range.subgroupOf (GammaHUpper N Hs q)).index : 𝒪) * Tq)
        - a * (algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' q hq').range.index : 𝒪)
            + algebraMap 𝒪 cd.cornerRing ((iotaDeg N (N * q) Hs Hs' 1 h1).range.index : 𝒪))
        + algebraMap 𝒪 cd.cornerRing (((iotaDeg N (N * q) Hs Hs' 1 h1).range.subgroupOf (GammaHLower N Hs q)).index : 𝒪) * Tl := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_exists_rungDatum_two.solution
