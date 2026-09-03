import Definitions.Def_CohCarrier_LevelPairing
import P2M.Util
import P2M.Sol.S_IharaTower_CornerData_exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint

set_option autoImplicit false

theorem IharaTower.CornerData.exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint
    {𝒪 : Type} [CommRing 𝒪]
    {𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋ₐ V] [Module 𝕋₁ V]
    [IsScalarTower 𝒪 𝕋ₐ V] [IsScalarTower 𝒪 𝕋₁ V]
    (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (hι : ∀ (t : 𝕋ₐ) (v : V), ι t • v = t • v)
    (cdₐ : IharaTower.CornerData (𝒪 := 𝒪) 𝕋ₐ V) (S₁ : IharaLemma.IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
    (hincl : ∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) →
      v ∈ IharaLemma.cornerSubmodule (M := V) (cdₐ.split.e cdₐ.idx))
    (hadj : ∀ (t : 𝕋₁) (x y Tx Ty : cdₐ.cornerModule), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      cdₐ.pairing.B Tx y = cdₐ.pairing.B x Ty) :
    ∃ C : Submodule 𝒪 V,
      (∀ v : V, v ∈ IharaLemma.cornerSubmodule (M := V) (cdₐ.split.e cdₐ.idx) ↔
        ∃ v₁ v₂, v₁ ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) ∧ v₂ ∈ C ∧ v = v₁ + v₂) ∧
      (∀ v, v ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) → v ∈ C → v = 0) ∧
      (∀ (x y : cdₐ.cornerModule), (x : V) ∈ IharaLemma.cornerSubmodule (M := V) (S₁.e i₁) → (y : V) ∈ C →
        cdₐ.pairing.B x y = 0 ∧ cdₐ.pairing.B y x = 0) ∧
      (∀ (t : cdₐ.cornerRing) (y : cdₐ.cornerModule), (y : V) ∈ C →
        ((t • y : cdₐ.cornerModule) : V) ∈ C) := by p2m_exact_reverting @_root_.P2MW.S_IharaTower_CornerData_exists_orthogonal_stable_complement_of_corner_le_of_selfAdjoint.solution
