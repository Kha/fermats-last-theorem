import Definitions.Def_CerednikDrinfeld_MumfordTower
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_q_eq_of_isAlgClosed

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_q_eq_of_isAlgClosed

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : (algebraMap 𝒪 k π) ^ (n + 1) = 0)
    (z : Spec (CommRingCat.of k) ⟶ DM.Z n)
    (hz : z ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 k))) :
    ∃ P : (Omega K₀ π).obj k, DM.q n k hk P = z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_q_eq_of_isAlgClosed.solution
