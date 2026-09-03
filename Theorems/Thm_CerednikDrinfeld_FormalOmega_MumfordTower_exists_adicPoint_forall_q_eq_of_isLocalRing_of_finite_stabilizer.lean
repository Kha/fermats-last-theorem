import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))

    (hNfin : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ N ∧ g • v = v})
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra 𝒪 R]
    (hmod : ∀ n : ℕ, (algebraMap 𝒪 (modPow π R n) π) ^ (n + 1) = 0) :
    (∀ η : ∀ n : ℕ, Spec (CommRingCat.of (modPow π R n)) ⟶ DM.Z n,
      (∀ n : ℕ, η n ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (modPow π R n)))) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (modPowTransition π R n).toRingHom) ≫ η (n + 1) = η n ≫ DM.zt n) →
      ∃ x : AdicPoint K₀ π R, ∀ n : ℕ, η n = DM.q n (modPow π R n) (hmod n) (x.pt n)) ∧
    (∀ x x' : AdicPoint K₀ π R,
      (∀ n : ℕ, DM.q n (modPow π R n) (hmod n) (x.pt n) = DM.q n (modPow π R n) (hmod n) (x'.pt n)) ↔
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
        ∀ n : ℕ, DeligneDatum.IsPullback (K := K₀) (π := π) (modPow π R n) g⁻¹ (x.pt n) (x'.pt n)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_exists_adicPoint_forall_q_eq_of_isLocalRing_of_finite_stabilizer.solution
