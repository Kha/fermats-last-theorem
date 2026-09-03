import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_residueField_of_isEigensystemH1_of_isDiscreteValuationRing

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.isEigensystemH1_residueField_of_isEigensystemH1_of_isDiscreteValuationRing
    (N : ℕ) [Group.FG (Gamma0 N)]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {L : Type} [Field L] [Algebra O L] (hOL : Function.Injective (algebraMap O L))
    (S₀ : Set ℕ)
    {Λ : Type} [AddCommGroup Λ] [Module O Λ]
    {V : Type} [AddCommGroup V] [Module L V]
    {W : Type} [AddCommGroup W] [Module (IsLocalRing.ResidueField O) W]
    (ρO : Representation O (Gamma0 N) Λ) (ρL : Representation L (Gamma0 N) V)
    (ρk : Representation (IsLocalRing.ResidueField O) (Gamma0 N) W)
    (aO : ℕ → (Λ →ₗ[O] Λ)) (aL : ℕ → (V →ₗ[L] V)) (ak : ℕ → (W →ₗ[IsLocalRing.ResidueField O] W))
    (haO : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        aO ℓ ∘ₗ ρO (HeckeEis.heckeConj N ℓ u) = ρO (u : Gamma0 N) ∘ₗ aO ℓ)
    (jL : Λ →ₛₗ[algebraMap O L] V) (hjL : ∀ (g : Gamma0 N) (x : Λ), jL (ρO g x) = ρL g (jL x))
    (hjLa : ∀ (ℓ : ℕ) (x : Λ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → jL (aO ℓ x) = aL ℓ (jL x))
    (jk : Λ →ₛₗ[IsLocalRing.residue O] W) (hjk : ∀ (g : Gamma0 N) (x : Λ), jk (ρO g x) = ρk g (jk x))
    (hjka : ∀ (ℓ : ℕ) (x : Λ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → jk (aO ℓ x) = ak ℓ (jk x))
    (hbc : ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι O Λ) (bL : Module.Basis ι L V)
        (bk : Module.Basis ι (IsLocalRing.ResidueField O) W),
      (∀ i : ι, bL i = jL (b i)) ∧ ∀ i : ι, bk i = jk (b i))
    (hTF : ∀ (c : O) (x : HeckeEis.coeffH1 ρO), c • x = 0 → c = 0 ∨ x = 0)
    (lam : ℕ → O)
    (h : HeckeEis.IsEigensystemH1 N ρL aL S₀ (fun ℓ => algebraMap O L (lam ℓ))) :
    HeckeEis.IsEigensystemH1 N ρk ak S₀ (fun ℓ => IsLocalRing.residue O (lam ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_residueField_of_isEigensystemH1_of_isDiscreteValuationRing.solution
