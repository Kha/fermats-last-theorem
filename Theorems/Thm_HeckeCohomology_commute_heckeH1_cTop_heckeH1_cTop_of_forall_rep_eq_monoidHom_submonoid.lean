import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import P2M.Util
import P2M.Sol.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

p2m_open "groupCohomology HeckeCohomology~heckeH1_eq_of_section"

theorem HeckeCohomology.commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M)
    (ℓ' : ℕ) (hℓ' : ℓ'.Prime) (hℓN' : ¬ ℓ' ∣ N) (hℓM' : !![(ℓ' : ℤ), 0; 0, 1] ∈ M)
    (hφ : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
        (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩))
    (hφ' : haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ') X
        (ρ' ⟨!![(ℓ' : ℤ), 0; 0, 1], hℓM'⟩)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    Commute (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ) (HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ') (HeckeCohomology.cTop N ⊥ ℓ') X _ hφ') := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_cTop_of_forall_rep_eq_monoidHom_submonoid.solution
