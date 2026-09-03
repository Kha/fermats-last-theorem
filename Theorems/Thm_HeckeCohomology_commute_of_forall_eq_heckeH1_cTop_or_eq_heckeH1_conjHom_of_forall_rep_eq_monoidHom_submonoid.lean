import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_DClassCoeff
import P2M.Util
import P2M.Sol.S_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

theorem
HeckeCohomology.commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
    (N : ℕ) (κ : Type) [CommRing κ] (X : Rep κ ↥(CohCarrier.GammaH N ⊥))
    (M : Submonoid (Matrix (Fin 2) (Fin 2) ℤ))
    (hΓ : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      g ∈ CongruenceSubgroup.Gamma0 N → (g : Matrix (Fin 2) (Fin 2) ℤ) ∈ M)
    (ρ' : M →* Module.End κ X)
    (hρ' : ∀ γ : ↥(CohCarrier.GammaH N ⊥),
      X.ρ γ = ρ' ⟨((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ),
        hΓ _ (CohCarrier.mem_GammaH_iff.mp γ.2).1⟩)
    (ι : Type) (T : ι → (groupCohomology.H1 X →ₗ[κ] groupCohomology.H1 X))
    (hT : ∀ i : ι,
      (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (_ : ¬ ℓ ∣ N) (hℓM : !![(ℓ : ℤ), 0; 0, 1] ∈ M),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ hφ : HeckeCohomology.IsTwist ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X
            (ρ' ⟨!![(ℓ : ℤ), 0; 0, 1], hℓM⟩),
          T i = HeckeCohomology.heckeH1 ⊤ (CohCarrier.GammaHUpper N ⊥ ℓ) (HeckeCohomology.cTop N ⊥ ℓ) X _ hφ) ∨
      (∃ (σ : CongruenceSubgroup.Gamma0 N)
          (hψ : HeckeCohomology.IsTwist ⊤ ⊤
            (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
              fun _ => Subgroup.mem_top _)
            X (ρ' ⟨(((σ⁻¹ : CongruenceSubgroup.Gamma0 N) : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ), hΓ _ (σ⁻¹).2⟩)),
        T i = HeckeCohomology.heckeH1 ⊤ ⊤
          (((CohCarrier.conjHom N ⊥ σ).comp (⊤ : Subgroup ↥(CohCarrier.GammaH N ⊥)).subtype).codRestrict ⊤
            fun _ => Subgroup.mem_top _)
          X _ hψ)) :
    ∀ i j : ι, Commute (T i) (T j) := by p2m_exact_reverting @_root_.P2MW.S_HeckeCohomology_commute_of_forall_eq_heckeH1_cTop_or_eq_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid.solution
