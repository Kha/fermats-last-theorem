import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem AutomorphicForm.exists_prod_eq_and_coupled_of_coupled_prod
    {G₁ G₂ H₁ H₂ : Type}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [LocallyCompactSpace H₁]
    [SecondCountableTopology H₁] [T2Space H₁]
    [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂] [LocallyCompactSpace H₂]
    [SecondCountableTopology H₂] [T2Space H₂]
    (φ₁ : G₁ →* H₁) (hφ₁ : Topology.IsClosedEmbedding φ₁) (φ₂ : G₂ →* H₂) (hφ₂ : Topology.IsClosedEmbedding φ₂)
    (η₁ : H₁ →* H₁) (hη₁ : Continuous η₁) (η₂ : H₂ →* H₂) (hη₂ : Continuous η₂)
    (γ₁ : G₁) (γ₂ : G₂) (δ₁ y₁ : H₁) (δ₂ y₂ : H₂)
    (eC : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) →
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)))
    (heC : ∀ p, ((eC p : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂)))
    (eT : AutomorphicForm.sigmaCentralizer η₁ δ₁ × AutomorphicForm.sigmaCentralizer η₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂))
    (heT : ∀ p, ((eT p : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) : H₁ × H₂) =
      ((p.1 : H₁), (p.2 : H₂)))
    (τ : @Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hcpl : @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun t : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) =>
          (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)) τ' =
      @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂)) τ) :
    ∃ (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _))
      (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _))
      (τ₁' : @Measure (AutomorphicForm.sigmaCentralizer η₁ δ₁) (borel _))
      (τ₂' : @Measure (AutomorphicForm.sigmaCentralizer η₂ δ₂) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁' ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' ∧
      τ = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eC
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) ∧
      τ' = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eT
            (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂') ∧
      @Measure.map _ _ (borel _) (borel H₁)
          (fun t : AutomorphicForm.sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) τ₁' =
        @Measure.map _ _ (borel _) (borel H₁)
          (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁)) τ₁ ∧
      @Measure.map _ _ (borel _) (borel H₂)
          (fun t : AutomorphicForm.sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) τ₂' =
        @Measure.map _ _ (borel _) (borel H₂)
          (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) τ₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod.solution
