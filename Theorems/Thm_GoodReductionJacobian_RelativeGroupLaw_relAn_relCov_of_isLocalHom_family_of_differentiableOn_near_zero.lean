import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero
attribute [-instance] PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian Topology

theorem GoodReductionJacobian.RelativeGroupLaw.relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    {G : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of Sc)} (L : RelativeGroupLaw Sc f)
    (hsep : IsSeparated f) (hsm : SmoothOfRelativeDimension 2 f)

    (Pf : (Sc →ₐ[ℂ] ℂ) → (Fin 2 → ℂ) → (Spec (CommRingCat.of ℂ) ⟶ G))
    (ε₀ r' : ℝ) (hε₀ : 0 < ε₀) (hε₀r : ε₀ ≤ r) (hr' : 0 < r')

    (hOVER : ∀ σ ∈ 𝒰, ∀ w : Fin 2 → ℂ, (Pf σ w) ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))

    (hHOM : ∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ)
      (hw : (Pf σ w) ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
      (hw' : (Pf σ w') ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom)),
      (L.mul (Spec.map (CommRingCat.ofHom σ.toRingHom)) ⟨(Pf σ w), hw⟩ ⟨(Pf σ w'), hw'⟩).1 = (Pf σ (w + w')))

    (hLOCAN : ∀ (V : G.Opens) (φ : Γ(G, V)),
      IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₀ ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
        ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
      ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
        DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε₀ ∧ p.2 ∈ Metric.ball (0 : Fin 2 → ℂ) r' ∧
          ∃ σ ∈ 𝒰, σ t = p.1 ∧ ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
        ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε₀ → ∀ w ∈ Metric.ball (0 : Fin 2 → ℂ) r', ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
          F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ w)).appLE V ⊤ hV) φ))

    (hFIBCOV : ∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε₀ → ∀ w₁ : Fin 2 → ℂ,
      ∃ (V : G.Opens) (f₂ f₃ : Γ(G, V)) (δ : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
        (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
        0 < δ ∧
        (∀ w ∈ Metric.ball w₁ δ, ⊤ ≤ (Pf σ₁ w) ⁻¹ᵁ V) ∧
        (∀ (w : Fin 2 → ℂ) (hV : ⊤ ≤ (Pf σ₁ w) ⁻¹ᵁ V), w ∈ Metric.ball w₁ δ →
          F w = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ₁ w)).appLE V ⊤ hV) f₂),
            (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((Pf σ₁ w)).appLE V ⊤ hV) f₃)]) ∧
        HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) w₁) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧

      (∀ (V : G.Opens) (f : Γ(G, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((Pf σ w).appLE V ⊤ hV) f)) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (Pf σ₁ w₁) =
          (Pf σ₁ w₁') →
        ∃ (V : G.Opens) (f₂ f₃ : Γ(G, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (Pf σ₁ w₁) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (Pf σ p.2) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (Pf σ w) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (Pf σ w') ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w').appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ w').appLE V ⊤ hV') f₃) →
              (Pf σ w) =
                (Pf σ w'))) ∧

      (∀ w : Fin 2 → ℂ, Pf σ₀ w ≠ (L.one (Spec.map (CommRingCat.ofHom σ₀.toRingHom))).1 →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) δ → ∀ w' : Fin 2 → ℂ,
          Pf σ w' = (L.one (Spec.map (CommRingCat.ofHom σ.toRingHom))).1 → δ ≤ ‖w' - w‖) ∧

      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : G.Opens) (fs : Finset ↑(Γ(G, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (Pf σ₁ w₁) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : Spec (CommRingCat.of ℂ) ⟶ G) (hPσ : P ≫ f = Spec.map (CommRingCat.ofHom σ.toRingHom))
              (hP : ⊤ ≤ P ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((Pf σ₁ w₁).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ, P = Pf σ w) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_relAn_relCov_of_isLocalHom_family_of_differentiableOn_near_zero.solution
