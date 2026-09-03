import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
    {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)}
    (L : RelativeGroupLaw ℂ f) (L' : RelativeGroupLaw ℂ f') {g g' : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

    (hL1' : ∃ b₀ : Module.Basis (Fin (2 * g')) ℝ (Fin g' → ℂ), Λ' = Submodule.span ℤ (Set.range b₀))

    (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (he' : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f', e' (L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e' P + e' Q)

    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ)))

    (hAN' : ∀ (U : G'.Opens) (φ : Γ(G', U)),
      IsOpen {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g' → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) φ)))

    (hCOV' : ∀ v₀ : Fin g' → ℂ,
      ∃ (U : G'.Opens) (t : Fin g' → Γ(G', U)) (ε : ℝ) (D : (Fin g' → ℂ) ≃L[ℂ] (Fin g' → ℂ))
        (F : (Fin g' → ℂ) → (Fin g' → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g' => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) v₀)

    (hSURJ' : ∀ (v₀ : Fin g' → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G'.Opens) (fs : Finset (Γ(G', U))) (ε : ℝ) (h₀ : ⊤ ≤ (e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f') (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e' P = (w : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

    (u : G ⟶ G') (hu : u ≫ f' = f)
    (hhom : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q)) :
    ∃! T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
      (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (v : Fin g → ℂ),
        e P = (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) →
        e' (mapPt u hu P) = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE.solution
