import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem NeronSpecialFibreInfra.exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
    {R : Type} [CommRing R] {κ : Type} [Field κ] [IsAlgClosed κ]
    (ι ι₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R))
    {G G₀ X₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}
    {f₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Lf₀ : RelativeGroupLaw R f₀)
    (hX₀ : AbelianSchemePropertyBundle κ (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    {t t₀ : ℕ}
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr κ t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀)) (hτ₀ : IsClosedImmersion τ₀.1)
    (hτ₀mul : ∀ χ χ' : WithConv (torusCoord κ t₀ →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ₀ =
        (L₀.baseChange ι₀).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ₀)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ₀))
    (abq₀ : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr ι₀ g₀) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (abq₀_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι₀).mul s x y) (abq₀ i) =
        (Lf₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (abq₀ i))
          (NeronModelInfra.schemeHomOverComp y (abq₀ i)))
    (abq₀_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abq₀ i) = (Lf₀.baseChange ι₀).one s) ↔
        ∃ y : SchemeHomOver s (torusStr κ t₀), NeronModelInfra.schemeHomOverComp y τ₀ = x)
    (Ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (hΨκ_mul : ∀ χ χ' : torusCoord κ t →ₐ[κ] κ,
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1) →
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) →
      NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ)) Ψκ =
        (L₀.baseChange ι₀).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) Ψκ)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ) Ψκ)) :
    ∃ M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ τ₀.1 = τ.1 ≫ Ψκ.1 := by p2m_exact_reverting @_root_.P2MW.S_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul.solution
