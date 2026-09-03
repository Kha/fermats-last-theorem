import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ σ₀ : Spec (CommRingCat.of ↥A) ⟶ base p) (hσ : σ = σ₀)
    (L : RelativeGroupLaw (baseRing p) g) (L₀ : RelativeGroupLaw (baseRing p) g₀)
    (Ψ : SchemeHomOver g g₀) (Ψ' : SchemeHomOver g₀ g) (hΨΨ' : Ψ.1 ≫ Ψ'.1 = 𝟙 G) (hΨ'Ψ : Ψ'.1 ≫ Ψ.1 = 𝟙 G₀)
    (hΨ'mul : ∀ x y : SchemeHomOver (barPt A ≫ σ₀) g₀, NeronModelInfra.schemeHomOverComp (L₀.mul _ x y) Ψ' =
      L.mul _ (NeronModelInfra.schemeHomOverComp x Ψ') (NeronModelInfra.schemeHomOverComp y Ψ'))
    {t t₀ : ℕ} (m : ℕ) (hm : 0 < m)
    (ιm : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (ι₀m : SchemeHomOver (muStr ↥A t₀ m) (RelativeGroupLaw.baseChangeStr σ₀ g₀))
    (hιm_mul : ∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) ιm =
        (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) ιm)
          (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) ιm))
    (hι₀m_mul : ∀ χ χ' : WithConv (muCoord ↥A t₀ m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A t₀ m (χ * χ').ofConv) ι₀m =
        (L₀.baseChange σ₀).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ.ofConv) ι₀m)
          (NeronModelInfra.schemeHomOverComp (muPt A t₀ m χ'.ofConv) ι₀m))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (τ₀ : SchemeHomOver (torusStr (ResidueField ↥A) t₀) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ₀) g₀))
    (hιm_sp : muBaseChange (residue ↥A) t m ≫ ιm.1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (hι₀m_sp : muBaseChange (residue ↥A) t₀ m ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ =
      muToTorus (ResidueField ↥A) t₀ m ≫ τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀))
    (M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ τ₀.1 ≫
        pullback.fst g₀ (resPt A ≫ σ₀) = τ.1 ≫ pullback.fst g (resPt A ≫ σ) ≫ Ψ.1)
    (M₀' : (Fin t → ℤ) →+ (Fin t₀ → ℤ))
    (hM₀' : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀')) ≫ τ.1 ≫
        pullback.fst g (resPt A ≫ σ) = τ₀.1 ≫ pullback.fst g₀ (resPt A ≫ σ₀) ≫ Ψ'.1)
    (RIGID : ∀ u v : SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g),
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) u =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) u)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) u)) →
      (∀ χ χ' : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ),
        NeronModelInfra.schemeHomOverComp (muPt A t m (χ * χ').ofConv) v =
          (L.baseChange σ).mul _ (NeronModelInfra.schemeHomOverComp (muPt A t m χ.ofConv) v)
            (NeronModelInfra.schemeHomOverComp (muPt A t m χ'.ofConv) v)) →
      muBaseChange (residue ↥A) t m ≫ u.1 = muBaseChange (residue ↥A) t m ≫ v.1 → u = v) :
    ∃ Mbar : (Fin t₀ → ZMod m) →+ (Fin t → ZMod m),
      Mbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t₀ => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)).comp M₀ ∧
      ∀ χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ,
        (muPt A t m χ).1 ≫ ιm.1 ≫ pullback.fst g σ ≫ Ψ.1 =
          (muPt A t₀ m (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ ι₀m.1 ≫ pullback.fst g₀ σ₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_forall_muPt_comp_eq_comp_of_torusMatrix_of_rigid.solution
