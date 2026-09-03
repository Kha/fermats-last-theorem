import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
import P2M.Sol.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion
    {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {G G₀ : Scheme.{0}} {g : G ⟶ base p} {g₀ : G₀ ⟶ base p}
    (σ : Spec (CommRingCat.of ↥A) ⟶ base p) [IsSeparated g] [IsSeparated g₀]
    (L Lc : RelativeGroupLaw (baseRing p) g) (L₀ Lc₀ : RelativeGroupLaw (baseRing p) g₀) (Ψ : SchemeHomOver g g₀)
    (hΨc : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s g),
      NeronModelInfra.schemeHomOverComp (Lc.mul s x y) Ψ =
        Lc₀.mul s (NeronModelInfra.schemeHomOverComp x Ψ) (NeronModelInfra.schemeHomOverComp y Ψ))
    (hL : ∀ a b : SchemeHomOver (barPt A ≫ σ) g, L.mul _ a b = Lc.mul _ a b)
    (hL₀ : ∀ a b : SchemeHomOver (barPt A ≫ σ) g₀, L₀.mul _ a b = Lc₀.mul _ a b)
    {t : ℕ} (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ σ) g))
    (ιm : ∀ m : ℕ, 0 < m → SchemeHomOver (muStr ↥A t m) (RelativeGroupLaw.baseChangeStr σ g))
    (hιm_sp : ∀ (m : ℕ) (hm : 0 < m), muBaseChange (residue ↥A) t m ≫ (ιm m hm).1 ≫ pullback.fst g σ =
      muToTorus (ResidueField ↥A) t m ≫ τ.1 ≫ pullback.fst g (resPt A ≫ σ))
    (χ χ' : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hχ : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1)
    (hχ' : ∃ n : ℕ, (n : ResidueField ↥A) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) :
    NeronModelInfra.schemeHomOverComp ((L.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ))
        (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ) =
      (L₀.baseChange (resPt A ≫ σ)).mul (𝟙 _)
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ) τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ))
        (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt _ t χ') τ) (fibreRestrictAlong (resPt A ≫ σ) g₀ g Ψ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOverComp_mul_torusPt_fibreRestrictAlong_of_torsion.solution
