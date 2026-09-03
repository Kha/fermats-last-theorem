import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor
import P2M.Util
import P2M.Sol.S_CuspForm_IsNewform_exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio
attribute [-instance] FLT.SpectralSide.instCompactSpaceMatrix
attribute [-simp] AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.rightTranslationEmbed_smul_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (K : Type) [Field K] [CharZero K]
    (φ : chig.range →+* K)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hratio : LocalNewvector.IsUnramified q (μ₁⁻¹ * μ₂)) :
    ∃ (m : ℕ) (_ : NeZero m), ((Odd q ∧ m = q) ∨ (q = 2 ∧ m = 8)) ∧
    ∃ (χ : (ZMod m)ˣ →* Kˣ), (∀ u : (ZMod m)ˣ, χ u * χ u = 1) ∧ χ ≠ 1 ∧
    ∃ (M' : ℕ) (_ : NeZero M'),
    ∃ (h : CuspForm (CongruenceSubgroup.Gamma0 M') 2), h.IsNewform ∧ ¬ q ^ 2 ∣ M' ∧
    ∃ (S' : Finset ℕ) (chih : CuspForm.heckeAlgebra M' 2 (↑S' : Set ℕ) →+* ℂ),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S' : Set ℕ)),
        chih (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff h ℓ) ∧
    ∃ (φ' : chih.range →+* K),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ)))
          (hℓN' : ¬ ℓ ∣ M') (hℓS' : ℓ ∉ ((S' : Set ℕ))) (hℓm : Nat.Coprime ℓ m),
        φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) =
          (χ (ZMod.unitOfCoprime ℓ hℓm) : K) *
            φ' (chih.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN' hℓS')) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_IsNewform_exists_quadraticTwistToExponentOne_of_sq_dvd_of_adelicLift_principalSeries_isUnramified_ratio.solution
