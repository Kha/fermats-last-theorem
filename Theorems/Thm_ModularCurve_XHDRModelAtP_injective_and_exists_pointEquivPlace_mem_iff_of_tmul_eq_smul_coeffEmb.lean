import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

theorem ModularCurve.XHDRModelAtP.injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥Pl] (halg : algebraMap (R p) ↥Pl = ρ)

    (B : Subalgebra (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (ιB : Spec (CommRingCat.of ↥B) ⟶ X p (ΓM M H) hj) [IsOpenImmersion ιB]
    (hιB : ιB ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) ↥B)))

    (hne : Nonempty (Scheme.Opens.toScheme ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ (ιB ''ᵁ ⊤))))
    (hMeta : ∀ b : ↥B, haveI := hne
      ((𝔛.Meta.ffEquiv.symm
        (𝔛.Meta.C.germToFunctionField
          ((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            (ιB ''ᵁ ⊤))
          (((𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              (ιB ''ᵁ ⊤)).hom
            ((ιB.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥B)).inv b))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))

    (γ : ↥Pl ⊗[R p] ↥B →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (α : ↥Pl) (b : ↥B), ((γ (α ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (α : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ))) :

    Function.Injective γ ∧

    (∀ e : ↥(xHFunctionFieldBar M H), ∃ a s : ↥Pl ⊗[R p] ↥B, s ≠ 0 ∧ e * γ s = γ a) ∧

    (∀ 𝔮 : Ideal (↥Pl ⊗[R p] ↥B), 𝔮.IsPrime →
      𝔮.comap (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = ⊥ → 𝔮 ≠ ⊥ →
      ∃ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (χ : ↥Pl ⊗[R p] ↥B →+* AlgebraicClosure ℚ),
        (∀ e : ↥(xHFunctionFieldBar M H),
          e ∈ (𝔛.Meta.pointEquivPlace y).toValuationSubring ↔ ∃ a s : ↥Pl ⊗[R p] ↥B, s ∉ 𝔮 ∧ e * γ s = γ a) ∧
        χ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥Pl) (B := ↥B)) = Pl.subtype ∧
        RingHom.ker χ = 𝔮 ∧
        y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥Pl) (B := ↥B)).toRingHom) ≫ ιB) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_injective_and_exists_pointEquivPlace_mem_iff_of_tmul_eq_smul_coeffEmb.solution
