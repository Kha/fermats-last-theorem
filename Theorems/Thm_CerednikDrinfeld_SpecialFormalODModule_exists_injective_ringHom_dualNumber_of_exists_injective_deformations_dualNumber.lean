import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    {r : ℕ}
    (htangent : ∃ (e : ∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
        (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule),
        w.IsIso → (Fin r → (IsLocalRing.ResidueField Onr))),

      (∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w' : (X'.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso) (v : X.Hom X'), v.IsIso →
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = w.toSeries →
        e X w hw = e X' w' hw') ∧

      (∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w' : (X'.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso),
        e X w hw = e X' w' hw' →
        ∃ v : X.Hom X', v.IsIso ∧
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = w.toSeries) ∧

      (∀ (c : (IsLocalRing.ResidueField Onr)) (μ : DualNumber (IsLocalRing.ResidueField Onr) →+* DualNumber (IsLocalRing.ResidueField Onr)),
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp μ = (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom →
          (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (w' : ((X.map μ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso), w'.toSeries = w.toSeries →
        e (X.map μ) w' hw' = c • e X w hw) ∧

      (∀ (B : Type) [CommRing B] (resB : B →+* (IsLocalRing.ResidueField Onr)), Function.Surjective resB → IsLocalHom resB →
        ∀ (p₁ p₂ σ : B →+* DualNumber (IsLocalRing.ResidueField Onr)),
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp p₁ = resB →
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp p₂ = resB →
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp σ = resB →
          (∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso →
        ∀ (w₁ : ((Y.map p₁).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw₁ : w₁.IsIso)
          (w₂ : ((Y.map p₂).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw₂ : w₂.IsIso)
          (wσ : ((Y.map σ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hwσ : wσ.IsIso),
          w₁.toSeries = u.toSeries → w₂.toSeries = u.toSeries → wσ.toSeries = u.toSeries →
        e (Y.map σ) wσ hwσ = e (Y.map p₁) w₁ hw₁ + e (Y.map p₂) w₂ hw₂)) :
    ∃ e' : (R →+* DualNumber (IsLocalRing.ResidueField Onr)) → (Fin r → IsLocalRing.ResidueField Onr),
      (∀ χ χ' : R →+* DualNumber (IsLocalRing.ResidueField Onr),
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ' = resR ∧ χ'.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        e' χ = e' χ' → χ = χ') ∧
      (∀ (c : IsLocalRing.ResidueField Onr) (μ : DualNumber (IsLocalRing.ResidueField Onr) →+* DualNumber (IsLocalRing.ResidueField Onr)),
        (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp μ = (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom →
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
          e' (μ.comp χ) = c • e' χ) ∧
      (∀ χ₁ χ₂ χ₃ : R →+* DualNumber (IsLocalRing.ResidueField Onr),
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₁ = resR ∧ χ₁.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₂ = resR ∧ χ₂.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₃ = resR ∧ χ₃.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        (∀ x, TrivSqZeroExt.snd (χ₃ x) = TrivSqZeroExt.snd (χ₁ x) + TrivSqZeroExt.snd (χ₂ x)) →
          e' χ₃ = e' χ₁ + e' χ₂) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber.solution
