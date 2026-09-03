import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
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
    (hnode₀ : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (hnode₁ : (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (e₀ e₁ : Xu.Lie) (u v : R)
    (he₀ : e₀ ∈ Xu.lieZero ((algebraMap Onr R).comp ι)) (he₁ : e₁ ∈ Xu.lieOne ((algebraMap Onr R).comp ι))
    (hbasis : ∀ m : Xu.Lie, ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁)
    (hu : Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₀ = u • e₁) (hv : Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₁ = v • e₀)
    (χ χ' : R →+* DualNumber (IsLocalRing.ResidueField Onr))
    (hχ : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)))
    (hχ' : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ' = resR ∧ χ'.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)))
    (hχu : χ u = χ' u) (hχv : χ v = χ' v) :
    χ = χ' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.solution
