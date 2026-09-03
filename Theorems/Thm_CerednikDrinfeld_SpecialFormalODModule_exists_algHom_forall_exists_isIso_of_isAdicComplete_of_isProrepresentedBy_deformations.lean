import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
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
    (B' : Type) [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] [Algebra Onr B']
    [IsAdicComplete (IsLocalRing.maximalIdeal B') B']
    (resB : B' →+* IsLocalRing.ResidueField Onr) (hresB : Function.Surjective resB)
    (hresB' : resB.comp (algebraMap Onr B') = IsLocalRing.residue Onr)
    (X' : FormalODModule q B') (w' : (X'.map resB).Hom X₀.toFormalODModule) (hw' : w'.IsIso) :
    ∃ χ : R →ₐ[Onr] B', resB.comp χ.toRingHom = resR ∧
      ∀ n : ℕ, 0 < n →
        ∃ v : (Xu.map ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n)).comp χ.toRingHom)).Hom
            (X'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n))),
          v.IsIso ∧
          ∀ (resn : B' ⧸ IsLocalRing.maximalIdeal B' ^ n →+* IsLocalRing.ResidueField Onr),
            resn.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n)) = resB →
            (w'.toSeries).comp (v.toSeries.map resn) = wu.toSeries := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations.solution
