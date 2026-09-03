import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal IsLocalRing in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isProrepresentedBy_deformations_of_forall_bijective_algHom
    {q : ℕ} [Fact q.Prime]
    (O : Type u) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) q]
    (ι : Zp2 q →+* O) (X₀ : SpecialFormalODModule q ((residue O).comp ι))
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
      ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso),
      resA.comp (β A resA hs hc X w hw).toRingHom = resR)
    (hβ_iso : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (X' : FormalODModule q A) (w' : (X'.map resA).Hom X₀.toFormalODModule) (hw' : w'.IsIso)
        (v : X.Hom X'), v.IsIso → w'.toSeries.comp (v.toSeries.map resA) = w.toSeries →
      β A resA hs hc X w hw = β A resA hs hc X' w' hw')
    (hβ_nat : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type u) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
      ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (w' : ((X.map f.toRingHom).map resA').Hom X₀.toFormalODModule) (hw' : w'.IsIso),
        w'.toSeries = w.toSeries →
      β A' resA' hs' hc' (X.map f.toRingHom) w' hw' = f.comp (β A resA hs hc X w hw))
    (hβ_inj : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso)
        (X' : FormalODModule q A) (w' : (X'.map resA).Hom X₀.toFormalODModule) (hw' : w'.IsIso),
      β A resA hs hc X w hw = β A resA hs hc X' w' hw' →
      ∃ v : X.Hom X', v.IsIso ∧ w'.toSeries.comp (v.toSeries.map resA) = w.toSeries)
    (hβ_surj : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (χ : R →ₐ[O] A), resA.comp χ.toRingHom = resR →
      ∃ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule) (hw : w.IsIso),
        β A resA hs hc X w hw = χ) :
    ∃ (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (_ : wu.IsIso),
      ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ (X : FormalODModule q A) (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧
            ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
              (w.comp (v.map resA)).toSeries = wu.toSeries := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_isProrepresentedBy_deformations_of_forall_bijective_algHom.solution
