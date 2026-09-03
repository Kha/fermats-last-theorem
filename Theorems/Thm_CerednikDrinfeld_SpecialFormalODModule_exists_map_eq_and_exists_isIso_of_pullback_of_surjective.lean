import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    {B A' A'' A : Type u} [CommRing B] [CommRing A'] [CommRing A''] [CommRing A]
    (p' : B →+* A') (p'' : B →+* A'') (q' : A' →+* A) (q'' : A'' →+* A)
    (hcomm : q'.comp p' = q''.comp p'')
    (hpb : ∀ (a' : A') (a'' : A''), q' a' = q'' a'' → ∃! b : B, p' b = a' ∧ p'' b = a'')
    (hq'' : Function.Surjective q'') (hq''loc : IsLocalHom q'')
    (resB : B →+* k) (resA' : A' →+* k) (resA'' : A'' →+* k) (resA : A →+* k)
    (hresA' : resA'.comp p' = resB) (hresA'' : resA''.comp p'' = resB)
    (hresq' : resA.comp q' = resA') (hresq'' : resA.comp q'' = resA'')
    (hresA : Function.Surjective resA) (hnil : IsNilpotent (RingHom.ker resA)) :
    (∀ (X' : FormalODModule q A') (w' : (X'.map resA').Hom X₀.toFormalODModule), w'.IsIso →
      ∀ (X'' : FormalODModule q A'') (w'' : (X''.map resA'').Hom X₀.toFormalODModule), w''.IsIso →
      ∀ (φ : (X'.map q').Hom (X''.map q'')), φ.IsIso →
        w''.toSeries.comp (φ.toSeries.map resA) = w'.toSeries →
        ∃ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso ∧
          Y.map p' = X' ∧ u.toSeries = w'.toSeries ∧
          ∃ v : (Y.map p'').Hom X'', v.IsIso ∧ v.toSeries.map q'' = φ.toSeries ∧
            w''.toSeries.comp (v.toSeries.map resA'') = u.toSeries) ∧
    (∀ (Y₁ : FormalODModule q B) (u₁ : (Y₁.map resB).Hom X₀.toFormalODModule), u₁.IsIso →
      ∀ (Y₂ : FormalODModule q B) (u₂ : (Y₂.map resB).Hom X₀.toFormalODModule), u₂.IsIso →
      ∀ (v' : (Y₁.map p').Hom (Y₂.map p')), v'.IsIso →
        u₂.toSeries.comp (v'.toSeries.map resA') = u₁.toSeries →
      ∀ (v'' : (Y₁.map p'').Hom (Y₂.map p'')), v''.IsIso →
        u₂.toSeries.comp (v''.toSeries.map resA'') = u₁.toSeries →
        ∃ v : Y₁.Hom Y₂, v.IsIso ∧ v.toSeries.map p' = v'.toSeries ∧
          v.toSeries.map p'' = v''.toSeries ∧
          u₂.toSeries.comp (v.toSeries.map resB) = u₁.toSeries) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.solution
