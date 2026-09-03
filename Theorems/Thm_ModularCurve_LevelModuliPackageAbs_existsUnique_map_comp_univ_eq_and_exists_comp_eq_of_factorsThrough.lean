import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import P2M.Util
import P2M.Sol.S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough

set_option autoImplicit false

universe u

open ModularCurve IsLocalRing

theorem ModularCurve.LevelModuliPackageAbs.existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)

    (R : Type u) [CommRing R] [Algebra A R] (ι : P.B₀ →ₐ[A] R)
    (k : Type u) [CommRing k] (resR : R →+* k)
    (W₀ : Type u) [CommRing W₀] (res₀ : W₀ →+* k) [Algebra W₀ R] [Algebra A W₀] [IsScalarTower A W₀ R]

    (hfac : ∀ (T : Type u) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A T] [IsScalarTower A W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P.B₀ →ₐ[A] T, (∀ b : P.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P.B₀, Φ (ι b) = φ b)

    (T : Type u) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T] [Algebra A T]
    [IsScalarTower A W₀ T]
    (resT : T →+* k) (hresT : Function.Surjective resT) (hkerT : RingHom.ker resT = maximalIdeal T)
    (hresT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) :

    (∀ y : D.Pt T, (∀ b : P.B₀, resT (P.classify y b) = resR (ι b)) →
      ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ D.map ((Φ.restrictScalars A).comp ι) P.univ = y) ∧
    (∀ Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) →
      ∀ b : P.B₀, resT (P.classify (D.map ((Φ.restrictScalars A).comp ι) P.univ) b) = resR (ι b)) ∧

    (∀ (T' : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T'] [Algebra A T']
        [IsScalarTower A W₀ T'] (resT' : T' →+* k), Function.Surjective resT' →
        RingHom.ker resT' = maximalIdeal T' → (∀ w : W₀, resT' (algebraMap W₀ T' w) = res₀ w) →
      ∀ π : T' →ₐ[W₀] T, (∀ t : T', resT (π t) = resT' t) →
      ∀ g : R →ₐ[W₀] T, (∀ r : R, resT (g r) = resR r) →
      ∀ y' : D.Pt T', D.map (π.restrictScalars A) y' = D.map ((g.restrictScalars A).comp ι) P.univ →
        ∃ g' : R →ₐ[W₀] T', (∀ r : R, resT' (g' r) = resR r) ∧ π.comp g' = g ∧
          D.map ((g'.restrictScalars A).comp ι) P.univ = y') ∧

    (∀ [Algebra A k] (ρT : T →ₐ[A] k) (ρ : P.B₀ →ₐ[A] k), (∀ t : T, ρT t = resT t) →
      (∀ b : P.B₀, ρ b = resR (ι b)) →
      ∀ y : D.Pt T, (∀ b : P.B₀, resT (P.classify y b) = resR (ι b)) ↔ D.map ρT y = D.map ρ P.univ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_LevelModuliPackageAbs_existsUnique_map_comp_univ_eq_and_exists_comp_eq_of_factorsThrough.solution
