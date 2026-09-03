import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp
    {g d n : ℕ} {S C C' : Type u} [CommRing S] [CommRing C] [CommRing C'] (ρ : S →+* C) (σ : C →+* C')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n C) (v' : PolarisedAbelianScheme g d n C')
    (gv : v.A ⟶ u.A) (hgv : CategoryTheory.IsPullback gv v.f u.f (Spec.map (CommRingCat.ofHom ρ)))
    (hgvmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C)) (x y : SchemeHomOver t' v.f),
      (v.L.mul t' x y).1 ≫ gv =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨x.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, y.2]⟩).1)
    (hgvP : ∀ i, (v.P i).1 ≫ gv = Spec.map (CommRingCat.ofHom ρ) ≫ (u.P i).1)
    (hgvpol : Nonempty ((Scheme.Modules.pullback gv).obj u.pol ≅ v.pol))
    (gv' : v'.A ⟶ u.A) (hgv' : CategoryTheory.IsPullback gv' v'.f u.f (Spec.map (CommRingCat.ofHom (σ.comp ρ))))
    (hgv'mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
      (v'.L.mul t' x y).1 ≫ gv' =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ.comp ρ)))
          ⟨x.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, y.2]⟩).1)
    (hgv'P : ∀ i, (v'.P i).1 ≫ gv' = Spec.map (CommRingCat.ofHom (σ.comp ρ)) ≫ (u.P i).1)
    (hgv'pol : Nonempty ((Scheme.Modules.pullback gv').obj u.pol ≅ v'.pol)) :
    ∃ (c : v'.A ⟶ v.A) (_ : c ≫ gv = gv') (hc : CategoryTheory.IsPullback c v'.f v.f (Spec.map (CommRingCat.ofHom σ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
        (v'.L.mul t' x y).1 ≫ c =
          (v.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ i, (v'.P i).1 ≫ c = Spec.map (CommRingCat.ofHom σ) ≫ (v.P i).1) ∧
      Nonempty ((Scheme.Modules.pullback c).obj v.pol ≅ v'.pol) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp.solution
