import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (U₀ : P.Opens) (hU₀ : IsAffineOpen U₀) (r : ℕ)
    (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀) (hpr : Function.Surjective pr)
    (δ : ↥(LinearMap.ker pr) →ₗ[Γ(P, U₀)] GK.obj U₀) :
    ∃ (prU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        (Fin r → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (v : Fin r → Γ(P, U₀)),
        prU U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr v))
      (_hprUs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (prU U))
      (_hprUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        prU U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU U v))
      (gU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker pr) → ↥(LinearMap.ker (prU U)))
      (_hgU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)) (m : Fin r),
        ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin r → Γ(P, U₀)) m))
      (δU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker (prU U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)),
        δU U (gU U s) = GK.res U.2 (δ s))
      (_hgUspan : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker pr) =>
              ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1))) =
          LinearMap.ker (prU U))
      (_hδUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U'))),
        (∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin r → Γ(P, U.1.1)) m)) →
        δU U' s' = GK.res h (δU U s)),
    letI : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module A (LinearMap.ExtPushout (prU U) (δU U)) :=
      fun U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (_ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1
          IsScalarTower A Γ(P, U.1.1) (LinearMap.ExtPushout (prU U) (δU U)))
      (res : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}}, U'.1.1 ≤ U.1.1 → (LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] LinearMap.ExtPushout (prU U') (δU U')))
      (res_smul : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)),
          res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (res_refl : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)), res (le_refl U.1.1) x = x)
      (res_comp : ∀ {U U' U'' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : LinearMap.ExtPushout (prU U) (δU U)), res (h.trans h') x = res h (res h' x))
      (hqc : ∀ (U Ug : {U : P.affineOpens // U.1 ≤ U₀}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : LinearMap.ExtPushout (prU Ug) (δU Ug), ∃ (n : ℕ) (x : LinearMap.ExtPushout (prU U) (δU U)),
              res (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : LinearMap.ExtPushout (prU U) (δU U), res (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module.Finite (Γ(P, U.1.1) : Type u) (LinearMap.ExtPushout (prU U) (δU U)))
      (ϑ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), GK.obj U.1.1 →ₗ[A] LinearMap.ExtPushout (prU U) (δU U))
      (θE : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] GE.obj U.1.1)
            (hϑs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ U (a • x) = a • ϑ U x)
      (hθEs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)), θE U (a • x) = a • θE U x)
            (hϑn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ U' (GK.res h x) = res h (ϑ U x))
      (hθEn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : LinearMap.ExtPushout (prU U) (δU U)),
          θE U' (res h x) = GE.res h (θE U x))
            (hexact : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.range (ϑ U) = LinearMap.ker (θE U))
      (hsurj : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (θE U))
      (hϑi : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Injective (ϑ U)),

      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : GK.obj U.1.1),
        ϑ U x = LinearMap.ExtPushout.inl (prU U) (δU U) x) ∧
      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)),
        θE U x = LinearMap.ExtPushout.proj (prU U) (δU U) x) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res h (LinearMap.ExtPushout.inl (prU U) (δU U) n) = LinearMap.ExtPushout.inl (prU U') (δU U') (GK.res h n)) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        res h (LinearMap.ExtPushout.inr (prU U) (δU U) v) =
          LinearMap.ExtPushout.inr (prU U') (δU U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution
