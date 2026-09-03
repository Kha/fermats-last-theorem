import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P] [IsSeparated q]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ'))

    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (hδ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
      X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j))))

    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
      (_hgUspan : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker (pr i)) =>
              ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1))) =
          LinearMap.ker (prU i U))
      (_hδUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU i U))) (s' : ↥(LinearMap.ker (prU i U'))),
        (∀ m : Fin (rk i), (s' : Fin (rk i) → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin (rk i) → Γ(P, U.1.1)) m)) →
        δU i U' s' = GK.res h (δU i U s))

      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 →
        LinearMap.ExtPushout (prU i U) (δU i U) → LinearMap.ExtPushout (prU i U') (δU i U'))
      (res_add : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (x y : LinearMap.ExtPushout (prU i U) (δU i U)),
        res i h (x + y) = res i h x + res i h y)
      (res_inl : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res i h (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = LinearMap.ExtPushout.inl (prU i U') (δU i U') (GK.res h n))
      (res_inr : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        res i h (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) =
          LinearMap.ExtPushout.inr (prU i U') (δU i U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) :
    letI : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
      fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), LinearMap.ExtPushout (prU i W) (δU i W) →ₗ[A] LinearMap.ExtPushout (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩))
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x)),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (LinearMap.ExtPushout.inl (prU i W) (δU i W) x) = LinearMap.ExtPushout.inl (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
        LinearMap.ExtPushout.proj (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) (u i j W hj x) = LinearMap.ExtPushout.proj (prU i W) (δU i W) x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution
