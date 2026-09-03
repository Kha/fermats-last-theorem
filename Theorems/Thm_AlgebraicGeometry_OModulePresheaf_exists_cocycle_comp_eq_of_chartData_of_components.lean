import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_components
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (E : ℕ → OModulePresheaf q) (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (GE : OModulePresheaf q) (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (GK : OModulePresheaf q) (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    {ι : Type u} [LinearOrder ι] (Uc : ι → P.Opens)
    (M : ∀ i : ι, {U : P.affineOpens // U.1 ≤ Uc i} → Type u)
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), AddCommGroup (M i U)]
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), Module A (M i U)]
    [iΓ : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : ι) {U U' : {U : P.affineOpens // U.1 ≤ Uc i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (ϑ : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hc1 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
    (u : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : ι) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)

    (zC : ∀ (i j : ι), i < j → ∀ (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), GE.obj W.1.1 →ₗ[A] GK.obj W.1.1)
    (hzCs : ∀ (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (v : GE.obj W.1.1),
      zC i j hij W hj (a • v) = a • zC i j hij W hj v)
    (hzCn : ∀ (i j : ι) (hij : i < j) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (v : GE.obj W.1.1),
      zC i j hij W' (h.trans hj) (GE.res h v) = GK.res h (zC i j hij W hj v))
    (hzCc : ∀ (i j l : ι) (hij : i < j) (hjl : j < l) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (v : GE.obj W.1.1),
      zC i j hij W hj v + zC j l hjl ⟨W.1, hj⟩ hl v = zC i l (hij.trans hjl) W hl v)

    (YC : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), GE.obj U.1.1 →ₗ[A] GK.obj U.1.1)
    (hYs : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (v : GE.obj U.1.1), YC k i U (a • v) = a • YC k i U v)
    (hYn : ∀ (k : ℕ) (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (v : GE.obj U.1.1),
      YC k i U' (GE.res h v) = GK.res h (YC k i U v))
    (hY : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (v : GE.obj U.1.1), (lam k).app U.1 (YC (k + 1) i U v) = (lam k).app U.1 (YC k i U v))

    (tC : ∀ (k : ℕ) (i j : ι), i < j → ∀ (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), GE.obj W.1.1 →ₗ[A] GK.obj W.1.1)
    (ht : ∀ (k : ℕ) (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
      (lam k).app W.1 (tC k i j hij W hj (θE i W x)) = θF j k ⟨W.1, hj⟩ (u i j W hj x) - θF i k W x)
    (hzt : ∀ (k : ℕ) (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (v : GE.obj W.1.1),
      (lam k).app W.1 (zC i j hij W hj v) =
        (lam k).app W.1 (tC k i j hij W hj v) + (lam k).app W.1 (YC k j ⟨W.1, hj⟩ v) - (lam k).app W.1 (YC k i W v))
    :
    ∃ (θF'' : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] (F k).obj U.1.1),
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF'' i k U (a • x) = a • θF'' i k U x) ∧
      (∀ (i : ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF'' i k U' (res i h x) = (F k).res h (θF'' i k U x)) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (φ k).app U.1 ∘ₗ θF'' i (k + 1) U = θF'' i k U) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), θF'' i k U ∘ₗ ϑ i U = (lam k).app U.1) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (ε k).app U.1 ∘ₗ θF'' i k U = (ψE k).app U.1 ∘ₗ θE i U) ∧
    ∃ (u'' : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), Function.Bijective (u'' i j W hj)) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u'' i j W hj (a • x) = a • u'' i j W hj x) ∧
      (∀ (i j : ι) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u'' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u'' i j W hj x)) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : GK.obj W.1.1), u'' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W), θE j ⟨W.1, hj⟩ (u'' i j W hj x) = θE i W x) ∧

      (∀ (i j l : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (x : M i W),
        u'' j l ⟨W.1, hj⟩ hl (u'' i j W hj x) = u'' i l W hl x) ∧
      (∀ (i j : ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
        θF'' j k ⟨W.1, hj⟩ (u'' i j W hj x) = θF'' i k W x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution
