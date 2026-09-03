import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.exists_forall_pullback_iso_of_cocycle
    {Y : Scheme.{u}} {I : Type u} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ y : ↥Y, ∃ (i : I) (x : ↥(X i)), (ι i).base x = y)
    (M : ∀ i, (X i).Modules)
    (φ : ∀ i j : I,
      (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).obj (M i) ≅
        (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).obj (M j))
    (hcocycle : ∀ (i j l : I) (T : Scheme.{u})
      (π₁₂ : T ⟶ Limits.pullback (ι i) (ι j)) (π₂₃ : T ⟶ Limits.pullback (ι j) (ι l)) (π₁₃ : T ⟶ Limits.pullback (ι i) (ι l))
      (h₂ : π₁₂ ≫ Limits.pullback.snd (ι i) (ι j) = π₂₃ ≫ Limits.pullback.fst (ι j) (ι l))
      (h₁ : π₁₃ ≫ Limits.pullback.fst (ι i) (ι l) = π₁₂ ≫ Limits.pullback.fst (ι i) (ι j))
      (h₃ : π₁₃ ≫ Limits.pullback.snd (ι i) (ι l) = π₂₃ ≫ Limits.pullback.snd (ι j) (ι l)),

      ((Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.fst (ι i) (ι j))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₂).mapIso (φ i j) ≪≫
          (Scheme.Modules.pullbackComp π₁₂ (Limits.pullback.snd (ι i) (ι j))).app (M j) ≪≫
          (Scheme.Modules.pullbackCongr h₂).app (M j) ≪≫
          ((Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.fst (ι j) (ι l))).app (M j)).symm ≪≫
          (Scheme.Modules.pullback π₂₃).mapIso (φ j l) ≪≫
          (Scheme.Modules.pullbackComp π₂₃ (Limits.pullback.snd (ι j) (ι l))).app (M l) ≪≫
          (Scheme.Modules.pullbackCongr h₃.symm).app (M l)
        = (Scheme.Modules.pullbackCongr h₁.symm).app (M i) ≪≫
          ((Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.fst (ι i) (ι l))).app (M i)).symm ≪≫
          (Scheme.Modules.pullback π₁₃).mapIso (φ i l) ≪≫
          (Scheme.Modules.pullbackComp π₁₃ (Limits.pullback.snd (ι i) (ι l))).app (M l)) :
    ∃ (Mg : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i),
      ∀ i j : I,
        ((Scheme.Modules.pullbackComp (Limits.pullback.fst (ι i) (ι j)) (ι i)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.fst (ι i) (ι j))).mapIso (ψ i) ≪≫ φ i j =
          (Scheme.Modules.pullbackCongr
              (Limits.pullback.condition : Limits.pullback.fst (ι i) (ι j) ≫ ι i = Limits.pullback.snd (ι i) (ι j) ≫ ι j)).app Mg ≪≫
            ((Scheme.Modules.pullbackComp (Limits.pullback.snd (ι i) (ι j)) (ι j)).app Mg).symm ≪≫
            (Scheme.Modules.pullback (Limits.pullback.snd (ι i) (ι j))).mapIso (ψ j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_forall_pullback_iso_of_cocycle.solution
