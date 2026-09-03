import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
attribute [-simp] AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K), y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (((fun x : AdelicGL2 (𝓞 K) K → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y)) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (y) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero.solution
