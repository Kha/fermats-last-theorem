import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (U : G.Opens) (W : (pullback f f).Opens)
    (hWm : W ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ U)
    (hW₁ : W ≤ pullback.fst f f ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd f f ⁻¹ᵁ U)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ U)
    (hee : pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec (CommRingCat.of k)))).1 rfl
      (IsLocalRing.closedPoint k) ∈ W)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk _)) :
    ((pullback f f).presheaf.germ W _ hee).hom
        (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.appLE U W hWm).hom φ
          - ((pullback.fst f f).appLE U W hW₁).hom φ - ((pullback.snd f f).appLE U W hW₂).hom φ)
      ∈ IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk _) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq.solution
