import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
    {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B)) [IsSeparated ϖ]
    (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s))
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hfin : (OModulePresheaf.ofModules ϖ N).CechFinite 𝔚)
    (hfib : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal),
      (OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
          ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).H0
          (𝔚.baseChange ϖ (B ⧸ 𝔪)) = ⊥ ∧
        ∀ i, Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
            ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).HSucc
            (𝔚.baseChange ϖ (B ⧸ 𝔪)) i)) :
    (OModulePresheaf.ofModules ϖ N).H0 𝔚 = ⊥ ∧ ∀ i, Subsingleton ((OModulePresheaf.ofModules ϖ N).HSucc 𝔚 i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient.solution
