import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.IsCanonicalPolData.exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓜 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) (h𝓜 : IsCanonicalPolData f L act act_over star 𝓜) :
    ∃ (k'' : Type) (_ : Field k'') (_ : IsAlgClosed k'') (_ : Algebra k k''),
      ∀ {A'' : Scheme} (f'' : A'' ⟶ Spec (CommRingCat.of k'')) (g : A'' ⟶ A)
        (hg : IsPullback g f'' f (Spec.map (CommRingCat.ofHom (algebraMap k k''))))
        (L'' : RelativeGroupLaw k'' f''),
        (∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of k'')) (P Q : SchemeHomOver t' f''),
            (L''.mul t' P Q).1 ≫ g =
              (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'')))
                ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) →
        (∃ 𝓛₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial f'' L'' 𝓛₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛) (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₁)) ∧
        (∃ 𝓜₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓜₁ ∧ KernelTrivial f'' L'' 𝓜₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓜) (𝓜₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓜₁)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair.solution
