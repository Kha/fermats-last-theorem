import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {n : ℕ} (σ : Fin n → Γ(M, ⊤))
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
        (x' : ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom sk)))),
        ∃ (t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤))
          (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom sk))).Opens), x' ∈ U' ∧ Scheme.Modules.IsFrameOn t U')
    (hspan : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k)
        (t : Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M, ⊤)),
        letI : Module k Γ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk)))).obj M,
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) :=
          Module.compHom _ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom sk))).appLE ⊤
              ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) ⁻¹ᵁ ⊤) le_top).hom
        ∃ c : Fin n → k, t = ∑ i, c i • Scheme.Modules.pullbackLocalSection (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom sk))) (σ i))
    (x : ↥X) :
    ∃ (i : Fin n) (U : X.Opens), x ∈ U ∧ Scheme.Modules.IsFrameOn (σ i) U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_forall_geometricFibre_exists_isFrameOn_of_forall_eq_sum_smul_pullbackLocalSection.solution
