import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 πM)
    (σ : Spec (CommRingCat.of ℂ) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U)
      (inst : Algebra ℂ ↑(M.presheaf.obj (op U))),

      (∀ z : ℂ, algebraMap ℂ ↑(M.presheaf.obj (op U)) z =
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (πM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z))) ∧
      IsDomain ↑(M.presheaf.obj (op U)) ∧ Algebra.FiniteType ℂ ↑(M.presheaf.obj (op U)) ∧
      Algebra.Smooth ℂ ↑(M.presheaf.obj (op U)) ∧
      Module.rank ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U))) = 1 ∧
      ∃ (σ₀ : ↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ) (t : ↑(M.presheaf.obj (op U))),
        (∀ s : ↑(M.presheaf.obj (op U)),
          σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((σ.appLE U ⊤ hσU).hom s)) ∧
        KaehlerDifferential.D ℂ ↑(M.presheaf.obj (op U)) t ∉
          (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U)))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point.solution
