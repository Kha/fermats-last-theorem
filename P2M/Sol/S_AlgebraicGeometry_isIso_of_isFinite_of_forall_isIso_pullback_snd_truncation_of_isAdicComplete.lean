import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_forall_isIso_pullback_snd_truncation_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (h : Γ ⟶ X) [IsFinite h]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (hn : ∀ n : ℕ, IsIso (Limits.pullback.snd h (Limits.pullback.fst f (sR n)))) :
    IsIso h := by
  haveI : IsClosedImmersion h :=
    AlgebraicGeometry.isClosedImmersion_of_isFinite_of_forall_isClosedImmersion_pullback_snd_truncation_of_isAdicComplete
      R I f h sR hsR (fun n => by haveI := hn n; infer_instance)
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
    R I f sR hsR h.ker fun n => ?_
  haveI := hn n
  have : pullback.fst f (sR n) = (inv (pullback.snd h (pullback.fst f (sR n))) ≫ pullback.fst h (pullback.fst f (sR n))) ≫ h := by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  rw [this]
  exact Scheme.Hom.le_ker_comp _ _
