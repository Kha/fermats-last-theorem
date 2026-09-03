import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_comp

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hψφ : (ψ.comp φ).toRingHom.IsIntegral)
    (D : Divisor K F'') :
    Divisor.pushforwardAlong (ψ.comp φ) hψφ D =
      Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) := by
  letI iφ : Algebra F F' := algebraAlong φ
  letI iψ : Algebra F' F'' := algebraAlong ψ
  letI iψφ : Algebra F F'' := algebraAlong (ψ.comp φ)
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  haveI : IsScalarTower K F' F'' := isScalarTower_along ψ
  haveI : IsScalarTower K F F'' := isScalarTower_along (ψ.comp φ)
  haveI : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  haveI : Algebra.IsIntegral F' F'' := isIntegral_along ψ hψ
  haveI : Algebra.IsIntegral F F'' := isIntegral_along (ψ.comp φ) hψφ
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun x => rfl

  show Divisor.pushforward F D = Divisor.pushforward F (Divisor.pushforward F' D)

  have hres : ∀ w : Place K F'', (w.restrict F').restrict F = w.restrict F := fun _ => rfl

  have hdeg : ∀ w : Place K F'', (w.restrict F').inertiaDeg F * w.inertiaDeg F' = w.inertiaDeg F := by
    intro w

    letI iFF' : Algebra (w.restrict F).ResidueField (w.restrict F').ResidueField :=
      Place.instAlgebraResidueFieldRestrictPushforward (F := F) (w.restrict F')
    haveI : IsScalarTower (w.restrict F).ResidueField (w.restrict F').ResidueField w.ResidueField := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      change Place.restrictResidueMap F w (IsLocalRing.residue _ a) =
        Place.restrictResidueMap F' w (Place.restrictResidueMap F (w.restrict F') (IsLocalRing.residue _ a))
      rw [Place.restrictResidueMap_residue, Place.restrictResidueMap_residue, Place.restrictResidueMap_residue]
      congr 1
    have h := Module.finrank_mul_finrank (w.restrict F).ResidueField (w.restrict F').ResidueField w.ResidueField
    exact h
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, Divisor.pushforward_single, Divisor.pushforward_single,
      Divisor.pushforward_single, hres w, ← hdeg w, Nat.cast_mul]
    congr 1
    ring_nf
