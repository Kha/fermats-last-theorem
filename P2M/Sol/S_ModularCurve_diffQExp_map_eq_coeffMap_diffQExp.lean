import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
namespace P2MW.S_ModularCurve_diffQExp_map_eq_coeffMap_diffQExp

set_option autoImplicit false

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_coeff qEuler qEuler_coeff diffQExp diffQExp_D diffQExp_smul_D"
p2m_open "ModularCurve"

theorem coeffMap_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f (qEuler R x) = qEuler S (coeffMap f x) := by
  ext n
  simp [coeffMap_coeff, qEuler_coeff, map_mul]

end ModularCurve

theorem solution
    (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))
    [Algebra ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)] [Algebra k ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [IsScalarTower k K ↥(ModularCurve.qExpFunctionFieldC K Γ)] [IsScalarTower k ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    [SMulCommClass K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k Γ),
      ((algebraMap ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) =
        ModularCurve.coeffMap (algebraMap k K) (x : LaurentSeries k))
    (ω : Ω[↥(ModularCurve.qExpFunctionFieldC k Γ)⁄k]) :
    ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ) (KaehlerDifferential.map k K ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) ω) =
      ModularCurve.coeffMap (algebraMap k K) (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC k Γ) ω) := by

  have hmem : ω ∈ Submodule.span ↥(ModularCurve.qExpFunctionFieldC k Γ)
      (Set.range (KaehlerDifferential.D k ↥(ModularCurve.qExpFunctionFieldC k Γ))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem ω h =>
    obtain ⟨x, rfl⟩ := h
    rw [KaehlerDifferential.map_D, ModularCurve.diffQExp_D, ModularCurve.diffQExp_D, hι, ModularCurve.coeffMap_qEuler]
  | zero => simp only [map_zero]
  | add ω₁ ω₂ _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
  | smul f ω _ h =>
    rw [(KaehlerDifferential.map k K _ _).map_smul, (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC k Γ)).map_smul,
      ← IsScalarTower.algebraMap_smul ↥(ModularCurve.qExpFunctionFieldC K Γ) f,
      (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ)).map_smul, h]
    show ((algebraMap ↥(ModularCurve.qExpFunctionFieldC k Γ) ↥(ModularCurve.qExpFunctionFieldC K Γ) f :
        ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) * _ =
      ModularCurve.coeffMap (algebraMap k K) ((f : LaurentSeries k) * _)
    rw [map_mul, hι]
