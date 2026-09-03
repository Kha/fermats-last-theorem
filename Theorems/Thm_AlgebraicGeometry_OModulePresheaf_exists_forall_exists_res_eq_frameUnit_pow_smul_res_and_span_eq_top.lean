import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    {π : X ⟶ Spec (CommRingCat.of A)} (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ (m : ℕ) (s : Fin m → ∀ i : Fin (N + 1), F.obj (ProjSpace.pullbackChart φ i)),
        (∀ (a : Fin m) (i j : Fin (N + 1)),
          F.res (ProjSpace.pullbackOverlap_le_left φ i j) (s a i) =
            ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j) ^ d •
              F.res (ProjSpace.pullbackOverlap_le_right φ i j) (s a j)) ∧
        ∀ i : Fin (N + 1),
          Submodule.span Γ(X, ProjSpace.pullbackChart φ i) (Set.range fun a : Fin m => s a i) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.solution
