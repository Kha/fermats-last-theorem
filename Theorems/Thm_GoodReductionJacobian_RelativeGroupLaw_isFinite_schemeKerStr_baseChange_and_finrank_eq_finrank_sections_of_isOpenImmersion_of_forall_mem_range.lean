import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
attribute [-simp] GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range
    {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {R' : Type} [CommRing R'] [IsLocalRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {k : Type} [Field k] (π : R' →+* k) (hker : ∀ x : R', π x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R')
    (c : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (hc : Spec.map (CommRingCat.ofHom π) ≫ ι = c)
    (n : ℕ) (A : Type) [CommRing A] [Algebra R' A] [Module.Finite R' A] [Module.Free R' A]
    (j : Spec (CommRingCat.of A) ⟶ (L.baseChange ι).schemeKer n)
    (hj : j ≫ (L.baseChange ι).schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap R' A)))
    (hjo : IsOpenImmersion j) (hjc : IsClosedImmersion j)
    (hcov : ∀ x : ↥((L.baseChange ι).schemeKer n),
      ((L.baseChange ι).schemeKerStr n).base x = IsLocalRing.closedPoint R' → x ∈ Set.range j.base) :
    IsFinite ((L.baseChange c).schemeKerStr n) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((L.baseChange c).schemeKerStr n) ⊤
     Module.finrank R' A = Module.finrank k Γ((L.baseChange c).schemeKer n, ⊤)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_baseChange_and_finrank_eq_finrank_sections_of_isOpenImmersion_of_forall_mem_range.solution
