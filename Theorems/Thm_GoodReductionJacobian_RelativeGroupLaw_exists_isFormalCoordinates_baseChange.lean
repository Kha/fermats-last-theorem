import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_baseChange
    {B B' : Type} [CommRing B] [CommRing B']
    (ι : Spec (CommRingCat.of B') ⟶ Spec (CommRingCat.of B))
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f d) (hθ : L.IsFormalCoordinates F θ) :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates (RelativeGroupLaw.baseChangeStr ι f) d,
      (L.baseChange ι).IsFormalCoordinates (F.map (Spec.preimage ι).hom) θ' ∧
      ∀ (C : Type) [CommRing C] [Algebra B' C] (s : Fin d → C),
        letI : Algebra B C := ((algebraMap B' C).comp (Spec.preimage ι).hom).toAlgebra
        (θ' C s).1 ≫ pullback.fst f ι = (θ C s).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_baseChange.solution
