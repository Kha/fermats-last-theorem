import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKer_kerPairLaw_baseChange

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isPullback_schemeKer_kerPairLaw_baseChange
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (ι' : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
    (hφ : ∀ i, RelativeGroupLaw.IsHom G G' (φ i)) (m : ℕ) :
    letI L' := RelativeGroupLaw.kerPairLaw (G.baseChange ι) (G'.baseChange ι)
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong ι f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong ι (hφ i))
    letI L'' := RelativeGroupLaw.kerPairLaw (G.baseChange (ι' ≫ ι)) (G'.baseChange (ι' ≫ ι))
      (fun i => NeronSpecialFibreInfra.fibreRestrictAlong (ι' ≫ ι) f' f (φ i))
      (fun i => RelativeGroupLaw.IsHom.fibreRestrictAlong (ι' ≫ ι) (hφ i))
    ∃ π : L''.schemeKer m ⟶ L'.schemeKer m, IsPullback π (L''.schemeKerStr m) (L'.schemeKerStr m) ι' := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isPullback_schemeKer_kerPairLaw_baseChange.solution
