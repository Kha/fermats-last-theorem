import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_of_forall_isBaseChangeAlong_away
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : DrinfeldDatum (K := K) π B) (d : DeligneDatum (K := K) π B)
    (Qf : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (hbc : ∀ i : Fin k, Q.IsBaseChangeAlong (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))) (Qf i))
    (hQf : ∀ i : Fin k, (Qf i).IsQuadrupleOf (d.map π (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f i))))) :
    Q.IsQuadrupleOf d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_of_forall_isBaseChangeAlong_away.solution
