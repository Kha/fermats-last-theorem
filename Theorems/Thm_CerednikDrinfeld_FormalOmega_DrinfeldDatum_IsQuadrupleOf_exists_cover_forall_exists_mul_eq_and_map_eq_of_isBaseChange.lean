import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
attribute [-instance] CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsQuadrupleOf.exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) [Finite (𝒪 ⧸ Ideal.span {π})]
    {B B' : Type} [CommRing B] [CommRing B'] [Algebra 𝒪 B] [Algebra 𝒪 B']
    (φ : B' →ₐ[𝒪] B) (hφs : Function.Surjective φ) (hφn : IsNilpotent (RingHom.ker (φ : B' →+* B)))
    (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    {Q : DrinfeldDatum (K := K) π B} {d : DeligneDatum (K := K) π B} (hQ : Q.IsQuadrupleOf d)
    (e₀ : Q.T₀) (e₁ : Q.T₁)
    (he₀ : ∀ t : Q.T₀, ∃! b : B, t = b • e₀) (he₁ : ∀ t : Q.T₁, ∃! b : B, t = b • e₁)
    (α β : B) (hα : Q.Pi₀ e₀ = α • e₁) (hβ : Q.Pi₁ e₁ = β • e₀)
    (d' : DeligneDatum (K := K) π B')
    (hd' : DeligneDatum.IsBaseChange (K := K) (π := π) φ d' d) :
    ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L' : Type) [CommRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
        (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
        (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B)),
        ∃ α' β' : L', φL α' = algebraMap B L α ∧ φL β' = algebraMap B L β ∧
          α' * β' = algebraMap B' L' (algebraMap 𝒪 B' π) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_IsQuadrupleOf_exists_cover_forall_exists_mul_eq_and_map_eq_of_isBaseChange.solution
