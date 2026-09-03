import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_connected_etale_sequence_padicInt
attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_connected_etale_sequence_padicInt
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] :
    ∃ (H₀ : Type) (_ : CommRing H₀) (_ : HopfAlgebra ℤ_[p] H₀) (Hₑ : Type) (_ : CommRing Hₑ)
      (_ : HopfAlgebra ℤ_[p] Hₑ) (π : H →ₐc[ℤ_[p]] H₀) (ι : Hₑ →ₐc[ℤ_[p]] H),
      Module.Finite ℤ_[p] H₀ ∧ Module.Free ℤ_[p] H₀ ∧ Coalgebra.IsCocomm ℤ_[p] H₀ ∧ IsLocalRing H₀ ∧
      Module.Finite ℤ_[p] Hₑ ∧ Module.Free ℤ_[p] Hₑ ∧ Coalgebra.IsCocomm ℤ_[p] Hₑ ∧
        Algebra.Etale ℤ_[p] Hₑ ∧
      Function.Surjective π ∧ (∃ e : H, IsIdempotentElem e ∧ RingHom.ker π = Ideal.span {e}) ∧
      Function.Injective ι ∧ (∀ x : H, x ∈ HopfAlgebra.hopfKer π ↔ x ∈ Set.range ι) ∧
      Module.finrank ℤ_[p] H = Module.finrank ℤ_[p] H₀ * Module.finrank ℤ_[p] Hₑ ∧
      Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] Hₑ ∧
      (∀ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) =
            (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) ↔
          ∃ g : H₀ →ₐ[ℤ_[p]] PadicAlgCl p, f = g.comp (π : H →ₐ[ℤ_[p]] H₀)) ∧
      (∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p, ∃ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) = h) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) (y : Hₑ), σ (h y) = h y) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_connected_etale_sequence_padicInt.solution
