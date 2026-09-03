import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
namespace P2MW.S_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : InfinitePlace E) :
    Nat.card {w : InfinitePlace K // w.comap (algebraMap E K) = v} *
      Nat.card (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) = Nat.card (K ≃ₐ[E] K) := by
  have h0 := NumberField.ArchIdele.comap_above E K v
  have e : {w : InfinitePlace K // w.comap (algebraMap E K) = v} ≃
      MulAction.orbit (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v) :=
    Equiv.subtypeEquivRight fun w => by
      rw [NumberField.InfinitePlace.mem_orbit_iff, h0, eq_comm]
  rw [Nat.card_congr e]
  change Nat.card (MulAction.orbit (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) *
      Nat.card (MulAction.stabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) = _
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v))
