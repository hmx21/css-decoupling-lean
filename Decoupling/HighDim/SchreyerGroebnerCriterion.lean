import Decoupling.HighDim.SchreyerGroebnerCriterionReduction
import Decoupling.HighDim.SchreyerGroebnerCriterionPairLift
import Decoupling.HighDim.SchreyerSyzygyCancellation

/-!
# The module Buchberger criterion from actual strict S-pair representations

Every lower-preimage witness is constructed from an actual normalized pair
lift. The final theorem has only ClosedPairs as a premise; zero generators,
empty families, finite fields and inhomogeneous vectors are all included.
This is mathematical correctness of completion, not an executable runtime claim.
-/
namespace Decoupling.HighDim.SchreyerModule
open SchreyerSyzygy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D r s : ℕ}

theorem ClosedPairs.isGroebnerBasis_of_leaders {o : ModuleOrder D r}
    {G : Fin s → Vec K D r} (hc : ClosedPairs o G)
    (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i)) :
    IsGroebnerBasis o G (Submodule.span (Poly K D) (Set.range G)) := by
  apply isGroebnerBasis_of_preimage_lowering o G t hG
  intro q u hq hzero
  obtain ⟨j,hij,hpos,hdiv⟩ := pair_divides_of_image_coeff_zero G t hG hq hzero
  obtain ⟨correction,he,hb⟩ := hc u.2 j (t u.2) (t j) (hG u.2) (hG j) hpos
  have hz := pairLift_leading G t hG u.2 j hij hpos correction hb
  have hker : (∑ i,(pairLift G t u.2 j correction) i • G i)=0 :=
    pairLift_kernel G t u.2 j correction he
  exact lower_preimage_of_kernel_leading G (inducedOrder o t) hq hz hker hdiv

/-- All intermediate leader and lowering data are constructed internally.
No nonzero-generator or Gröbner hypothesis is added to the final criterion. -/
theorem ClosedPairs.isGroebnerBasis {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    (hc : ClosedPairs o G) : IsGroebnerBasis o G (Submodule.span (Poly K D) (Set.range G)) := by
  obtain ⟨n,index,hi,hnz,hcover⟩ := exists_nonzero_subfamily G
  apply IsGroebnerBasis.of_nonzero_subfamily index hcover
  let H : Fin n → Vec K D r := fun i => G (index i)
  let t : Fin n → Term D r := fun i => lm o (H i) (hnz i)
  exact (hc.nonzero_subfamily index hi hcover).isGroebnerBasis_of_leaders t
    (fun i => lm_isLeading o (H i) (hnz i))

theorem closedPairs_iff_isGroebnerBasis (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    ClosedPairs o G ↔ IsGroebnerBasis o G (Submodule.span (Poly K D) (Set.range G)) :=
  ⟨fun h => h.isGroebnerBasis,fun h => h.closedPairs⟩

/-- Noetherian completion and the proved criterion yield a genuine finite
GB of the original module while retaining all original generators. -/
theorem exists_groebner_completion (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    ∃ n : ℕ, ∃ H : Fin n → Vec K D r,
      Submodule.span (Poly K D) (Set.range H)=Submodule.span (Poly K D) (Set.range G) ∧
      Set.range G ⊆ Set.range H ∧
      IsGroebnerBasis o H (Submodule.span (Poly K D) (Set.range G)) := by
  obtain ⟨n,H,hspan,hretain,hclosed⟩ := exists_closed_completion o G
  refine ⟨n,H,hspan,hretain,?_⟩
  rw [← hspan]
  exact hclosed.isGroebnerBasis

end
end Decoupling.HighDim.SchreyerModule
