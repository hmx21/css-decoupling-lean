import Decoupling.HighDim.CorollaryOneZ

/-! # Extending the actual dual-cell change of coordinates across product ancillas -/

namespace Decoupling.HighDim.PhysicalIsomorphism

open Matrix
noncomputable section
variable {K : Type} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D

section Extension

variable {Q Q' A B C C' I : Type}
  [Fintype Q] [Fintype A] [Fintype B]
  [Fintype C] [Fintype C'] [Fintype I]
  [DecidableEq A] [DecidableEq B]

/-- Only the toric qudit block is relabeled; both ancillary species blocks
are left literally unchanged. -/
def ancillaryExtension (U : Matrix Q' Q R) :
    Matrix ((Q' ⊕ A) ⊕ B) ((Q ⊕ A) ⊕ B) R :=
  fromBlocks (fromBlocks U 0 0 1) 0 0 1

theorem ancillaryExtension_mulVec (U : Matrix Q' Q R)
    (v : ((Q ⊕ A) ⊕ B) → R) :
    ancillaryExtension U *ᵥ v =
      Sum.elim (Sum.elim (U *ᵥ (fun i => v (.inl (.inl i))))
        (fun a => v (.inl (.inr a)))) (v ∘ Sum.inr) := by
  simp [ancillaryExtension, fromBlocks_mulVec, Function.comp_def]

omit [Fintype Q] [Fintype A] [Fintype B] in
@[simp] theorem dagger_ancillaryExtension (U : Matrix Q' Q R) :
    dagger (ancillaryExtension (A := A) (B := B) U) = ancillaryExtension (dagger U) := by
  funext i j
  rcases i with (i | a) | b <;> rcases j with (j | a') | b' <;>
    simp [ancillaryExtension, dagger, Matrix.one_apply, eq_comm]

omit [Fintype Q] in
theorem ancillaryExtension_dagger_mul [DecidableEq Q] (U : Matrix Q' Q R)
    [Fintype Q'] (h : dagger U * U = 1) :
    dagger (ancillaryExtension (A := A) (B := B) U) *
      ancillaryExtension (A := A) (B := B) U = 1 := by
  rw [dagger_ancillaryExtension]
  simp [ancillaryExtension, Matrix.fromBlocks_multiply, h, Matrix.fromBlocks_one]

theorem ancillaryExtension_mul_dagger [DecidableEq Q'] (U : Matrix Q' Q R)
    (h : U * dagger U = 1) :
    ancillaryExtension (A := A) (B := B) U *
      dagger (ancillaryExtension (A := A) (B := B) U) = 1 := by
  rw [dagger_ancillaryExtension]
  simp [ancillaryExtension, Matrix.fromBlocks_multiply, h, Matrix.fromBlocks_one]

/-- A proved stabilizer-image equivalence extends to the zero-A/arbitrary-B
ancillary block, retaining the actual matrix action. -/
theorem ancillaryExtension_Z_image (U : Matrix Q' Q R)
    (F : Matrix Q C R) (G : Matrix Q' C' R)
    (h : ∀ v, (∃ z, U *ᵥ (F *ᵥ z) = v) ↔ inImage G v)
    (v : ((Q' ⊕ A) ⊕ B) → R) :
    (∃ z, ancillaryExtension U *ᵥ (StableCSS.H_Z_dagger (A := A) (B := B) F *ᵥ z) = v) ↔
      inImage (StableCSS.H_Z_dagger (A := A) (B := B) G) v := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (h _).mp ⟨z ∘ Sum.inl, rfl⟩
    refine ⟨Sum.elim w (z ∘ Sum.inr), ?_⟩
    rw [StableCSS.H_Z_dagger_mulVec, StableCSS.H_Z_dagger_mulVec, ancillaryExtension_mulVec]
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr, Function.comp_def] using
      congrArg (fun x => Sum.elim (Sum.elim x (0 : A → R)) (z ∘ Sum.inr)) hw
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (h _).mpr ⟨z ∘ Sum.inl, rfl⟩
    refine ⟨Sum.elim w (z ∘ Sum.inr), ?_⟩
    rw [StableCSS.H_Z_dagger_mulVec, StableCSS.H_Z_dagger_mulVec, ancillaryExtension_mulVec]
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr, Function.comp_def] using
      congrArg (fun x => Sum.elim (Sum.elim x (0 : A → R)) (z ∘ Sum.inr)) hw

/-- The arbitrary-A/zero-B block and any zero identity-check rows likewise
preserve a proved image equivalence. -/
theorem ancillaryExtension_X_image (U : Matrix Q' Q R)
    (F : Matrix C Q R) (G : Matrix C' Q' R)
    (h : ∀ v, (∃ z, U *ᵥ (dagger F *ᵥ z) = v) ↔ inImage (dagger G) v)
    (v : ((Q' ⊕ A) ⊕ B) → R) :
    (∃ z, ancillaryExtension U *ᵥ
      (dagger (StableCSS.H_X (A := A) (B := B)
        (StableCSS.identityChecks (A := I) F)) *ᵥ z) = v) ↔
      inImage (dagger (StableCSS.H_X (A := A) (B := B)
        (StableCSS.identityChecks (A := I) G))) v := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (h _).mp ⟨fun i => z (.inl (.inl i)), rfl⟩
    refine ⟨Sum.elim (Sum.elim w (0 : I → R)) (z ∘ Sum.inr), ?_⟩
    rw [StableCSS.dagger_X_mulVec, StableCSS.dagger_X_mulVec,
      StableCSS.identityChecks_dagger_mulVec, StableCSS.identityChecks_dagger_mulVec,
      ancillaryExtension_mulVec]
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr, Function.comp_def] using
      congrArg (fun x => Sum.elim (Sum.elim x (z ∘ Sum.inr)) (0 : B → R)) hw
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := (h _).mpr ⟨fun i => z (.inl (.inl i)), rfl⟩
    refine ⟨Sum.elim (Sum.elim w (0 : I → R)) (z ∘ Sum.inr), ?_⟩
    rw [StableCSS.dagger_X_mulVec, StableCSS.dagger_X_mulVec,
      StableCSS.identityChecks_dagger_mulVec, StableCSS.identityChecks_dagger_mulVec,
      ancillaryExtension_mulVec]
    simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inl, Sum.elim_inr, Function.comp_def] using
      congrArg (fun x => Sum.elim (Sum.elim x (z ∘ Sum.inr)) (0 : B → R)) hw

end Extension

section Composition

variable {Q Q' Q'' C C' C'' Z Z' Z'' : Type}
  [Fintype Q] [Fintype Q'] [Fintype Q'']
  [Fintype C] [Fintype C'] [Fintype C'']
  [Fintype Z] [Fintype Z'] [Fintype Z'']
  [DecidableEq Q']

/-- Actual stabilizer transport by the local word followed by the separately
specified geometric qudit relabeling. The two operations are not conflated. -/
def TransportsAfter (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (U : Matrix Q'' Q' R) (HC : Matrix C Q R) (HT : Matrix C'' Q'' R)
    (BC : Matrix Q Z R) (BT : Matrix Q'' Z'' R) : Prop :=
  (∀ v, (∃ z, U *ᵥ (Circuit.wordZ gates *ᵥ ((BC *ᵥ z) ∘ e.symm)) = v) ↔ inImage BT v) ∧
  (∀ v, (∃ z, U *ᵥ (Circuit.wordX gates *ᵥ ((dagger HC *ᵥ z) ∘ e.symm)) = v) ↔
    inImage (dagger HT) v)

omit [Fintype Q] [Fintype Q''] in
theorem transportsAfter_of_images (gates : List (Circuit.Layer K D Q')) (e : Q ≃ Q')
    (U : Matrix Q'' Q' R) (HC : Matrix C Q R) (HM : Matrix C' Q' R)
    (HT : Matrix C'' Q'' R) (BC : Matrix Q Z R) (BM : Matrix Q' Z' R)
    (BT : Matrix Q'' Z'' R)
    (hc : Transports gates e HC HM BC BM)
    (hz : ∀ v, (∃ z, U *ᵥ (BM *ᵥ z) = v) ↔ inImage BT v)
    (hx : ∀ v, (∃ z, U *ᵥ (dagger HM *ᵥ z) = v) ↔ inImage (dagger HT) v) :
    TransportsAfter gates e U HC HT BC BT := by
  constructor
  · intro v
    rw [← hz]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := (hc.1 _).mp ⟨z, rfl⟩
      exact ⟨w, congrArg (fun x => U *ᵥ x) hw⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hc.1 _).mpr ⟨w, rfl⟩
      exact ⟨z, congrArg (fun x => U *ᵥ x) hz⟩
  · intro v
    rw [← hx]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := (hc.2 _).mp ⟨z, rfl⟩
      exact ⟨w, congrArg (fun x => U *ᵥ x) hw⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hc.2 _).mpr ⟨w, rfl⟩
      exact ⟨z, congrArg (fun x => U *ᵥ x) hz⟩

end Composition
end
end Decoupling.HighDim.PhysicalIsomorphism
