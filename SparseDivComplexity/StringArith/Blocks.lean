import SparseDivComplexity.StringArith.Add

/-!
# Block iteration in Cobham's algebra

Term lists are encoded as concatenations of `delimit`-framed blocks, i.e. as nested pairs
`pair b₁ (pair b₂ (… []))`. This module provides the generic loop combinators used by the bridge
string transformation:

* `mapBlocks f s` — apply `f` to every framed block of `s` and re-frame the results;
* `foldBlocks step init s` — left fold over the framed blocks of `s`.

Both are shown to be in Cobham's algebra whenever the block function is, provided it comes with a
polynomial output-length bound (needed for the `boundedRec`/`iterFn` length side condition). Both
are instances of one generic loop (`blockStep`/`blockLoop`): the state `pair rem acc` holds the
unprocessed remainder and the accumulator, one step consumes a well-formed block, and a malformed
remainder moves to a fixed `bad` state that encodes the answer for unparsable input (matching
`blocks s = []`). The loop is run `|s| + 1` times with complexitylib's `Complexity.Cobham.iterFn`;
the length side condition is discharged for *all* inputs by a trajectory analysis based on the
maximal parse `s = frame bs ++ rem` (`exists_frame_append`), with a Cobham ruler of polynomial
length bounding every state.

The block decoders are complexitylib's `pairFst`/`pairSnd` (in `FP`, hence Cobham by
`FP_subset_CobhamFP`).
-/

open Complexity

namespace SparseDiv.StringArith

/-- `pairFst` as a Cobham function of a Cobham argument. -/
theorem cobham_pairFst_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ pairFst (g v) :=
  (Cobham.comp (FP_subset_CobhamFP Cobham.fstBlock_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-- `pairSnd` as a Cobham function of a Cobham argument. -/
theorem cobham_pairSnd_comp {n : ℕ} {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ pairSnd (g v) :=
  (Cobham.comp (FP_subset_CobhamFP Cobham.sndBlock_mem_FP) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-- `pair` of two Cobham functions is Cobham. -/
theorem cobham_pair_comp {n : ℕ} {g₀ g₁ : (Fin n → List Bool) → List Bool}
    (h₀ : Cobham g₀) (h₁ : Cobham g₁) :
    Cobham fun v : Fin n → List Bool ↦ pair (g₀ v) (g₁ v) :=
  (Cobham.comp₂ Cobham.pairing h₀ h₁).of_eq fun _ ↦ by simp

/-- The framed blocks of a string: `blocks (pair b rest) = b :: blocks rest`, `blocks s = []` when
`s` does not start with a well-formed block. Total, and
`blocks (encTerms-style code) = the list`. -/
def blocks (s : List Bool) : List (List Bool) :=
  match undelimitBlocks s with
  | some bs => bs
  | none => []

theorem blocks_flatten_delimit (bs : List (List Bool)) :
    blocks ((bs.map delimit).flatten) = bs := by
  simp [blocks, undelimitBlocks_flatten_delimit]

/-- Re-frame a list of blocks. -/
def frame (bs : List (List Bool)) : List Bool := (bs.map delimit).flatten

/-- Apply `f` to every framed block, re-framing the results. -/
def mapBlocks (f : List Bool → List Bool) (s : List Bool) : List Bool :=
  frame ((blocks s).map f)

/-- Left fold over the framed blocks. -/
def foldBlocks (step : List Bool → List Bool → List Bool) (init : List Bool) (s : List Bool) :
    List Bool :=
  (blocks s).foldl step init

theorem mapBlocks_frame (f : List Bool → List Bool) (bs : List (List Bool)) :
    mapBlocks f (frame bs) = frame (bs.map f) := by
  simp [mapBlocks, frame, blocks_flatten_delimit]

theorem foldBlocks_frame (step : List Bool → List Bool → List Bool) (init : List Bool)
    (bs : List (List Bool)) : foldBlocks step init (frame bs) = bs.foldl step init := by
  simp [foldBlocks, frame, blocks_flatten_delimit]

/-! ### Framing lemmas -/

/-- The empty block list frames to the empty string. -/
theorem frame_nil : frame [] = [] := rfl

/-- Framing peels one delimited block at a time. -/
theorem frame_cons (b : List Bool) (bs : List (List Bool)) :
    frame (b :: bs) = delimit b ++ frame bs := by
  simp [frame]

/-- Framing is a monoid homomorphism. -/
theorem frame_append (bs cs : List (List Bool)) : frame (bs ++ cs) = frame bs ++ frame cs := by
  simp [frame]

/-- A framed block list followed by a remainder is a `pair` of the first block with the rest. -/
theorem frame_cons_append (b : List Bool) (bs : List (List Bool)) (rem : List Bool) :
    frame (b :: bs) ++ rem = pair b (frame bs ++ rem) := by
  simp [frame, pair]

/-- `blocks` inverts `frame`. -/
theorem blocks_frame (bs : List (List Bool)) : blocks (frame bs) = bs :=
  blocks_flatten_delimit bs

/-- A framed list is at least as long as the number of its blocks. -/
theorem length_le_length_frame (bs : List (List Bool)) : bs.length ≤ (frame bs).length :=
  length_le_length_flatten_delimit bs

/-- Every block of a framed list fits in the frame. -/
theorem two_mul_length_add_two_le_of_mem_frame {b : List Bool} {bs : List (List Bool)}
    (h : b ∈ bs) : 2 * b.length + 2 ≤ (frame bs).length := by
  induction bs with
  | nil => simp at h
  | cons c bs ih =>
    rw [frame_cons, List.length_append, delimit_length]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h
      omega

/-- A pair encoding is never empty (it contains the separator). -/
theorem pair_ne_nil (x y : List Bool) : pair x y ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [pair_length]
  omega

/-- The nonemptiness flag of a nonempty string is `[true]`. -/
theorem nonemptyFlag_of_ne_nil {x : List Bool} (h : x ≠ []) : nonemptyFlag x = [true] := by
  obtain ⟨c, x', rfl⟩ := List.exists_cons_of_ne_nil h
  simp

/-- The equality flag of a string with itself is `[true]`. -/
theorem eqFlag_self (x : List Bool) : Cobham.eqFlag x x = [true] :=
  (Cobham.eqFlag_eq_true_iff x x).mpr rfl

/-- **Maximal parse.** Every string is a framed block list followed by a remainder that is either
empty or does not start with a well-formed block. -/
theorem exists_frame_append (s : List Bool) :
    ∃ (bs : List (List Bool)) (rem : List Bool),
      s = frame bs ++ rem ∧ (rem = [] ∨ unpair? rem = none) := by
  suffices h : ∀ (N : ℕ) (s : List Bool), s.length ≤ N →
      ∃ (bs : List (List Bool)) (rem : List Bool),
        s = frame bs ++ rem ∧ (rem = [] ∨ unpair? rem = none) from h s.length s le_rfl
  intro N
  induction N with
  | zero =>
    intro s hs
    exact ⟨[], s, by simp [frame], Or.inl (List.eq_nil_of_length_eq_zero (by omega))⟩
  | succ N ih =>
    intro s hs
    rcases hu : unpair? s with _ | ⟨b, rest⟩
    · exact ⟨[], s, by simp [frame], Or.inr hu⟩
    · have hs' : s = pair b rest := eq_pair_of_unpair?_eq_some hu
      have hlen : rest.length ≤ N := by
        have := congrArg List.length hs'
        rw [pair_length] at this
        omega
      obtain ⟨bs, rem, hrest, hrem⟩ := ih rest hlen
      exact ⟨b :: bs, rem, by rw [hs', hrest, frame_cons_append], hrem⟩

/-- The block parser fails on a framed list followed by a nonempty malformed remainder, whatever
the fuel. -/
theorem undelimitBlocksAux_frame_append_of_bad {rem : List Bool} (hne : rem ≠ [])
    (hbad : unpair? rem = none) :
    ∀ (bs : List (List Bool)) (fuel : ℕ), undelimitBlocksAux fuel (frame bs ++ rem) = none := by
  intro bs
  induction bs with
  | nil =>
    intro fuel
    obtain ⟨c, rem', rfl⟩ := List.exists_cons_of_ne_nil hne
    cases fuel with
    | zero => simp [frame, undelimitBlocksAux]
    | succ fuel => simp [frame, undelimitBlocksAux, hbad]
  | cons b bs ih =>
    intro fuel
    rw [frame_cons_append]
    obtain ⟨c, s', hs⟩ := List.exists_cons_of_ne_nil (pair_ne_nil b (frame bs ++ rem))
    cases fuel with
    | zero => rw [hs]; simp [undelimitBlocksAux]
    | succ fuel =>
      have h1 : unpair? (c :: s') = some (b, frame bs ++ rem) := by
        rw [← hs]
        exact unpair?_pair _ _
      rw [hs]
      simp [undelimitBlocksAux, h1, ih fuel]

/-- `blocks` returns `[]` on a framed list followed by a nonempty malformed remainder. -/
theorem blocks_frame_append_of_bad (bs : List (List Bool)) {rem : List Bool} (hne : rem ≠ [])
    (hbad : unpair? rem = none) : blocks (frame bs ++ rem) = [] := by
  simp [blocks, undelimitBlocks, undelimitBlocksAux_frame_append_of_bad hne hbad bs]

/-! ### The generic block loop

The loop state is `pair rem acc`: the unprocessed remainder of the input and the accumulator. One
step peels a block `b` off `rem` (when `rem = pair b rest`) and replaces `acc` by `g acc b`; an
empty remainder is a fixed point; a nonempty remainder that is not a well-formed block moves to the
designated `bad` state (which the callers choose to be a fixed point encoding the answer for an
unparsable input, matching `blocks s = []`). -/

/-- One step of the generic block loop on the state `pair rem acc`. -/
def blockStep (g : List Bool → List Bool → List Bool) (bad st : List Bool) : List Bool :=
  caseBit₀ (nonemptyFlag (pairFst st))
    (caseBit₀ (Cobham.eqFlag (pair (pairFst (pairFst st)) (pairSnd (pairFst st))) (pairFst st))
      (pair (pairSnd (pairFst st)) (g (pairSnd st) (pairFst (pairFst st)))) bad)
    st

/-- The block loop: `|s| + 1` steps from `pair s acc₀`, returning the accumulator. -/
def blockLoop (g : List Bool → List Bool → List Bool) (bad s acc₀ : List Bool) : List Bool :=
  pairSnd ((blockStep g bad)^[s.length + 1] (pair s acc₀))

/-- The empty string is a fixed point of the loop step. -/
theorem blockStep_nil (g : List Bool → List Bool → List Bool) (bad : List Bool) :
    blockStep g bad [] = [] := rfl

/-- An exhausted remainder is a fixed point of the loop step. -/
theorem blockStep_pair_nil (g : List Bool → List Bool → List Bool) (bad acc : List Bool) :
    blockStep g bad (pair [] acc) = pair [] acc := by
  simp [blockStep]

/-- The loop step consumes one well-formed block. -/
theorem blockStep_pair_pair (g : List Bool → List Bool → List Bool) (bad b rest acc : List Bool) :
    blockStep g bad (pair (pair b rest) acc) = pair rest (g acc b) := by
  simp [blockStep, nonemptyFlag_of_ne_nil (pair_ne_nil b rest), eqFlag_self]

/-- A nonempty malformed remainder sends the loop step to the `bad` state. -/
theorem blockStep_pair_bad (g : List Bool → List Bool → List Bool) (bad : List Bool)
    {rem : List Bool} (acc : List Bool) (hne : rem ≠ []) (hbad : unpair? rem = none) :
    blockStep g bad (pair rem acc) = bad := by
  have hflag : Cobham.eqFlag (pair (pairFst rem) (pairSnd rem)) rem = [false] := by
    rcases Cobham.eqFlag_flag (pair (pairFst rem) (pairSnd rem)) rem with h | h
    · exfalso
      have heq := (Cobham.eqFlag_eq_true_iff _ _).mp h
      have := unpair?_pair (pairFst rem) (pairSnd rem)
      rw [heq, hbad] at this
      simp at this
    · exact h
  simp [blockStep, nonemptyFlag_of_ne_nil hne, hflag]

/-- Iterating from an exhausted remainder changes nothing. -/
theorem blockStep_iterate_pair_nil (g : List Bool → List Bool → List Bool) (bad acc : List Bool)
    (m : ℕ) : (blockStep g bad)^[m] (pair [] acc) = pair [] acc :=
  Function.iterate_fixed (blockStep_pair_nil g bad acc) m

/-- Running the loop `k ≤ |bs|` steps on `frame bs ++ rem` processes the first `k` blocks. -/
theorem blockStep_iterate_of_le (g : List Bool → List Bool → List Bool) (bad : List Bool)
    {s : List Bool} {bs : List (List Bool)} {rem : List Bool} (hs : s = frame bs ++ rem)
    (acc : List Bool) {k : ℕ} (hk : k ≤ bs.length) :
    (blockStep g bad)^[k] (pair s acc) =
      pair (frame (bs.drop k) ++ rem) ((bs.take k).foldl g acc) := by
  subst hs
  induction k generalizing bs acc with
  | zero => simp
  | succ k ih =>
    cases bs with
    | nil => simp at hk
    | cons b bs =>
      rw [Function.iterate_succ_apply, frame_cons_append, blockStep_pair_pair,
        ih (g acc b) (by simpa using hk)]
      simp

/-- On a well-formed input the loop stays at `pair [] (bs.foldl g acc)` once all blocks are
processed. -/
theorem blockStep_iterate_of_nil (g : List Bool → List Bool → List Bool) (bad : List Bool)
    {s : List Bool} {bs : List (List Bool)} {rem : List Bool} (hs : s = frame bs ++ rem)
    (hrem : rem = []) (acc : List Bool) (k : ℕ) :
    (blockStep g bad)^[k] (pair s acc) =
      pair (frame (bs.drop k) ++ rem) ((bs.take k).foldl g acc) := by
  rcases Nat.lt_or_ge bs.length k with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + bs.length := ⟨k - bs.length, by omega⟩
    have hd : bs.drop (m + bs.length) = [] := List.drop_eq_nil_of_le (by omega)
    have ht : bs.take (m + bs.length) = bs := List.take_of_length_le (by omega)
    rw [Function.iterate_add_apply, blockStep_iterate_of_le g bad hs acc le_rfl, List.drop_length,
      List.take_length, frame_nil, List.nil_append, hrem, blockStep_iterate_pair_nil, hd, ht,
      frame_nil, List.nil_append]
  · exact blockStep_iterate_of_le g bad hs acc hk

/-- On a malformed input the loop reaches the `bad` state once the parsable prefix is consumed. -/
theorem blockStep_iterate_of_bad (g : List Bool → List Bool → List Bool) (bad : List Bool)
    (hfix : blockStep g bad bad = bad) {s : List Bool} {bs : List (List Bool)} {rem : List Bool}
    (hs : s = frame bs ++ rem) (hne : rem ≠ []) (hbad : unpair? rem = none) (acc : List Bool)
    {k : ℕ} (hk : bs.length < k) : (blockStep g bad)^[k] (pair s acc) = bad := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + bs.length := ⟨k - 1 - bs.length, by omega⟩
  rw [Function.iterate_add_apply, blockStep_iterate_of_le g bad hs acc le_rfl, List.drop_length,
    List.take_length, frame_nil, List.nil_append, Function.iterate_succ_apply,
    blockStep_pair_bad g bad _ hne hbad]
  exact Function.iterate_fixed hfix m

/-- **The loop computes the fold over `blocks`.** After `|s| + 1` steps the state is
`pair [] ((blocks s).foldl g acc₀)`, or `bad` when the input is unparsable (and then
`blocks s = []`). -/
theorem blockStep_iterate_length_add_one (g : List Bool → List Bool → List Bool) (bad : List Bool)
    (hfix : blockStep g bad bad = bad) (s acc₀ : List Bool) :
    (blockStep g bad)^[s.length + 1] (pair s acc₀) = pair [] ((blocks s).foldl g acc₀) ∨
      (blocks s = [] ∧ (blockStep g bad)^[s.length + 1] (pair s acc₀) = bad) := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append s
  have hlen : bs.length ≤ s.length := by
    rw [hs, List.length_append]
    exact le_add_right (length_le_length_frame bs)
  by_cases hne : rem = []
  · left
    subst hne
    rw [List.append_nil] at hs
    have hd : bs.drop (s.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
    have ht : bs.take (s.length + 1) = bs := List.take_of_length_le (by omega)
    rw [blockStep_iterate_of_nil g bad (by rw [hs, List.append_nil]) rfl acc₀, hd, ht, frame_nil,
      List.nil_append, hs, blocks_frame]
  · right
    have hbad : unpair? rem = none := hrem.resolve_left hne
    exact ⟨by rw [hs]; exact blocks_frame_append_of_bad bs hne hbad,
      blockStep_iterate_of_bad g bad hfix hs hne hbad acc₀ (by omega)⟩

/-- Length growth of a left fold whose step adds at most `K` bits. -/
theorem length_foldl_le (g : List Bool → List Bool → List Bool) (K : ℕ) :
    ∀ (l : List (List Bool)) (acc : List Bool),
      (∀ acc b, b ∈ l → (g acc b).length ≤ acc.length + K) →
      (l.foldl g acc).length ≤ acc.length + l.length * K := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons b l ih =>
    intro acc hg
    rw [List.foldl_cons, List.length_cons]
    have h1 := ih (g acc b) fun acc' b' hb' ↦ hg acc' b' (List.mem_cons_of_mem b hb')
    have h2 := hg acc b (List.mem_cons_self ..)
    calc (l.foldl g (g acc b)).length ≤ (g acc b).length + l.length * K := h1
      _ ≤ acc.length + K + l.length * K := by omega
      _ = acc.length + (l.length + 1) * K := by ring

/-- **Length bound for the whole trajectory.** If the block function adds at most `K` bits per
block of the input and the `bad` state respects the bound, every state of the loop does. -/
theorem blockStep_iterate_length_le (g : List Bool → List Bool → List Bool) (bad : List Bool)
    (hfix : blockStep g bad bad = bad) (s acc₀ : List Bool) (K : ℕ)
    (hg : ∀ acc b, 2 * b.length + 2 ≤ s.length → (g acc b).length ≤ acc.length + K)
    (hbad : bad.length ≤ 2 * s.length + 2 + acc₀.length + s.length * K) (k : ℕ) :
    ((blockStep g bad)^[k] (pair s acc₀)).length ≤
      2 * s.length + 2 + acc₀.length + s.length * K := by
  obtain ⟨bs, rem, hs, hrem⟩ := exists_frame_append s
  have hframe : (frame bs).length ≤ s.length := by
    rw [hs, List.length_append]
    exact Nat.le_add_right _ _
  have hreg : ∀ j, (pair (frame (bs.drop j) ++ rem) ((bs.take j).foldl g acc₀)).length ≤
      2 * s.length + 2 + acc₀.length + s.length * K := by
    intro j
    have hsplit : frame bs ++ rem = frame (bs.take j) ++ (frame (bs.drop j) ++ rem) := by
      rw [← List.append_assoc, ← frame_append, List.take_append_drop]
    have hlen : (frame (bs.drop j) ++ rem).length ≤ s.length := by
      rw [hs, hsplit]
      simp only [List.length_append]
      omega
    have hbs : (bs.take j).length ≤ s.length :=
      le_trans (List.length_take_le' _ _) (le_trans (length_le_length_frame bs) hframe)
    have hfold := length_foldl_le g K (bs.take j) acc₀ fun acc b hb ↦
      hg acc b (le_trans (two_mul_length_add_two_le_of_mem_frame (List.mem_of_mem_take hb)) hframe)
    have hmul := Nat.mul_le_mul_right K hbs
    rw [pair_length]
    omega
  by_cases hk : k ≤ bs.length ∨ rem = []
  · rcases hk with hk | hk
    · rw [blockStep_iterate_of_le g bad hs acc₀ hk]
      exact hreg k
    · rw [blockStep_iterate_of_nil g bad hs hk acc₀ k]
      exact hreg k
  · push Not at hk
    rw [blockStep_iterate_of_bad g bad hfix hs hk.2 (hrem.resolve_left hk.2) acc₀ hk.1]
    exact hbad

/-! ### Cobham membership of the loop -/

/-- Prepending a fixed bit to a member of the class. -/
theorem cobham_cons {n : ℕ} (b : Bool) {g : (Fin n → List Bool) → List Bool} (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool ↦ b :: g v :=
  (Cobham.comp (.bit b) fun _ : Fin 1 ↦ hg).of_eq fun _ ↦ rfl

/-- The concatenation of all arguments is in the class. -/
theorem cobham_flattenOfFn : ∀ m : ℕ, Cobham fun u : Fin m → List Bool ↦ (List.ofFn u).flatten
  | 0 => Cobham.empty.of_eq fun _ ↦ by simp
  | m + 1 =>
    (Cobham.appendFn (Cobham.proj 0)
      (Cobham.comp (cobham_flattenOfFn m) fun i ↦ Cobham.proj i.succ)).of_eq fun u ↦ by
        simp [List.ofFn_succ]

/-- The concatenation of all arguments has the total input length. -/
theorem length_flatten_ofFn {m : ℕ} (u : Fin m → List Bool) :
    (List.ofFn u).flatten.length = ∑ i, (u i).length := by
  simp [List.length_flatten, List.sum_ofFn]

/-- **The loop step is in the class.** The state is argument `0`, the loop parameters follow; the
block function `g` receives the accumulator, the block, then the loop parameters. -/
theorem cobham_blockStep {n : ℕ} {g : (Fin (n + 2) → List Bool) → List Bool} (hg : Cobham g)
    {bad : (Fin n → List Bool) → List Bool} (hbad : Cobham bad) :
    Cobham fun w : Fin (n + 1) → List Bool ↦
      blockStep (fun acc b ↦ g (Fin.cons acc (Fin.cons b (Fin.tail w)))) (bad (Fin.tail w))
        (w 0) := by
  have hst : Cobham fun w : Fin (n + 1) → List Bool ↦ w 0 := Cobham.proj 0
  have hrem := cobham_pairFst_comp hst
  have hacc := cobham_pairSnd_comp hst
  have hblk := cobham_pairFst_comp hrem
  have hrest := cobham_pairSnd_comp hrem
  have hg' : Cobham fun w : Fin (n + 1) → List Bool ↦
      g (Fin.cons (pairSnd (w 0)) (Fin.cons (pairFst (pairFst (w 0))) (Fin.tail w))) := by
    refine (Cobham.comp hg
      (gs := fun i (w : Fin (n + 1) → List Bool) ↦
        (Fin.cons (pairSnd (w 0)) (Fin.cons (pairFst (pairFst (w 0))) (Fin.tail w)) :
          Fin (n + 2) → List Bool) i)
      ?_).of_eq fun w ↦ rfl
    intro i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
    · exact hacc
    · exact hblk
    · exact Cobham.proj i.succ
  have hbad' : Cobham fun w : Fin (n + 1) → List Bool ↦ bad (Fin.tail w) :=
    (Cobham.comp hbad fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl
  exact Cobham.iteFn (Cobham.nonemptyFn hrem)
    (Cobham.iteFn (Cobham.eqFlag_mem (cobham_pair_comp hblk hrest) hrem)
      (cobham_pair_comp hrest hg') hbad') hst

/-- **The block loop is in the class**, given a ruler `ruler` bounding every state of the loop.
Here `u 0` is the string being processed and `Fin.tail u` are the parameters; the block function
`g` receives the accumulator, the block, then all of `u`. -/
theorem cobham_blockLoop {n : ℕ} {g : (Fin (n + 3) → List Bool) → List Bool} (hg : Cobham g)
    {bad acc₀ ruler : (Fin (n + 1) → List Bool) → List Bool}
    (hbad : Cobham bad) (hacc : Cobham acc₀) (hruler : Cobham ruler)
    (hlen : ∀ (u : Fin (n + 1) → List Bool) (k : ℕ),
      ((blockStep (fun acc b ↦ g (Fin.cons acc (Fin.cons b u))) (bad u))^[k]
        (pair (u 0) (acc₀ u))).length ≤ (ruler u).length) :
    Cobham fun u : Fin (n + 1) → List Bool ↦
      blockLoop (fun acc b ↦ g (Fin.cons acc (Fin.cons b u))) (bad u) (u 0) (acc₀ u) := by
  have hstep : Cobham fun w : Fin (n + 2) → List Bool ↦
      blockStep (fun acc b ↦ g (Fin.cons acc (Fin.cons b (Fin.tail w)))) (bad (Fin.tail w)) (w 0) :=
    cobham_blockStep hg hbad
  have he : Cobham fun u : Fin (n + 1) → List Bool ↦ pair (u 0) (acc₀ u) :=
    cobham_pair_comp (Cobham.proj 0) hacc
  have hj : Cobham fun w : Fin (n + 2) → List Bool ↦ ruler (Fin.tail w) :=
    (Cobham.comp hruler fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl
  have hiter := Cobham.iterFn he hstep hj (by
    intro c u
    simp only [Fin.tail_cons, Fin.cons_zero]
    exact hlen u c.length)
  have hclock : Cobham fun u : Fin (n + 1) → List Bool ↦ false :: u 0 :=
    cobham_cons false (Cobham.proj 0)
  have hloop := Cobham.comp hiter
    (gs := fun i (u : Fin (n + 1) → List Bool) ↦
      (Fin.cons (false :: u 0) u : Fin (n + 2) → List Bool) i)
    (by
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact hclock
      · exact Cobham.proj i)
  refine (cobham_pairSnd_comp hloop).of_eq fun u ↦ ?_
  simp only [blockLoop, Fin.tail_cons, Fin.cons_zero, List.length_cons]

/-- Folding `acc ++ delimit (f' b)` over a block list frames the mapped list. -/
theorem foldl_append_delimit (f' : List Bool → List Bool) :
    ∀ (bs : List (List Bool)) (acc : List Bool),
      bs.foldl (fun acc b ↦ acc ++ delimit (f' b)) acc = acc ++ frame (bs.map f')
  | [], acc => by simp [frame]
  | b :: bs, acc => by
    rw [List.foldl_cons, foldl_append_delimit f' bs, List.map_cons, frame_cons, List.append_assoc]

/-- `mapBlocks` as a block loop (with `bad = []`). -/
theorem mapBlocks_eq_blockLoop (f' : List Bool → List Bool) (s : List Bool) :
    mapBlocks f' s = blockLoop (fun acc b ↦ acc ++ delimit (f' b)) [] s [] := by
  unfold blockLoop
  rcases blockStep_iterate_length_add_one (fun acc b ↦ acc ++ delimit (f' b)) [] rfl s []
    with h | ⟨hb, h⟩
  · rw [h, pairSnd_pair, foldl_append_delimit, List.nil_append, mapBlocks]
  · rw [h, mapBlocks, hb]
    rfl

/-- `foldBlocks` as a block loop (with `bad = pair [] init'`). -/
theorem foldBlocks_eq_blockLoop (step' : List Bool → List Bool → List Bool) (init' s : List Bool) :
    foldBlocks step' init' s = blockLoop step' (pair [] init') s init' := by
  unfold blockLoop
  rcases blockStep_iterate_length_add_one step' (pair [] init') (blockStep_pair_nil _ _ _) s init'
    with h | ⟨hb, h⟩
  · rw [h, pairSnd_pair, foldBlocks]
  · rw [h, pairSnd_pair, foldBlocks, hb]
    rfl

/-- **`mapBlocks` is in Cobham's algebra** for any Cobham block function with a polynomial length
bound. The block function may depend on parameters `v` (arity `n`), the string being mapped is the
extra first argument. -/
theorem cobham_mapBlocks {n : ℕ} {f : (Fin (n + 1) → List Bool) → List Bool} (hf : Cobham f)
    (q : Polynomial ℕ) (hq : ∀ v, (f v).length ≤ q.eval (∑ i, (v i).length)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      mapBlocks (fun b ↦ f (Fin.cons b (Fin.tail v))) (v 0) := by
  -- The block function on `(acc, b, s, params)`: `acc ++ delimit (f (b, params))`.
  have hfblock : Cobham fun x : Fin (n + 3) → List Bool ↦
      f (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x)))) := by
    refine (Cobham.comp hf
      (gs := fun i (x : Fin (n + 3) → List Bool) ↦
        (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x))) : Fin (n + 1) → List Bool) i)
      ?_).of_eq fun x ↦ rfl
    intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact Cobham.proj 1
    · exact Cobham.proj i.succ.succ.succ
  have hg : Cobham fun x : Fin (n + 3) → List Bool ↦
      x 0 ++ delimit (f (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x))))) :=
    (Cobham.appendFn (Cobham.proj 0) (cobham_pair_comp hfblock (Cobham.const []))).of_eq
      fun x ↦ by simp [pair]
  -- The ruler: `2L + 2 + L (2 q(L) + 2)` bits, where `L` is the total input length.
  have hruler : Cobham fun u : Fin (n + 1) → List Bool ↦
      Cobham.polyLen (Polynomial.C 2 * Polynomial.X + Polynomial.C 2 +
        Polynomial.X * (Polynomial.C 2 * q + Polynomial.C 2)) (List.ofFn u).flatten :=
    Cobham.polyLen_mem _ (cobham_flattenOfFn (n + 1))
  refine (cobham_blockLoop hg (bad := fun _ ↦ []) (acc₀ := fun _ ↦ []) Cobham.empty Cobham.empty
    hruler ?_).of_eq fun v ↦ ?_
  · intro u k
    have hL0 : (u 0).length ≤ ∑ i, (u i).length := by
      rw [Fin.sum_univ_succ]
      exact Nat.le_add_right _ _
    have hK : ∀ acc b, 2 * b.length + 2 ≤ (u 0).length →
        (acc ++ delimit (f (Fin.cons b (Fin.tail u)))).length ≤
          acc.length + (2 * q.eval (∑ i, (u i).length) + 2) := by
      intro acc b hb
      have h1 := hq (Fin.cons b (Fin.tail u))
      have h2 : ∑ i, ((Fin.cons b (Fin.tail u) : Fin (n + 1) → List Bool) i).length ≤
          ∑ i, (u i).length := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
        omega
      have h3 : q.eval (∑ i, ((Fin.cons b (Fin.tail u) : Fin (n + 1) → List Bool) i).length) ≤
          q.eval (∑ i, (u i).length) := polynomial_eval_mono_nat q h2
      simp only [List.length_append, delimit_length]
      omega
    have hb := blockStep_iterate_length_le _ [] rfl (u 0) [] (2 * q.eval (∑ i, (u i).length) + 2)
      hK (by simp) k
    simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    refine le_trans hb ?_
    rw [Cobham.polyLen_length, length_flatten_ofFn]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      List.length_nil]
    have := Nat.mul_le_mul_right (2 * q.eval (∑ i, (u i).length) + 2) hL0
    omega
  · rw [mapBlocks_eq_blockLoop]
    rfl

/-- **`foldBlocks` is in Cobham's algebra** for any Cobham step function whose output length is
bounded by a polynomial in the accumulator length plus the block length (so the accumulator stays
polynomially bounded over the whole fold). The step receives the accumulator as argument `0`, the
block as argument `1`, and parameters afterwards. -/
theorem cobham_foldBlocks {n : ℕ} {step : (Fin (n + 2) → List Bool) → List Bool}
    (hstep : Cobham step) {init : (Fin n → List Bool) → List Bool} (hinit : Cobham init)
    (c : ℕ) (hgrow : ∀ w, (step w).length ≤ (w 0).length + c * ((w 1).length + 1)) :
    Cobham fun v : Fin (n + 1) → List Bool ↦
      foldBlocks (fun acc b ↦ step (Fin.cons acc (Fin.cons b (Fin.tail v))))
        (init (Fin.tail v)) (v 0) := by
  -- The block function on `(acc, b, s, params)`: `step (acc, b, params)`.
  have hg : Cobham fun x : Fin (n + 3) → List Bool ↦
      step (Fin.cons (x 0) (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x))))) := by
    refine (Cobham.comp hstep
      (gs := fun i (x : Fin (n + 3) → List Bool) ↦
        (Fin.cons (x 0) (Fin.cons (x 1) (Fin.tail (Fin.tail (Fin.tail x)))) :
          Fin (n + 2) → List Bool) i)
      ?_).of_eq fun x ↦ rfl
    intro i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
    · exact Cobham.proj 0
    · exact Cobham.proj 1
    · exact Cobham.proj i.succ.succ.succ
  have hinit' : Cobham fun u : Fin (n + 1) → List Bool ↦ init (Fin.tail u) :=
    (Cobham.comp hinit fun i ↦ Cobham.proj i.succ).of_eq fun _ ↦ rfl
  have hbad : Cobham fun u : Fin (n + 1) → List Bool ↦ pair [] (init (Fin.tail u)) :=
    cobham_pair_comp (Cobham.const []) hinit'
  -- The ruler: `2 + 2|s| + |init| + |s| · c · (|s| + 1)` bits.
  have hruler : Cobham fun u : Fin (n + 1) → List Bool ↦
      false :: false :: (u 0 ++ u 0) ++ init (Fin.tail u) ++
        Complexity.smash (u 0) (List.replicate c (false :: u 0)).flatten :=
    Cobham.appendFn (Cobham.appendFn
        (cobham_cons false (cobham_cons false (Cobham.appendFn (Cobham.proj 0) (Cobham.proj 0))))
        hinit')
      ((Cobham.comp₂ Cobham.smash (Cobham.proj 0)
        (Cobham.repeatFn (cobham_cons false (Cobham.proj 0)) c)).of_eq fun _ ↦ by simp)
  refine (cobham_blockLoop hg hbad hinit' hruler ?_).of_eq fun v ↦ ?_
  · intro u k
    have hK : ∀ acc b, 2 * b.length + 2 ≤ (u 0).length →
        (step (Fin.cons acc (Fin.cons b (Fin.tail u)))).length ≤
          acc.length + c * ((u 0).length + 1) := by
      intro acc b hb
      have h1 := hgrow (Fin.cons acc (Fin.cons b (Fin.tail u)))
      simp only [Fin.cons_zero, Fin.cons_one] at h1
      have h2 : c * (b.length + 1) ≤ c * ((u 0).length + 1) := Nat.mul_le_mul_left c (by omega)
      omega
    have hb := blockStep_iterate_length_le _ (pair [] (init (Fin.tail u)))
      (blockStep_pair_nil _ _ _) (u 0) (init (Fin.tail u)) (c * ((u 0).length + 1)) hK
      (by rw [pair_length]; simp only [List.length_nil]; omega) k
    simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
    refine le_trans hb ?_
    simp only [List.length_append, List.length_cons, smash_length, List.length_flatten,
      List.map_replicate, List.sum_replicate, smul_eq_mul]
    omega
  · rw [foldBlocks_eq_blockLoop]
    rfl

end SparseDiv.StringArith
