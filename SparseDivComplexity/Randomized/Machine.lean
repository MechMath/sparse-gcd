import Complexitylib.Models.TuringMachine.GuessAssembly
import Complexitylib.Models.TuringMachine.Composition.Nondeterministic.Trace
import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
import Complexitylib.Models.TuringMachine.Subroutines.Internal
import Complexitylib.Classes.Containments.Internal.NLSearchAssemble
import Complexitylib.Classes.P.NormalForm
import SparseDivComplexity.Randomized.Defs

/-!
# A probabilistic machine realizing a random-tape verdict

Given a polynomial-time verdict function `V` on `pair x r` and a seed length `ℓ`, we build a
probabilistic Turing machine (complexitylib `NTM`) which on input `x` guesses a uniformly random
seed, runs `V` and accepts iff the verdict is `[true]`.

## Construction

* `SparseDiv.guessCopyTM ng : TM (ng + 2)` — the only nondeterministic ingredient. Its last work
  tape is the guess tape (`NTM.ofGuess`); tape `ng` is the virtual input of the verifier. It copies
  the input `z` onto tape `ng`, then appends `|z| + 1` guessed bits (one per input cell, scanning
  the input backwards), so that tape `ng` holds `z ++ r'`.
* `SparseDiv.verdictTM ng D` — rewinds tape `ng` and runs the verifier `D` on it as virtual input
  (`TM.retargetInputStarted`), lifted past the guess tape.
* `SparseDiv.seedMachine ng D := NTM.ofGuess (seqTM (guessCopyTM ng) (verdictTM ng D))`.
* The final machine is `NTM.compositionNTM tmF (seedMachine ng D)` where `tmF` pads the input to
  `pair x (polyRuler ℓ x)`, so that `|z| + 1 ≥ ℓ(|x|)` guessed bits are available, and `D`
  computes the flag `Cobham.eqFlag (V (pair x r)) [true]` from `z ++ r'`.
-/

open Complexity

namespace SparseDiv

open Complexity.TM

/-! ## The guess-and-copy machine -/

/-- Control states of `guessCopyTM`. -/
inductive GuessCopyPhase where
  /-- Copy the input onto the virtual-input tape, scanning right. -/
  | copy
  /-- Append one guessed bit per input cell, scanning the input back to its left end. -/
  | guess
  /-- Halt. -/
  | done
  deriving DecidableEq

instance : Fintype GuessCopyPhase where
  elems := {.copy, .guess, .done}
  complete := fun x ↦ by cases x <;> simp

/-- The advancing state of `guessCopyTM`: only `guess` consumes guess bits. -/
@[simp] def guessCopyAdv (q : GuessCopyPhase) : Bool := decide (q = GuessCopyPhase.guess)

/-- The virtual-input tape index in the `ng + 2` layout: tape `ng`. -/
def vIdx (ng : ℕ) : Fin (ng + 2) := ⟨ng, by omega⟩

/-- The guess tape index in the `ng + 2` layout: the last tape. -/
def gIdx (ng : ℕ) : Fin (ng + 2) := Fin.last (ng + 1)

theorem vIdx_ne_gIdx (ng : ℕ) : vIdx ng ≠ gIdx ng := by
  intro h
  have := congrArg Fin.val h
  simp [vIdx, gIdx] at this

theorem gIdx_ne_vIdx (ng : ℕ) : gIdx ng ≠ vIdx ng := (vIdx_ne_gIdx ng).symm

theorem last_eq_gIdx (ng : ℕ) : Fin.last (ng + 1) = gIdx ng := rfl

theorem vIdx_eq_castSucc_last (ng : ℕ) : vIdx ng = (Fin.last ng).castSucc := rfl

/-- **The guess-and-copy machine.** In state `copy` it copies each input bit onto tape `ng`
(moving both heads right) and switches to `guess` on the first blank. In state `guess` it writes
the guess-tape symbol onto tape `ng` and moves the input head left, until the input head reads
the left marker; then it halts. The guess head advances exactly in state `guess`. -/
def guessCopyTM (ng : ℕ) : TM (ng + 2) where
  Q := GuessCopyPhase
  qstart := .copy
  qhalt := .done
  δ q iHead wHeads oHead :=
    match q with
    | .copy =>
      if iHead = Γ.blank then
        (GuessCopyPhase.guess, fun i ↦ readBackWrite (wHeads i), readBackWrite oHead,
          idleDir iHead, fun i ↦ idleDir (wHeads i), idleDir oHead)
      else
        (GuessCopyPhase.copy,
          fun i ↦ if i = vIdx ng then readBackWrite iHead else readBackWrite (wHeads i),
          readBackWrite oHead, Dir3.right,
          fun i ↦ if i = vIdx ng then Dir3.right else idleDir (wHeads i), idleDir oHead)
    | .guess =>
      if iHead = Γ.start then
        (GuessCopyPhase.done, fun i ↦ readBackWrite (wHeads i), readBackWrite oHead,
          Dir3.right, fun i ↦ if i = gIdx ng then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
      else
        (GuessCopyPhase.guess,
          fun i ↦ if i = vIdx ng then readBackWrite (wHeads (gIdx ng))
            else readBackWrite (wHeads i),
          readBackWrite oHead, Dir3.left,
          fun i ↦ if i = gIdx ng then Dir3.right else if i = vIdx ng then Dir3.right
            else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle GuessCopyPhase.done iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    match q with
    | .copy =>
      dsimp only
      split
      · exact rightOfStart_allIdle iHead wHeads oHead
      · refine ⟨fun _ ↦ rfl, fun i hi ↦ ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · rfl
        · exact idleDir_right_of_start hi
    | .guess =>
      dsimp only
      split
      · refine ⟨fun _ ↦ rfl, fun i hi ↦ ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · rfl
        · exact idleDir_right_of_start hi
      · rename_i h
        refine ⟨fun h' ↦ absurd h' h, fun i hi ↦ ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · rfl
        · split
          · rfl
          · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

@[simp] theorem guessCopyTM_qstart (ng : ℕ) : (guessCopyTM ng).qstart = GuessCopyPhase.copy := rfl

@[simp] theorem guessCopyTM_qhalt (ng : ℕ) : (guessCopyTM ng).qhalt = GuessCopyPhase.done := rfl

/-- The guess-and-copy machine obeys the guess protocol with advancing state `guess`. -/
theorem guessProtocol_guessCopyTM (ng : ℕ) :
    GuessProtocol (guessCopyTM ng) guessCopyAdv := by
  have hg : gIdx ng = Fin.last (ng + 1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | _ | _) hq iHead wHeads oHead
    · simp only [guessCopyTM]
      split <;> simp [← hg, gIdx_ne_vIdx]
    · simp only [guessCopyTM]
      split <;> simp [← hg]
    · exact absurd rfl hq
  · rintro (_ | _ | _) hq iHead wHeads oHead hs
    · rw [← hg] at hs
      simp only [guessCopyTM]
      split <;> simp [← hg, gIdx_ne_vIdx, idleDir, hs, guessCopyAdv]
    · simp only [guessCopyTM]
      split <;> simp [← hg, guessCopyAdv]
    · exact absurd rfl hq
  · rintro (_ | _ | _) hq hadv iHead ww oHead g g'
    · simp only [guessCopyTM, visible]
      split <;> simp [Fin.snoc_castSucc, vIdx_eq_castSucc_last]
    · simp at hadv
    · exact absurd rfl hq

/-! ## Tapes and configurations along the run of `guessCopyTM` -/

/-- The input tape carrying `z`, with its head at cell `p`. -/
def inpTape (z : List Bool) (p : ℕ) : Tape := ⟨p, (Tape.init (z.map Γ.ofBool)).cells⟩

/-- A blank tape parked at cell `1` (the shape every scratch tape has after the first step). -/
def blank1 : Tape := (Tape.init []).move Dir3.right

theorem blank1_head : blank1.head = 1 := rfl

theorem blank1_cells (p : ℕ) : blank1.cells p = (Tape.init []).cells p := rfl

theorem blank1_read : blank1.read = Γ.blank := by
  show (Tape.init []).cells 1 = Γ.blank
  exact Tape.init_nil_cells_succ 0

theorem blank1_read_ne_start : blank1.read ≠ Γ.start := by
  rw [blank1_read]; decide

/-- Cells of the virtual-input tape after copying the first `i - 1` input cells. -/
def copyCells (z : List Bool) (i : ℕ) (p : ℕ) : Γ :=
  if p = 0 then Γ.start else if p < i then (Tape.init (z.map Γ.ofBool)).cells p else Γ.blank

/-- Cells of the virtual-input tape holding `z` followed by the first `j` guessed bits. -/
def guessCells (z : List Bool) (g : ℕ → Bool) (j : ℕ) (p : ℕ) : Γ :=
  if p ≤ z.length then (Tape.init (z.map Γ.ofBool)).cells p
  else if p ≤ z.length + j then Γ.ofBool (g (p - z.length - 1)) else Γ.blank

/-- The guess tape after `j` guesses have been consumed. -/
def gTape (g : ℕ → Bool) (j : ℕ) : Tape := ⟨j + 1, (NTM.loadTape g).cells⟩

theorem gTape_read (g : ℕ → Bool) (j : ℕ) : (gTape g j).read = Γ.ofBool (g j) :=
  NTM.loadTape_cells_succ g j

theorem gTape_read_ne_start (g : ℕ → Bool) (j : ℕ) : (gTape g j).read ≠ Γ.start := by
  rw [gTape_read]; exact Γ.ofBool_ne_start _

theorem gTape_zero (g : ℕ → Bool) : gTape g 0 = NTM.loadTape g := rfl

variable {ng : ℕ}

/-- The configuration of `guessCopyTM` after `i ≥ 1` steps of the copy phase. -/
def copyCfg (ng : ℕ) (z : List Bool) (g : ℕ → Bool) (i : ℕ) :
    Cfg (ng + 2) (guessCopyTM ng).Q where
  state := GuessCopyPhase.copy
  input := inpTape z i
  work := fun k ↦ if k = gIdx ng then NTM.loadTape g
    else if k = vIdx ng then ⟨i, copyCells z i⟩ else blank1
  output := blank1

/-- The configuration of `guessCopyTM` after `j` steps of the guess phase. -/
def guessCfg (ng : ℕ) (z : List Bool) (g : ℕ → Bool) (j : ℕ) :
    Cfg (ng + 2) (guessCopyTM ng).Q where
  state := GuessCopyPhase.guess
  input := inpTape z (z.length + 1 - j)
  work := fun k ↦ if k = gIdx ng then gTape g j
    else if k = vIdx ng then ⟨z.length + 1 + j, guessCells z g j⟩ else blank1
  output := blank1

/-- The halting configuration of `guessCopyTM`. -/
def doneCfg (ng : ℕ) (z : List Bool) (g : ℕ → Bool) : Cfg (ng + 2) (guessCopyTM ng).Q where
  state := GuessCopyPhase.done
  input := inpTape z 1
  work := fun k ↦ if k = gIdx ng then gTape g (z.length + 2)
    else if k = vIdx ng then ⟨2 * z.length + 2, guessCells z g (z.length + 1)⟩ else blank1
  output := blank1

/-! ### Tape-level helpers -/

theorem idle_writeAndMove (t : Tape) (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t h, idleDir, ite_eq_right h]
  rfl

theorem init_nil_writeAndMove_right (s : Γ) :
    (Tape.init []).writeAndMove s Dir3.right = blank1 := by
  show ((Tape.init []).write s).move Dir3.right = _
  rw [Tape.write, ite_eq_left (Tape.init_head [])]
  rfl

theorem mk_writeAndMove_right (p : ℕ) (cs : ℕ → Γ) (s : Γ) (hp : p ≠ 0) :
    (⟨p, cs⟩ : Tape).writeAndMove s Dir3.right = ⟨p + 1, Function.update cs p s⟩ := by
  show ((⟨p, cs⟩ : Tape).write s).move Dir3.right = _
  rw [Tape.write, ite_eq_right hp]
  rfl

theorem mk_writeAndMove_left (p : ℕ) (cs : ℕ → Γ) (s : Γ) (hp : p ≠ 0) :
    (⟨p, cs⟩ : Tape).writeAndMove s Dir3.left = ⟨p - 1, Function.update cs p s⟩ := by
  show ((⟨p, cs⟩ : Tape).write s).move Dir3.left = _
  rw [Tape.write, ite_eq_right hp]
  rfl

theorem inpTape_read (z : List Bool) (p : ℕ) :
    (inpTape z p).read = (Tape.init (z.map Γ.ofBool)).cells p := rfl

theorem inpTape_read_zero (z : List Bool) : (inpTape z 0).read = Γ.start := by
  rw [inpTape_read]; simp

theorem inpTape_read_bit (z : List Bool) (p : ℕ) (hp1 : 1 ≤ p) (hp : p ≤ z.length) :
    (inpTape z p).read = Γ.ofBool (z[p - 1]'(by omega)) := by
  rw [inpTape_read]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Tape.init_ofBool_cells_lt z q (by omega)]
  rfl

theorem inpTape_read_blank (z : List Bool) : (inpTape z (z.length + 1)).read = Γ.blank := by
  rw [inpTape_read]
  exact Tape.init_ofBool_cells_ge z z.length le_rfl

theorem inpTape_read_ne_start (z : List Bool) (p : ℕ) (hp : 1 ≤ p) :
    (inpTape z p).read ≠ Γ.start :=
  Tape.init_ofBool_cells_ne_start z p hp

theorem inpTape_move_right (z : List Bool) (p : ℕ) :
    (inpTape z p).move Dir3.right = inpTape z (p + 1) := rfl

theorem inpTape_move_left (z : List Bool) (p : ℕ) :
    (inpTape z p).move Dir3.left = inpTape z (p - 1) := rfl

theorem copyCells_succ_self (z : List Bool) (i : ℕ) (hi : i ≠ 0) :
    Function.update (copyCells z i) i ((Tape.init (z.map Γ.ofBool)).cells i) =
      copyCells z (i + 1) := by
  funext p
  by_cases hp : p = i
  · subst hp
    rw [Function.update_self, copyCells, ite_eq_right hi, ite_eq_left (Nat.lt_succ_self p)]
  · rw [Function.update_of_ne hp]
    simp only [copyCells]
    split_ifs <;> first | rfl | omega

theorem copyCells_length_succ (z : List Bool) (g : ℕ → Bool) :
    copyCells z (z.length + 1) = guessCells z g 0 := by
  funext p
  simp only [copyCells, guessCells, add_zero]
  by_cases h0 : p = 0
  · subst h0; simp
  · split_ifs <;> first | rfl | omega

theorem guessCells_read_blank (z : List Bool) (g : ℕ → Bool) (j : ℕ) :
    guessCells z g j (z.length + 1 + j) = Γ.blank := by
  simp only [guessCells]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem guessCells_succ_self (z : List Bool) (g : ℕ → Bool) (j : ℕ) :
    Function.update (guessCells z g j) (z.length + 1 + j) (Γ.ofBool (g j)) =
      guessCells z g (j + 1) := by
  funext p
  by_cases hp : p = z.length + 1 + j
  · subst hp
    rw [Function.update_self]
    simp only [guessCells]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 2
    omega
  · rw [Function.update_of_ne hp]
    simp only [guessCells]
    split_ifs <;> first | rfl | omega

theorem loadCfg_state (M : TM (ng + 2)) (z : List Bool) (g : ℕ → Bool) :
    (NTM.loadCfg M z g).state = M.qstart := rfl

theorem loadCfg_input (M : TM (ng + 2)) (z : List Bool) (g : ℕ → Bool) :
    (NTM.loadCfg M z g).input = Tape.init (z.map Γ.ofBool) := rfl

theorem loadCfg_output (M : TM (ng + 2)) (z : List Bool) (g : ℕ → Bool) :
    (NTM.loadCfg M z g).output = Tape.init [] := rfl

theorem loadCfg_work (M : TM (ng + 2)) (z : List Bool) (g : ℕ → Bool) (k : Fin (ng + 2)) :
    (NTM.loadCfg M z g).work k = if k = gIdx ng then NTM.loadTape g else Tape.init [] := by
  refine Fin.lastCases ?_ ?_ k
  · rw [ite_eq_left (last_eq_gIdx ng)]
    exact NTM.loadCfg_work_last M z g
  · intro j
    rw [ite_eq_right (show j.castSucc ≠ gIdx ng from (Fin.castSucc_lt_last j).ne)]
    simp [NTM.loadCfg]

theorem blank1_eq_copyCells_one (z : List Bool) :
    blank1 = ⟨1, copyCells z 1⟩ := by
  refine Tape.ext rfl ?_
  funext p
  show (Tape.init []).cells p = copyCells z 1 p
  rw [copyCells]
  by_cases h0 : p = 0
  · subst h0; simp
  · rw [ite_eq_right h0, ite_eq_right (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact Tape.init_nil_cells_succ q

/-! ### Step lemmas -/

/-- One step, spelled out through the projections of the transition. -/
theorem stepCfg_eq {n : ℕ} (tm : TM n) (c : Cfg n tm.Q) :
    tm.stepCfg c =
      { state := (tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).1
        input := c.input.move
          (tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.2.2.1
        work := fun i ↦ (c.work i).writeAndMove
          ((tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.1 i)
          ((tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.2.2.2.1 i)
        output := c.output.writeAndMove
          (tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.2.1
          (tm.δ c.state c.input.read (fun i ↦ (c.work i).read) c.output.read).2.2.2.2.2 } :=
  rfl

theorem δ_copy_bit (iHead : Γ) (wHeads : Fin (ng + 2) → Γ) (oHead : Γ) (h : iHead ≠ Γ.blank) :
    (guessCopyTM ng).δ .copy iHead wHeads oHead =
      (GuessCopyPhase.copy,
        fun i ↦ if i = vIdx ng then readBackWrite iHead else readBackWrite (wHeads i),
        readBackWrite oHead, Dir3.right,
        fun i ↦ if i = vIdx ng then Dir3.right else idleDir (wHeads i), idleDir oHead) := by
  simp [guessCopyTM, h]

theorem δ_copy_blank (wHeads : Fin (ng + 2) → Γ) (oHead : Γ) :
    (guessCopyTM ng).δ .copy Γ.blank wHeads oHead =
      (GuessCopyPhase.guess, fun i ↦ readBackWrite (wHeads i), readBackWrite oHead,
        idleDir Γ.blank, fun i ↦ idleDir (wHeads i), idleDir oHead) := by
  simp [guessCopyTM]

theorem δ_guess_start (wHeads : Fin (ng + 2) → Γ) (oHead : Γ) :
    (guessCopyTM ng).δ .guess Γ.start wHeads oHead =
      (GuessCopyPhase.done, fun i ↦ readBackWrite (wHeads i), readBackWrite oHead,
        Dir3.right, fun i ↦ if i = gIdx ng then Dir3.right else idleDir (wHeads i),
        idleDir oHead) := by
  simp [guessCopyTM]

theorem δ_guess_bit (iHead : Γ) (wHeads : Fin (ng + 2) → Γ) (oHead : Γ) (h : iHead ≠ Γ.start) :
    (guessCopyTM ng).δ .guess iHead wHeads oHead =
      (GuessCopyPhase.guess,
        fun i ↦ if i = vIdx ng then readBackWrite (wHeads (gIdx ng)) else readBackWrite (wHeads i),
        readBackWrite oHead, Dir3.left,
        fun i ↦ if i = gIdx ng then Dir3.right else if i = vIdx ng then Dir3.right
          else idleDir (wHeads i),
        idleDir oHead) := by
  simp [guessCopyTM, h]

theorem stepCfg_loadCfg (z : List Bool) (g : ℕ → Bool) :
    (guessCopyTM ng).stepCfg (NTM.loadCfg (guessCopyTM ng) z g) = copyCfg ng z g 1 := by
  have hread : (Tape.init (z.map Γ.ofBool)).read = Γ.start := by simp [Tape.read]
  have hnb : (Tape.init (z.map Γ.ofBool)).read ≠ Γ.blank := by rw [hread]; decide
  rw [stepCfg_eq]
  simp only [loadCfg_state, loadCfg_input, loadCfg_output, loadCfg_work, guessCopyTM_qstart,
    copyCfg]
  rw [δ_copy_bit _ _ _ hnb]
  dsimp only
  refine Cfg.ext rfl ?_ ?_ ?_
  · rfl
  · funext k
    by_cases hk : k = gIdx ng
    · subst hk
      simp only [gIdx_ne_vIdx, ↓reduceIte]
      exact idle_writeAndMove _ (gTape_read_ne_start g 0)
    · by_cases hk' : k = vIdx ng
      · subst hk'
        simp only [hk, ↓reduceIte]
        rw [init_nil_writeAndMove_right]
        exact blank1_eq_copyCells_one z
      · simp only [hk, hk', ↓reduceIte, Tape.read, Tape.init_head, Tape.init_cells_zero, idleDir]
        exact init_nil_writeAndMove_right _
  · simp only [Tape.read, Tape.init_head, Tape.init_cells_zero, idleDir, ↓reduceIte]
    exact init_nil_writeAndMove_right _

theorem stepCfg_copyCfg (z : List Bool) (g : ℕ → Bool) (i : ℕ) (hi1 : 1 ≤ i)
    (hi : i ≤ z.length) :
    (guessCopyTM ng).stepCfg (copyCfg ng z g i) = copyCfg ng z g (i + 1) := by
  have hnb : (inpTape z i).read ≠ Γ.blank := by
    rw [inpTape_read_bit z i hi1 hi]; exact Γ.ofBool_ne_blank _
  have hns : (inpTape z i).read ≠ Γ.start := inpTape_read_ne_start z i hi1
  rw [stepCfg_eq]
  simp only [copyCfg]
  rw [δ_copy_bit _ _ _ hnb]
  dsimp only
  refine Cfg.ext rfl (inpTape_move_right z i) ?_ ?_
  · funext k
    by_cases hk : k = gIdx ng
    · subst hk
      simp only [gIdx_ne_vIdx, ↓reduceIte]
      exact idle_writeAndMove _ (gTape_read_ne_start g 0)
    · by_cases hk' : k = vIdx ng
      · subst hk'
        simp only [hk, ↓reduceIte]
        rw [mk_writeAndMove_right i _ _ (by omega), toΓ_readBackWrite_of_ne_start hns,
          inpTape_read, copyCells_succ_self z i (by omega)]
      · simp only [hk, hk', ↓reduceIte]
        exact idle_writeAndMove blank1 blank1_read_ne_start
  · exact idle_writeAndMove blank1 blank1_read_ne_start

theorem stepCfg_copyCfg_last (z : List Bool) (g : ℕ → Bool) :
    (guessCopyTM ng).stepCfg (copyCfg ng z g (z.length + 1)) = guessCfg ng z g 0 := by
  have hb : (inpTape z (z.length + 1)).read = Γ.blank := inpTape_read_blank z
  rw [stepCfg_eq]
  simp only [copyCfg, guessCfg, hb]
  rw [δ_copy_blank]
  dsimp only
  refine Cfg.ext rfl ?_ ?_ ?_
  · simp only [idleDir, Nat.sub_zero]
    rfl
  · funext k
    by_cases hk : k = gIdx ng
    · subst hk
      simp only [↓reduceIte]
      exact idle_writeAndMove _ (gTape_read_ne_start g 0)
    · by_cases hk' : k = vIdx ng
      · subst hk'
        simp only [hk, ↓reduceIte, add_zero]
        rw [copyCells_length_succ z g]
        refine idle_writeAndMove _ ?_
        show guessCells z g 0 (z.length + 1) ≠ Γ.start
        rw [show z.length + 1 = z.length + 1 + 0 by rfl, guessCells_read_blank]
        decide
      · simp only [hk, hk', ↓reduceIte]
        exact idle_writeAndMove blank1 blank1_read_ne_start
  · exact idle_writeAndMove blank1 blank1_read_ne_start

theorem stepCfg_guessCfg (z : List Bool) (g : ℕ → Bool) (j : ℕ) (hj : j ≤ z.length) :
    (guessCopyTM ng).stepCfg (guessCfg ng z g j) = guessCfg ng z g (j + 1) := by
  have hns : (inpTape z (z.length + 1 - j)).read ≠ Γ.start :=
    inpTape_read_ne_start z _ (by omega)
  rw [stepCfg_eq]
  simp only [guessCfg]
  rw [δ_guess_bit _ _ _ hns]
  dsimp only
  apply Cfg.ext
  · rfl
  · show (inpTape z (z.length + 1 - j)).move Dir3.left = inpTape z (z.length + 1 - (j + 1))
    rw [inpTape_move_left]
    congr 1
  · funext k
    by_cases hk : k = gIdx ng
    · subst hk
      simp only [↓reduceIte, gIdx_ne_vIdx]
      rw [writeAndMove_readBack _ (gTape_read_ne_start g j)]
      rfl
    · by_cases hk' : k = vIdx ng
      · subst hk'
        simp only [hk, ↓reduceIte]
        rw [mk_writeAndMove_right _ _ _ (by omega),
          toΓ_readBackWrite_of_ne_start (gTape_read_ne_start g j), gTape_read,
          guessCells_succ_self]
        congr 1
      · simp only [hk, hk', ↓reduceIte]
        exact idle_writeAndMove blank1 blank1_read_ne_start
  · exact idle_writeAndMove blank1 blank1_read_ne_start

theorem stepCfg_guessCfg_last (z : List Bool) (g : ℕ → Bool) :
    (guessCopyTM ng).stepCfg (guessCfg ng z g (z.length + 1)) = doneCfg ng z g := by
  have hs : (inpTape z (z.length + 1 - (z.length + 1))).read = Γ.start := by
    rw [Nat.sub_self]; exact inpTape_read_zero z
  rw [stepCfg_eq]
  simp only [guessCfg, doneCfg, hs]
  rw [δ_guess_start]
  dsimp only
  refine Cfg.ext rfl ?_ ?_ ?_
  · rw [inpTape_move_right, Nat.sub_self]
  · funext k
    by_cases hk : k = gIdx ng
    · subst hk
      simp only [↓reduceIte]
      rw [writeAndMove_readBack _ (gTape_read_ne_start g _)]
      rfl
    · by_cases hk' : k = vIdx ng
      · subst hk'
        simp only [hk, ↓reduceIte]
        rw [idle_writeAndMove _ (by
          show guessCells z g (z.length + 1) (z.length + 1 + (z.length + 1)) ≠ Γ.start
          rw [guessCells_read_blank]; decide)]
        congr 1
        omega
      · simp only [hk, hk', ↓reduceIte]
        exact idle_writeAndMove blank1 blank1_read_ne_start
  · exact idle_writeAndMove blank1 blank1_read_ne_start

/-! ### The run of `guessCopyTM` -/

theorem copyCfg_state_ne (z : List Bool) (g : ℕ → Bool) (i : ℕ) :
    (copyCfg ng z g i).state ≠ (guessCopyTM ng).qhalt := by
  show GuessCopyPhase.copy ≠ GuessCopyPhase.done
  decide

theorem guessCfg_state_ne (z : List Bool) (g : ℕ → Bool) (j : ℕ) :
    (guessCfg ng z g j).state ≠ (guessCopyTM ng).qhalt := by
  show GuessCopyPhase.guess ≠ GuessCopyPhase.done
  decide

theorem doneCfg_halted (z : List Bool) (g : ℕ → Bool) :
    (doneCfg ng z g).state = (guessCopyTM ng).qhalt := rfl

theorem reachesIn_copyCfg (z : List Bool) (g : ℕ → Bool) :
    ∀ i, 1 ≤ i → i ≤ z.length + 1 →
      (guessCopyTM ng).reachesIn i (NTM.loadCfg (guessCopyTM ng) z g) (copyCfg ng z g i) := by
  intro i hi1 hi
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have h := step_of_not_halted (guessCopyTM ng) (c := NTM.loadCfg (guessCopyTM ng) z g)
        (by show GuessCopyPhase.copy ≠ GuessCopyPhase.done; decide)
      rw [stepCfg_loadCfg] at h
      exact reachesIn.step h reachesIn.zero
    · have h := step_of_not_halted (guessCopyTM ng) (copyCfg_state_ne z g i)
      rw [stepCfg_copyCfg z g i hpos (by omega)] at h
      exact reachesIn_snoc (ih hpos (by omega)) h

theorem reachesIn_guessCfg (z : List Bool) (g : ℕ → Bool) :
    ∀ j, j ≤ z.length + 1 →
      (guessCopyTM ng).reachesIn (z.length + 2 + j) (NTM.loadCfg (guessCopyTM ng) z g)
        (guessCfg ng z g j) := by
  intro j hj
  induction j with
  | zero =>
    have h := step_of_not_halted (guessCopyTM ng) (copyCfg_state_ne z g (z.length + 1))
    rw [stepCfg_copyCfg_last] at h
    exact reachesIn_snoc (reachesIn_copyCfg z g (z.length + 1) (by omega) le_rfl) h
  | succ j ih =>
    have h := step_of_not_halted (guessCopyTM ng) (guessCfg_state_ne z g j)
    rw [stepCfg_guessCfg z g j (by omega)] at h
    exact reachesIn_snoc (ih (by omega)) h

theorem reachesIn_doneCfg (z : List Bool) (g : ℕ → Bool) :
    (guessCopyTM ng).reachesIn (2 * z.length + 4) (NTM.loadCfg (guessCopyTM ng) z g)
      (doneCfg ng z g) := by
  have h := step_of_not_halted (guessCopyTM ng) (guessCfg_state_ne z g (z.length + 1))
  rw [stepCfg_guessCfg_last] at h
  have := reachesIn_snoc (reachesIn_guessCfg z g (z.length + 1) le_rfl) h
  rwa [show z.length + 2 + (z.length + 1) + 1 = 2 * z.length + 4 by omega] at this

/-! ## The verdict phase and the seed machine -/

/-- The deterministic verdict phase: rewind the virtual-input tape `ng` to cell `1`, then run the
verifier `D` on it. Lifted past the guess tape. -/
def verdictTM (ng : ℕ) (D : TM ng) : TM (ng + 2) :=
  seqTM (liftLast (rewindWorkTM (Fin.last ng))) (liftLast (retargetInputStarted D))

/-- The guess-reading deterministic machine: guess and copy, then compute the verdict. -/
def seedTM (ng : ℕ) (D : TM ng) : TM (ng + 2) := seqTM (guessCopyTM ng) (verdictTM ng D)

/-- The advancing states of `seedTM`: the `guess` state of the first phase. -/
def seedAdv (ng : ℕ) (D : TM ng) : (seedTM ng D).Q → Bool :=
  seqAdv guessCopyAdv (seqAdv (fun _ ↦ false) (fun _ ↦ false))

theorem guessProtocol_seedTM (ng : ℕ) (D : TM ng) :
    GuessProtocol (seedTM ng D) (seedAdv ng D) :=
  guessProtocol_seqTM (guessProtocol_guessCopyTM ng)
    (guessProtocol_seqTM (guessProtocol_liftLast _) (guessProtocol_liftLast _))

/-- **The seed machine**: the probabilistic machine denoted by `seedTM`. -/
def seedMachine (ng : ℕ) (D : TM ng) : NTM (ng + 1) := NTM.ofGuess (seedTM ng D)

theorem seedMachine_qstart_ne_qhalt (ng : ℕ) (D : TM ng) :
    (seedMachine ng D).qstart ≠ (seedMachine ng D).qhalt := by
  simp [seedMachine, seedTM, seqTM]

theorem seedAdv_inl_guess (ng : ℕ) (D : TM ng) :
    seedAdv ng D (Sum.inl GuessCopyPhase.guess) = true := by
  show (guessCopyAdv GuessCopyPhase.guess &&
    !decide (GuessCopyPhase.guess = GuessCopyPhase.done)) = true
  decide

theorem seedTM_qhalt (ng : ℕ) (D : TM ng) :
    (seedTM ng D).qhalt = Sum.inr (verdictTM ng D).qhalt := rfl

theorem inl_ne_seedTM_qhalt (ng : ℕ) (D : TM ng) (q : GuessCopyPhase) :
    (Sum.inl q : (seedTM ng D).Q) ≠ (seedTM ng D).qhalt := by
  simp [seedTM, seqTM]

/-- The loaded start configuration of `seedTM` is the embedding of that of `guessCopyTM`. -/
theorem loadCfg_seedTM (D : TM ng) (z : List Bool) (g : ℕ → Bool) :
    NTM.loadCfg (seedTM ng D) z g =
      phase1Wrap (guessCopyTM ng) (verdictTM ng D) (NTM.loadCfg (guessCopyTM ng) z g) := rfl

/-- During the guess phase, the seed machine is in the advancing state `guess` and its guess head
sits at cell `j + 1`. -/
theorem seedTM_traceD_guess (D : TM ng) (z : List Bool) (g : ℕ → Bool) (j : ℕ)
    (hj : j ≤ z.length + 1) :
    (seedTM ng D).traceD (z.length + 2 + j) (NTM.loadCfg (seedTM ng D) z g) =
      phase1Wrap (guessCopyTM ng) (verdictTM ng D) (guessCfg ng z g j) := by
  rw [loadCfg_seedTM]
  exact traceD_of_reachesIn _ _
    (seqTM_reachesIn_phase1Wrap (guessCopyTM ng) (verdictTM ng D) (reachesIn_guessCfg z g j hj))

theorem seedTM_traceD_guess_state (D : TM ng) (z : List Bool) (g : ℕ → Bool) (j : ℕ)
    (hj : j ≤ z.length + 1) :
    ((seedTM ng D).traceD (z.length + 2 + j) (NTM.loadCfg (seedTM ng D) z g)).state =
      Sum.inl GuessCopyPhase.guess := by
  rw [seedTM_traceD_guess D z g j hj]
  rfl

theorem seedTM_traceD_guess_work_last (D : TM ng) (z : List Bool) (g : ℕ → Bool) (j : ℕ)
    (hj : j ≤ z.length + 1) :
    ((seedTM ng D).traceD (z.length + 2 + j) (NTM.loadCfg (seedTM ng D) z g)).work
      (Fin.last (ng + 1)) = gTape g j := by
  rw [seedTM_traceD_guess D z g j hj]
  show (guessCfg ng z g j).work (Fin.last (ng + 1)) = gTape g j
  simp [guessCfg, last_eq_gIdx]

/-! ## The deterministic run of `seedTM` on a loaded guess tape -/

/-- The guessed bits `g 0, …, g (n - 1)` as a string. -/
def guessed (g : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n ↦ g i

@[simp] theorem guessed_length (g : ℕ → Bool) (n : ℕ) : (guessed g n).length = n := by
  simp [guessed]

theorem guessed_getElem (g : ℕ → Bool) (n i : ℕ) (hi : i < n) :
    (guessed g n)[i]'(by simp [hi]) = g i := by
  simp [guessed]

/-- The virtual-input tape after the guess phase holds `z ++ guessed g (|z| + 1)`. -/
theorem guessCells_eq_init (z : List Bool) (g : ℕ → Bool) :
    guessCells z g (z.length + 1) =
      (Tape.init ((z ++ guessed g (z.length + 1)).map Γ.ofBool)).cells := by
  funext p
  rcases p with _ | q
  · simp [guessCells]
  · rw [Tape.init_cells_succ, List.getElem?_map]
    simp only [guessCells]
    by_cases hq : q < z.length
    · rw [ite_eq_left (by omega), Tape.init_cells_succ, List.getElem?_map,
        List.getElem?_append_left hq]
    · rw [ite_eq_right (by omega)]
      by_cases hq2 : q + 1 ≤ z.length + (z.length + 1)
      · rw [ite_eq_left hq2, List.getElem?_append_right (by omega),
          List.getElem?_eq_getElem (by simp; omega), guessed_getElem]
        · simp only [Option.map_some, Option.getD_some]
          congr 2
          omega
        · omega
      · rw [ite_eq_right hq2, List.getElem?_eq_none (by simp; omega)]
        rfl

theorem guessCells_ne_start (z : List Bool) (g : ℕ → Bool) (j p : ℕ) (hp : 1 ≤ p) :
    guessCells z g j p ≠ Γ.start := by
  simp only [guessCells]
  split_ifs
  · exact Tape.init_ofBool_cells_ne_start z p hp
  · exact Γ.ofBool_ne_start _
  · decide

theorem guessCells_zero (z : List Bool) (g : ℕ → Bool) (j : ℕ) :
    guessCells z g j 0 = Γ.start := by
  simp [guessCells]

/-- A run bound for the seed machine on inputs of length `m`, given the verifier bound `q`. -/
def seedBound (q : Polynomial ℕ) (m : ℕ) : ℕ := 4 * m + 10 + q.eval (2 * m + 1)

theorem seedBound_mono (q : Polynomial ℕ) : Monotone (seedBound q) := by
  intro a b hab
  have h2 : q.eval (2 * a + 1) ≤ q.eval (2 * b + 1) :=
    polynomial_eval_mono_nat q (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  show 4 * a + 10 + q.eval (2 * a + 1) ≤ 4 * b + 10 + q.eval (2 * b + 1)
  omega

/-- The contract of the guess-and-copy phase, at the loaded start tapes. -/
theorem guessCopyTM_hoareTime (z : List Bool) (g : ℕ → Bool) :
    (guessCopyTM ng).HoareTime
      (fun inp work out ↦ inp = Tape.init (z.map Γ.ofBool) ∧
        work = Fin.snoc (fun _ ↦ Tape.init []) (NTM.loadTape g) ∧ out = Tape.init [])
      (fun inp work out ↦ inp = inpTape z 1 ∧ work = (doneCfg ng z g).work ∧ out = blank1)
      (2 * z.length + 4) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact ⟨doneCfg ng z g, 2 * z.length + 4, le_rfl, reachesIn_doneCfg z g, rfl, rfl, rfl, rfl⟩

/-- The work tapes after rewinding the virtual input. -/
def vinWork (ng : ℕ) (z : List Bool) (g : ℕ → Bool) : Fin (ng + 2) → Tape :=
  fun k ↦ if k = gIdx ng then gTape g (z.length + 2)
    else if k = vIdx ng then ⟨1, guessCells z g (z.length + 1)⟩ else blank1

theorem castSucc_eq_vIdx_iff (i : Fin (ng + 1)) : i.castSucc = vIdx ng ↔ i = Fin.last ng := by
  rw [vIdx_eq_castSucc_last, Fin.castSucc_inj]

theorem castSucc_ne_gIdx (i : Fin (ng + 1)) : i.castSucc ≠ gIdx ng :=
  (Fin.castSucc_lt_last i).ne

theorem doneCfg_work_castSucc (z : List Bool) (g : ℕ → Bool) (i : Fin (ng + 1)) :
    (doneCfg ng z g).work i.castSucc =
      if i = Fin.last ng then ⟨2 * z.length + 2, guessCells z g (z.length + 1)⟩ else blank1 := by
  simp only [doneCfg, castSucc_ne_gIdx, ↓reduceIte, castSucc_eq_vIdx_iff]

theorem doneCfg_work_gIdx (z : List Bool) (g : ℕ → Bool) :
    (doneCfg ng z g).work (gIdx ng) = gTape g (z.length + 2) := by
  simp [doneCfg]

/-- The rewind phase, lifted past the guess tape. -/
theorem liftLast_rewind_hoareTime (z : List Bool) (g : ℕ → Bool) :
    (liftLast (rewindWorkTM (Fin.last ng))).HoareTime
      (fun inp work out ↦ inp = inpTape z 1 ∧ work = (doneCfg ng z g).work ∧ out = blank1)
      (fun inp work out ↦ inp = inpTape z 1 ∧ work = vinWork ng z g ∧ out = blank1)
      (2 * z.length + 2 + 2) := by
  have hR := rewindWorkTM_hoareTime_frame (n := ng + 1) (Fin.last ng) (2 * z.length + 2)
    (P := fun inp work out ↦ inp = inpTape z 1 ∧ out = blank1 ∧
      (work (Fin.last ng)).cells = guessCells z g (z.length + 1) ∧
      ∀ i, i ≠ Fin.last ng → work i = blank1)
    (by
      rintro inp work out inp' work' out' ⟨hinp, hout, hcells, hother⟩ hc _ hoth rfl hoc hoh
      refine ⟨hinp, ?_, hc.trans hcells, fun i hi ↦ (hoth i hi).trans (hother i hi)⟩
      rw [← hout]
      exact Tape.ext hoh hoc)
  have hL := liftLast_hoareTime _ hR (gTape g (z.length + 2)) (gTape_read_ne_start _ _)
  refine hL.consequence ?_ ?_ le_rfl
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨doneCfg_work_gIdx z g, ?_⟩
    simp only [doneCfg_work_castSucc, ↓reduceIte]
    refine ⟨guessCells_zero z g _, fun j hj ↦ guessCells_ne_start z g _ j hj, le_rfl,
      inpTape_read_ne_start z 1 le_rfl, blank1_read_ne_start, le_rfl, fun i hi ↦ ?_, by trivial,
      by trivial, by trivial, fun i hi ↦ ?_⟩
    · rw [ite_eq_right hi]
      exact ⟨blank1_read_ne_start, le_rfl⟩
    · rw [ite_eq_right hi]
  · rintro inp work out ⟨hlast, hhead, hinp, hout, hcells, hother⟩
    refine ⟨hinp, ?_, hout⟩
    funext k
    refine Fin.lastCases ?_ ?_ k
    · rw [vinWork, ite_eq_left (last_eq_gIdx ng)]
      exact hlast
    · intro i
      rw [vinWork, ite_eq_right (castSucc_ne_gIdx i)]
      by_cases hi : i = Fin.last ng
      · subst hi
        rw [ite_eq_left (vIdx_eq_castSucc_last ng).symm]
        exact Tape.ext hhead hcells
      · rw [ite_eq_right ((castSucc_eq_vIdx_iff i).not.mpr hi)]
        exact hother i hi

/-- The verifier phase, lifted past the guess tape. -/
theorem liftLast_retarget_hoareTime (D : TM ng) {G : List Bool → List Bool} {TD : ℕ → ℕ}
    (hD : D.ComputesInTime G TD) (z : List Bool) (g : ℕ → Bool) :
    (liftLast (retargetInputStarted D)).HoareTime
      (fun inp work out ↦ inp = inpTape z 1 ∧ work = vinWork ng z g ∧ out = blank1)
      (fun _ _ out ↦ out.HasOutput (G (z ++ guessed g (z.length + 1))))
      (TD (z ++ guessed g (z.length + 1)).length) := by
  have hL := liftLast_hoareTime _
    (retargetInputStarted_hoareTime D hD (z ++ guessed g (z.length + 1)))
    (gTape g (z.length + 2)) (gTape_read_ne_start _ _)
  refine hL.consequence ?_ ?_ le_rfl
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨by simp [vinWork, last_eq_gIdx], ?_, rfl⟩
    funext i
    simp only [vinWork, castSucc_ne_gIdx, ↓reduceIte, castSucc_eq_vIdx_iff,
      retargetInputStartedCfg]
    by_cases hi : i.val < ng
    · rw [ite_eq_right (by intro h; rw [h] at hi; simp at hi), ite_eq_left hi]
      rfl
    · rw [ite_eq_left (Fin.ext (by have := i.isLt; simp; omega)), ite_eq_right hi]
      refine Tape.ext rfl ?_
      rw [Tape.move_cells, guessCells_eq_init]
  · rintro inp work out ⟨-, h⟩
    exact h

/-- Boundary tapes with heads off the left marker pass through a combinator seam unchanged. -/
theorem transition_vinWork (z : List Bool) (g : ℕ → Bool) (k : Fin (ng + 2)) :
    transitionTape (vinWork ng z g k) = vinWork ng z g k := by
  refine transitionTape_eq_self ?_
  simp only [vinWork]
  split_ifs
  · exact gTape_read_ne_start _ _
  · exact guessCells_ne_start z g _ 1 le_rfl
  · exact blank1_read_ne_start

theorem transition_doneCfg_work (z : List Bool) (g : ℕ → Bool) (k : Fin (ng + 2)) :
    transitionTape ((doneCfg ng z g).work k) = (doneCfg ng z g).work k := by
  refine transitionTape_eq_self ?_
  simp only [doneCfg]
  split_ifs
  · exact gTape_read_ne_start _ _
  · show guessCells z g (z.length + 1) (2 * z.length + 2) ≠ Γ.start
    exact guessCells_ne_start z g _ _ (by omega)
  · exact blank1_read_ne_start

/-- The contract of the whole verdict phase. -/
theorem verdictTM_hoareTime (D : TM ng) {G : List Bool → List Bool} {TD : ℕ → ℕ}
    (hD : D.ComputesInTime G TD) (z : List Bool) (g : ℕ → Bool) :
    (verdictTM ng D).HoareTime
      (fun inp work out ↦ inp = inpTape z 1 ∧ work = (doneCfg ng z g).work ∧ out = blank1)
      (fun _ _ out ↦ out.HasOutput (G (z ++ guessed g (z.length + 1))))
      (2 * z.length + 2 + 2 + 1 + TD (z ++ guessed g (z.length + 1)).length) :=
  seqTM_hoareTime _ _ (liftLast_rewind_hoareTime z g)
    (fun inp work out ⟨hinp, hwork, hout⟩ ↦ by
      subst hinp hwork hout
      refine ⟨transitionInput_eq_self (inpTape_read_ne_start z 1 le_rfl), ?_,
        transitionTape_eq_self blank1_read_ne_start⟩
      funext k
      exact transition_vinWork z g k)
    (liftLast_retarget_hoareTime D hD z g)

/-- The contract of the seed machine's deterministic reading. -/
theorem seedTM_hoareTime (D : TM ng) {G : List Bool → List Bool} {q : Polynomial ℕ}
    (hD : D.ComputesInTime G q.eval) (z : List Bool) (g : ℕ → Bool) :
    (seedTM ng D).HoareTime
      (fun inp work out ↦ inp = Tape.init (z.map Γ.ofBool) ∧
        work = Fin.snoc (fun _ ↦ Tape.init []) (NTM.loadTape g) ∧ out = Tape.init [])
      (fun _ _ out ↦ out.HasOutput (G (z ++ guessed g (z.length + 1))))
      (seedBound q z.length) := by
  have h := seqTM_hoareTime _ _ (guessCopyTM_hoareTime (ng := ng) z g)
    (fun inp work out ⟨hinp, hwork, hout⟩ ↦ by
      subst hinp hwork hout
      refine ⟨transitionInput_eq_self (inpTape_read_ne_start z 1 le_rfl), ?_,
        transitionTape_eq_self blank1_read_ne_start⟩
      funext k
      exact transition_doneCfg_work z g k)
    (verdictTM_hoareTime D hD z g)
  refine h.consequence (fun _ _ _ hp ↦ hp) (fun _ _ _ hp ↦ hp) ?_
  simp only [seedBound, List.length_append, guessed_length]
  have : q.eval (z.length + (z.length + 1)) = q.eval (2 * z.length + 1) := by
    congr 1; omega
  omega

/-- **The deterministic run of the seed machine on a loaded guess tape** halts within
`seedBound q |z|` steps with the verdict `G (z ++ guessed g (|z| + 1))` on the output tape. -/
theorem seedTM_run (D : TM ng) {G : List Bool → List Bool} {q : Polynomial ℕ}
    (hD : D.ComputesInTime G q.eval) (z : List Bool) (g : ℕ → Bool) :
    ∃ (c' : Cfg (ng + 2) (seedTM ng D).Q) (t : ℕ), t ≤ seedBound q z.length ∧
      (seedTM ng D).reachesIn t (NTM.loadCfg (seedTM ng D) z g) c' ∧ (seedTM ng D).halted c' ∧
      c'.output.HasOutput (G (z ++ guessed g (z.length + 1))) :=
  seedTM_hoareTime D hD z g _ _ _ ⟨rfl, rfl, rfl⟩

/-- For any clock `T ≥ seedBound q |z|`, the `T`-step trace is that halting configuration. -/
theorem seedTM_traceD (D : TM ng) {G : List Bool → List Bool} {q : Polynomial ℕ}
    (hD : D.ComputesInTime G q.eval) (z : List Bool) (g : ℕ → Bool) {T : ℕ}
    (hT : seedBound q z.length ≤ T) :
    (seedTM ng D).halted ((seedTM ng D).traceD T (NTM.loadCfg (seedTM ng D) z g)) ∧
      ((seedTM ng D).traceD T (NTM.loadCfg (seedTM ng D) z g)).output.HasOutput
        (G (z ++ guessed g (z.length + 1))) := by
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := seedTM_run D hD z g
  rw [traceD_of_reachesIn_halted _ (ht.trans hT) hreach hhalt]
  exact ⟨hhalt, hout⟩

/-! ## The seed machine along a choice sequence -/

/-- A finite choice sequence extended by `false`. -/
def extChoices {T : ℕ} (choices : Fin T → Bool) : ℕ → Bool :=
  fun i ↦ if h : i < T then choices ⟨i, h⟩ else false

theorem extChoices_lt {T : ℕ} (choices : Fin T → Bool) {i : ℕ} (hi : i < T) :
    extChoices choices i = choices ⟨i, hi⟩ := by
  simp [extChoices, hi]

theorem fun_extChoices {T : ℕ} (choices : Fin T → Bool) :
    (fun i : Fin T ↦ extChoices choices i.val) = choices := by
  funext i
  exact extChoices_lt choices i.isLt

/-- The bits the seed machine feeds to the verifier: choices `|z| + 2, …, 2|z| + 2`. -/
def seedWindow (z : List Bool) {T : ℕ} (hT : 2 * z.length + 3 ≤ T) (choices : Fin T → Bool) :
    List Bool :=
  List.ofFn fun i : Fin (z.length + 1) ↦ choices ⟨z.length + 2 + i, by omega⟩

/-- **The seed machine along a choice sequence**: with a clock of at least `seedBound q |z|`, every
path halts, with the verifier's verdict on `z ++ seedWindow` on the output tape. -/
theorem seedMachine_trace (D : TM ng) {G : List Bool → List Bool} {q : Polynomial ℕ}
    (hD : D.ComputesInTime G q.eval) (z : List Bool) {T : ℕ} (hT : seedBound q z.length ≤ T)
    (choices : Fin T → Bool) :
    ((seedMachine ng D).trace T choices ((seedMachine ng D).initCfg z)).state =
        (seedMachine ng D).qhalt ∧
      ((seedMachine ng D).trace T choices ((seedMachine ng D).initCfg z)).output.HasOutput
        (G (z ++ seedWindow z (by simp only [seedBound] at hT; omega) choices)) := by
  have hT' : 2 * z.length + 3 ≤ T := by simp only [seedBound] at hT; omega
  show ((NTM.ofGuess (seedTM ng D)).trace T choices ((NTM.ofGuess (seedTM ng D)).initCfg z)).state =
      (NTM.ofGuess (seedTM ng D)).qhalt ∧
    ((NTM.ofGuess (seedTM ng D)).trace T choices
      ((NTM.ofGuess (seedTM ng D)).initCfg z)).output.HasOutput (G (z ++ seedWindow z hT' choices))
  have hP := guessProtocol_seedTM ng D
  have hmain := NTM.traceD_guessOf (seedTM ng D) (extChoices choices)
    ((NTM.ofGuess (seedTM ng D)).initCfg z) hP T
  have hbit : ∀ i, i < T →
      NTM.consumes (seedTM ng D) (seedAdv ng D) (extChoices choices)
        ((NTM.ofGuess (seedTM ng D)).initCfg z) i = true →
      NTM.guessOf (seedTM ng D) (seedAdv ng D) (extChoices choices)
        ((NTM.ofGuess (seedTM ng D)).initCfg z) T
        (NTM.cursor (seedTM ng D) (seedAdv ng D) (extChoices choices)
          ((NTM.ofGuess (seedTM ng D)).initCfg z) i - 1) = extChoices choices i :=
    fun i hi hc ↦ NTM.guessOf_eq _ _ _ _ hi hc
  generalize hg : NTM.guessOf (seedTM ng D) (seedAdv ng D) (extChoices choices)
    ((NTM.ofGuess (seedTM ng D)).initCfg z) T = g at hmain hbit
  replace hmain : ∀ i ≤ T,
      NTM.dropChoice ((seedTM ng D).traceD i (NTM.loadCfg (seedTM ng D) z g)) =
          NTM.nrunAt (NTM.ofGuess (seedTM ng D)) (extChoices choices)
            ((NTM.ofGuess (seedTM ng D)).initCfg z) i ∧
        ((seedTM ng D).traceD i (NTM.loadCfg (seedTM ng D) z g)).work (Fin.last (ng + 1)) =
          ⟨NTM.cursor (seedTM ng D) (seedAdv ng D) (extChoices choices)
            ((NTM.ofGuess (seedTM ng D)).initCfg z) i, (NTM.loadTape g).cells⟩ := hmain
  have htrace : (NTM.ofGuess (seedTM ng D)).trace T choices
      ((NTM.ofGuess (seedTM ng D)).initCfg z) =
      NTM.dropChoice ((seedTM ng D).traceD T (NTM.loadCfg (seedTM ng D) z g)) := by
    rw [(hmain T le_rfl).1]
    conv_lhs => rw [← fun_extChoices choices]
    exact NTM.trace_eq_nrunAt _ _ T _
  have hbits : ∀ j (hj : j ≤ z.length), g j = choices ⟨z.length + 2 + j, by omega⟩ := by
    intro j hj
    have hi : z.length + 2 + j < T := by omega
    obtain ⟨h1, h2⟩ := hmain (z.length + 2 + j) hi.le
    have hstate : (NTM.nrunAt (NTM.ofGuess (seedTM ng D)) (extChoices choices)
        ((NTM.ofGuess (seedTM ng D)).initCfg z) (z.length + 2 + j)).state =
        Sum.inl GuessCopyPhase.guess := by
      rw [← h1]
      exact seedTM_traceD_guess_state D z g j (by omega)
    have hcons : NTM.consumes (seedTM ng D) (seedAdv ng D) (extChoices choices)
        ((NTM.ofGuess (seedTM ng D)).initCfg z) (z.length + 2 + j) = true := by
      unfold NTM.consumes
      rw [hstate]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨@decide_eq_false _ ((seedTM ng D).decEq _ _) (inl_ne_seedTM_qhalt ng D _),
        seedAdv_inl_guess ng D⟩
    have hcur : NTM.cursor (seedTM ng D) (seedAdv ng D) (extChoices choices)
        ((NTM.ofGuess (seedTM ng D)).initCfg z) (z.length + 2 + j) = j + 1 := by
      have := congrArg Tape.head h2
      rw [seedTM_traceD_guess_work_last D z g j (by omega)] at this
      exact this.symm
    have := hbit _ hi hcons
    rw [hcur, Nat.add_sub_cancel] at this
    rw [this]
    exact extChoices_lt choices hi
  obtain ⟨hhalt, hout⟩ := seedTM_traceD D hD z g hT
  have hwin : guessed g (z.length + 1) = seedWindow z hT' choices := by
    simp only [guessed, seedWindow]
    congr 1
    funext i
    exact hbits i (by omega)
  rw [hwin] at hout
  rw [htrace]
  exact ⟨hhalt, hout⟩

/-! ## The polynomial-time ingredients -/

/-- The padding of the input by a unary ruler of length `ℓ(|x|)`. -/
noncomputable def padInput (ℓ : Polynomial ℕ) (x : List Bool) : List Bool :=
  pair x (polyRuler ℓ x)

theorem padInput_mem_FP (ℓ : Polynomial ℕ) : padInput ℓ ∈ FP :=
  Cobham.pairFn_mem_FP id_mem_FP (polyRulerFn_mem_FP ℓ id_mem_FP)

theorem padInput_length (ℓ : Polynomial ℕ) (x : List Bool) :
    (padInput ℓ x).length = 2 * x.length + 2 + ℓ.eval x.length := by
  simp [padInput]

/-- The verdict flag: from `w = pair x (u ++ r')` (with `|u| = ℓ(|x|)`) compute whether
`V (pair x (first ℓ(|x|) bits of r'))` is `[true]`, as the one-bit flag `[true]`/`[false]`. -/
noncomputable def verdictFlag (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (w : List Bool) :
    List Bool :=
  Cobham.eqFlag (V (pair (pairFst w)
    (((pairSnd w).drop (ℓ.eval (pairFst w).length)).take (ℓ.eval (pairFst w).length)))) [true]

theorem verdictFlag_mem_FP {V : List Bool → List Bool} (hV : V ∈ FP) (ℓ : Polynomial ℕ) :
    verdictFlag V ℓ ∈ FP := by
  apply CobhamFP_subset_FP
  show Cobham fun v : Fin 1 → List Bool ↦ verdictFlag V ℓ (v 0)
  have h1 : Cobham fun v : Fin 1 → List Bool ↦ pairFst (v 0) := FP_subset_CobhamFP pairFst_mem_FP
  have h2 : Cobham fun v : Fin 1 → List Bool ↦ pairSnd (v 0) := FP_subset_CobhamFP pairSnd_mem_FP
  have hr : Cobham fun v : Fin 1 → List Bool ↦ Cobham.polyLen ℓ (pairFst (v 0)) :=
    Cobham.polyLen_mem ℓ h1
  have htake := Cobham.takeFn hr (Cobham.dropFn hr h2)
  have hpair : Cobham fun v : Fin 1 → List Bool ↦ pair (pairFst (v 0))
      (((pairSnd (v 0)).drop (Cobham.polyLen ℓ (pairFst (v 0))).length).take
        (Cobham.polyLen ℓ (pairFst (v 0))).length) :=
    (Cobham.comp₂ Cobham.pairing h1 htake).of_eq fun v ↦ by simp
  have hV' : Cobham fun v : Fin 1 → List Bool ↦ V (v 0) := FP_subset_CobhamFP hV
  have hVc := Cobham.comp hV' (gs := fun _ ↦ fun v : Fin 1 → List Bool ↦ pair (pairFst (v 0))
      (((pairSnd (v 0)).drop (Cobham.polyLen ℓ (pairFst (v 0))).length).take
        (Cobham.polyLen ℓ (pairFst (v 0))).length)) fun _ ↦ hpair
  exact (Cobham.eqFlag_mem hVc (Cobham.const [true])).of_eq fun v ↦ by
    simp [verdictFlag, Cobham.polyLen_length]

theorem verdictFlag_flag (V : List Bool → List Bool) (ℓ : Polynomial ℕ) (w : List Bool) :
    verdictFlag V ℓ w = [true] ∨ verdictFlag V ℓ w = [false] :=
  Cobham.eqFlag_flag _ _

/-- The verdict flag on `padInput ℓ x ++ r'` is the verdict on the first `ℓ(|x|)` bits of `r'`. -/
theorem verdictFlag_padInput_append (V : List Bool → List Bool) (ℓ : Polynomial ℕ)
    (x r' : List Bool) :
    verdictFlag V ℓ (padInput ℓ x ++ r') = [true] ↔
      V (pair x (r'.take (ℓ.eval x.length))) = [true] := by
  have hw : padInput ℓ x ++ r' = pair x (polyRuler ℓ x ++ r') := by
    simp [padInput, pair, List.append_assoc]
  rw [verdictFlag, Cobham.eqFlag_eq_true_iff, hw, pairFst_pair, pairSnd_pair,
    List.drop_left' (polyRuler_length ℓ x)]

/-- A one-bit flag on the output tape: cell `1` is `1` iff the flag is `[true]`. -/
theorem hasOutput_flag_cells_one {t : Tape} {f : List Bool} (hf : f = [true] ∨ f = [false])
    (h : t.HasOutput f) : t.cells 1 = Γ.one ↔ f = [true] := by
  rcases hf with rfl | rfl
  · have := h.1 0 (by simp)
    simp only [zero_add, List.getElem_cons_zero] at this
    exact ⟨fun _ ↦ rfl, fun _ ↦ this⟩
  · have := h.1 0 (by simp)
    simp only [zero_add, List.getElem_cons_zero] at this
    rw [this]
    simp [Γ.ofBool]

/-! ## Probability of an event depending on a window of the random bits -/

theorem eventProb_window {T a m : ℕ} (h : a + m ≤ T) (E : Finset (Fin m → Bool)) :
    eventProb (Finset.univ.filter fun w : Fin T → Bool ↦
        (fun i : Fin m ↦ w ⟨a + i, by omega⟩) ∈ E) = eventProb E := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := eventProb_block (a := a + m) (b := b)
    (fun v : Fin (a + m) → Bool ↦ (fun i : Fin m ↦ v ⟨a + i, by omega⟩) ∈ E) (fun _ ↦ True)
  have h2 := eventProb_block (a := a) (b := m) (fun _ : Fin a → Bool ↦ True)
    (fun v : Fin m → Bool ↦ v ∈ E)
  simp only [and_true, true_and, Finset.filter_true, eventProb_univ, mul_one, one_mul,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at h1 h2
  calc eventProb (Finset.univ.filter fun w : Fin (a + m + b) → Bool ↦
          (fun i : Fin m ↦ w ⟨a + i, by omega⟩) ∈ E)
      = eventProb (Finset.univ.filter fun w : Fin (a + m + b) → Bool ↦
          (fun i : Fin m ↦ blockFst (a + m) b w ⟨a + i, by omega⟩) ∈ E) := rfl
    _ = eventProb (Finset.univ.filter fun v : Fin (a + m) → Bool ↦
          (fun i : Fin m ↦ v ⟨a + i, by omega⟩) ∈ E) := h1
    _ = eventProb (Finset.univ.filter fun v : Fin (a + m) → Bool ↦ blockSnd a m v ∈ E) := rfl
    _ = eventProb E := h2

/-! ## The final machine -/

/-- The run bound of the composite machine: `4·p(n) + 11` for the padding computation, then the
seed machine's bound at input length `p(n)`. -/
def totalBound (p q : Polynomial ℕ) (n : ℕ) : ℕ := 4 * p.eval n + 11 + seedBound q (p.eval n)

/-- The run bound as a polynomial. -/
noncomputable def totalPoly (p q : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 4 * p + Polynomial.C 11 +
    (Polynomial.C 4 * p + Polynomial.C 10 + q.comp (Polynomial.C 2 * p + Polynomial.C 1))

theorem totalBound_eq_eval (p q : Polynomial ℕ) (n : ℕ) :
    totalBound p q n = (totalPoly p q).eval n := by
  simp [totalBound, totalPoly, seedBound, Polynomial.eval_comp]

theorem totalBound_bigO (p q : Polynomial ℕ) :
    totalBound p q =O (· ^ (totalPoly p q).natDegree) :=
  BigO.of_polynomial_bound (totalPoly p q) fun n ↦ (totalBound_eq_eval p q n).le

/-- The accepting event of the composite machine on `x`, in terms of the verdict on a window of
`ℓ(|x|)` random bits, for every clock `T ≥ totalBound p q |x|`. -/
theorem composite_accept_iff {nf ng : ℕ} {tmF : TM nf} {D : TM ng} {V : List Bool → List Bool}
    {ℓ p q : Polynomial ℕ} (hF : tmF.ComputesInTime (padInput ℓ) p.eval)
    (hD : D.ComputesInTime (verdictFlag V ℓ) q.eval) (x : List Bool) :
    ∃ (a : ℕ) (_ : a + ℓ.eval x.length ≤ totalBound p q x.length),
      ∀ (T : ℕ) (_ : totalBound p q x.length ≤ T) (choices : Fin T → Bool),
        let c := (NTM.compositionNTM tmF (seedMachine ng D)).trace T choices
          ((NTM.compositionNTM tmF (seedMachine ng D)).initCfg x)
        c.state = (NTM.compositionNTM tmF (seedMachine ng D)).qhalt ∧
          (c.output.cells 1 = Γ.one ↔
            V (pair x (List.ofFn fun i : Fin (ℓ.eval x.length) ↦ choices ⟨a + i, by omega⟩)) =
              [true]) := by
  obtain ⟨E, t, ht, -, hrun⟩ := NTM.compositionNTM_trace_run tmF (seedMachine ng D) hF x
    (seedMachine_qstart_ne_qhalt ng D)
  have hzlen : (padInput ℓ x).length ≤ p.eval x.length := hF.output_length_le x
  have hsb := seedBound_mono q hzlen
  have hℓ : ℓ.eval x.length ≤ (padInput ℓ x).length + 1 := by
    rw [padInput_length]; omega
  refine ⟨(padInput ℓ x).length + 2 + t, by simp only [totalBound, seedBound] at *; omega, ?_⟩
  intro T hT choices
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 + t := ⟨T - t - 1, by simp only [totalBound] at hT; omega⟩
  have hsT : seedBound q (padInput ℓ x).length ≤ s + 1 := by
    simp only [totalBound] at hT; omega
  obtain ⟨hstate, hout⟩ := seedMachine_trace D hD (padInput ℓ x) hsT
    (fun i : Fin (s + 1) ↦ choices ⟨i.val + t, by omega⟩)
  simp only [hrun s choices]
  refine ⟨(NTM.placedCfg_halted_iff _ _ _ _ _).mpr hstate, ?_⟩
  rw [NTM.placedCfg_output, hasOutput_flag_cells_one (verdictFlag_flag V ℓ _) hout,
    verdictFlag_padInput_append]
  simp only [seedWindow]
  refine Iff.of_eq (congrArg (fun r ↦ V (pair x r) = [true]) ?_)
  refine List.ext_getElem (by simp; omega) fun i hi₁ hi₂ ↦ ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  congr 1
  ext
  simp only
  omega

/-- **Random tape ⇒ PTM**, machine form. -/
theorem mem_BPP_of_randomTape_machine {L : Language} {V : List Bool → List Bool}
    {ℓ : Polynomial ℕ} (hV : V ∈ FP) (h : RandomTapeSolves (PromiseProblem.ofLanguage L) V ℓ) :
    L ∈ BPP := by
  obtain ⟨nf, tmF, p, hF⟩ := mem_FP_iff_computesInTime_polynomial.mp (padInput_mem_FP ℓ)
  obtain ⟨ng, D, q, hD⟩ := mem_FP_iff_computesInTime_polynomial.mp (verdictFlag_mem_FP hV ℓ)
  set N := NTM.compositionNTM tmF (seedMachine ng D) with hN
  have hprob : ∀ x : List Bool, N.acceptProb x (totalBound p q x.length) =
      eventProb (Finset.univ.filter fun r : Fin (ℓ.eval x.length) → Bool ↦
        V (pair x (List.ofFn r)) = [true]) := by
    intro x
    obtain ⟨a, ha, hacc⟩ := composite_accept_iff hF hD x
    rw [NTM.acceptProb_eq_eventProb, ← eventProb_window ha]
    congr 1
    ext choices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨hstate, hout⟩ := hacc _ le_rfl choices
    rw [hout]
    exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hstate, h'⟩⟩
  have hpromise : ∀ x : List Bool, x ∈ (PromiseProblem.ofLanguage L).promise := by
    intro x
    by_cases hx : x ∈ L
    · exact Or.inl hx
    · exact Or.inr hx
  refine Set.mem_iUnion.mpr ⟨(totalPoly p q).natDegree, _, N, totalBound p q, ?_, ?_, ?_,
    totalBound_bigO p q⟩
  · intro x choices
    obtain ⟨a, ha, hacc⟩ := composite_accept_iff hF hD x
    exact (hacc _ le_rfl choices).1
  · intro x hx
    rw [ge_iff_le, hprob x]
    refine (h x (hpromise x)).trans (le_of_eq ?_)
    congr 1
    ext r
    simp only [goodVerdictSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h' ↦ h'.mpr hx, fun h' ↦ ⟨fun _ ↦ hx, fun _ ↦ h'⟩⟩
  · intro x hx
    rw [hprob x]
    have hgood := h x (hpromise x)
    have hcompl : goodVerdictSeeds (PromiseProblem.ofLanguage L) V x (ℓ.eval x.length) =
        (Finset.univ.filter fun r : Fin (ℓ.eval x.length) → Bool ↦
          V (pair x (List.ofFn r)) = [true])ᶜ := by
      rw [Finset.compl_filter]
      ext r
      simp only [goodVerdictSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h' h'' ↦ hx (h'.mp h''),
        fun h' ↦ ⟨fun h'' ↦ absurd h'' h', fun h'' ↦ absurd h'' hx⟩⟩
    rw [hcompl, eventProb_compl] at hgood
    linarith

end SparseDiv
