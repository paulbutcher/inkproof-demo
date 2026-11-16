/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Viewport

namespace Inkproof.Demo.Robot

open Inkproof.Viewport

/-- `n` charts that share an x axis, all linked. -/
def home (c : ViewConfig Float) (n : Nat) : Linked Float n :=
  { x := ⟨c.x.home⟩, y := fun _ => c.y.home }

theorem home_view (c : ViewConfig Float) (n : Nat) (i : Fin n) :
    (home c n).view i = View.home c := by simp [home, Linked.view, View.home]

/-- Small deterministic generator, so a failing run replays from its seed. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

theorem next_lt (s : Nat) : next s < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem next_mod (s : Nat) : next (s % 2 ^ 64) = next s := by
  simp [next, Nat.add_mod, Nat.mul_mod]

/-- A value below `m` (at least 1) and the following state. -/
def below (s m : Nat) : Nat × Nat :=
  let s := next s
  (s / 2 ^ 20 % (m + 1), s)

theorem below_eq (s m : Nat) : below s m = (next s / 2 ^ 20 % (m + 1), next s) := rfl

theorem below_lt (s m : Nat) : (below s m).1 < m + 1 := Nat.mod_lt _ (Nat.succ_pos m)

/-- `action`, `violation` and `run` are checked by running them: their results are decided by float
comparisons, which have no lemmas to prove against. -/
inductive Action (n : Nat) where
  | input (i : Fin n) (inp : Input Float)
  | toggle (i : Fin n)

private def key (k : Nat) : Key :=
  match k % 6 with
  | 0 => .zoomIn | 1 => .zoomOut | 2 => .left | 3 => .right | 4 => .up | _ => .down

/-- Inputs of every kind, including factors that are zero and boxes that are empty or inverted. -/
def action (n : Nat) (hn : 0 < n) (s : Nat) : Action n × Nat :=
  let (k, s) := below s 9
  let (i, s) := below s (n - 1)
  let (a, s) := below s 800
  let (b, s) := below s 400
  let (c, s) := below s 800
  let (d, s) := below s 400
  let i : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩
  let a := a.toFloat
  let b := b.toFloat
  let c := c.toFloat
  let d := d.toFloat
  (match k with
   | 0 | 1 => .input i (.wheel a b (c / 200))
   | 2 => .input i (.pinch a b (c / 200) (d / 100))
   | 3 | 4 => .input i (.drag (a - 400) (b - 200))
   | 5 => .input i (.key (key (c.toUInt64.toNat)))
   | 6 => .input i (.box a b c d)
   | 7 => .toggle i
   | 8 => .input i (.set (a - 400) (c - 400) (b - 200) (d - 200))
   | _ => .input i .reset, s)

def near (a b : Float) : Bool := (a - b).abs ≤ 1e-6 * (1 + a.abs + b.abs)

theorem near_eq (a b : Float) : near a b = decide ((a - b).abs ≤ 1e-6 * (1 + a.abs + b.abs)) := rfl

private def within (c : Interval.Config Float) (a : Interval Float) : Bool :=
  c.minSpan ≤ a.span && a.span ≤ c.maxSpan

/-- The first broken property after `a` takes `r` to `r'`: a limit, a link, a cursor, or a chart
other than the one acted on moving, or unlinking one changing what it shows. -/
def violation {n : Nat} (c : ViewConfig Float) (r r' : Linked Float n) (a : Action n) : Option String :=
  let views := List.finRange n
  let limits := views.any fun j => !(within c.x (r'.view j).x && within c.y (r'.view j).y)
  let linkedX := views.filter r'.isLinked |>.map fun j => (r'.view j).x
  let desynced := linkedX.any fun x => x != r'.x.scale
  let moved := match a with
    | .input i _ => views.any fun j => j != i && (r'.view j).y != (r.view j).y
    | .toggle i => views.any fun j => (r'.view j).y != (r.view j).y ||
        (j != i && (r'.view j).x != (r.view j).x) || (!r'.isLinked i && r'.view i != r.view i)
  let drift := match a with
    | .input i (.wheel px py _) | .input i (.pinch px py _ _) =>
      let before := View.cursor c (r.view i) px py
      let after := View.cursor c (r'.view i) px py
      !(near before.1 after.1 && near before.2 after.2)
    | _ => false
  if limits then some "zoom limit violated"
  else if desynced then some "linked charts disagree on x"
  else if drift then some "cursor moved under a zoom"
  else if moved then some "an action moved a chart it did not address"
  else none

/-- Run `steps` random actions on `n` charts from `seed`; the first violation, with its step. A rig
with no charts is reported, since it would check nothing. -/
def run (c : ViewConfig Float) (n : Nat) (seed steps : Nat) : Option String :=
  if hn : 0 < n then
    let rec go : Nat → Nat → Linked Float n → Option String
      | 0, _, _ => none
      | k + 1, s, r =>
        let (a, s) := action n hn s
        let r' := match a with
          | .input i inp => r.step c i inp
          | .toggle i => if r.isLinked i then r.unlink i else r.relink i
        match violation c r r' a with
        | some e => some s!"step {steps - k}: {e}"
        | none => go k s r'
    go steps seed (home c n)
  else some "no charts to check"

end Inkproof.Demo.Robot
