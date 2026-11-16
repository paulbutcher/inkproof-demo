/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Compile
import Inkproof.Gpu.Tessellate
import Inkproof.Gpu.Wire

namespace Inkproof.Demo.Draw

open Inkproof.Scene Inkproof.Gpu

/-- The tile for a chart `w` by `h` device pixels whose grid is pixels from the top left, so a point maps to clip space by `2x/w - 1` and `1 - 2y/h`. -/
def tile (w h : Nat) (list : DisplayList) : Tile where
  list := list
  slope := [(2 / Float32.ofNat w).toBits, (-2 / Float32.ofNat h).toBits]
  offset := [(-1 : Float32).toBits, (1 : Float32).toBits]
  scissor r :=
    let x0 := r.x0.floor
    let y1 := r.y1.ceil
    [x0.toInt32.toUInt32, ((h : Int) - y1).toInt32.toUInt32, (r.x1.ceil - x0).toNat.toUInt32,
      (y1 - r.y0.floor).toNat.toUInt32]

theorem tile_list (w h : Nat) (list : DisplayList) : (tile w h list).list = list := rfl

theorem tile_scissor (w h : Nat) (list : DisplayList) (r : Rect) :
    (tile w h list).scissor r =
      [r.x0.floor.toInt32.toUInt32, ((h : Int) - r.y1.ceil).toInt32.toUInt32,
        (r.x1.ceil - r.x0.floor).toNat.toUInt32, (r.y1.ceil - r.y0.floor).toNat.toUInt32] := rfl

/-- The commands that clear to `background`, build and use the renderer's program, then draw `list` from the origin. -/
def frame (background : UInt32) (w h : Nat) (list : DisplayList) : List Cmd :=
  ⟨6, [.u32 background]⟩ :: ⟨7, [.u32 0]⟩ :: ⟨3, [.u32 0]⟩ ::
    (compileCmds (tessellate ⟨0, 0⟩) {} [tile w h list]).2

/-- The wire bytes of `frame`, which is what a chart element takes as its command list. -/
def bytes (background : UInt32) (w h : Nat) (list : DisplayList) : ByteArray :=
  ByteArray.mk (encode (frame background w h list)).toArray

theorem frame_eq (background : UInt32) (w h : Nat) (list : DisplayList) :
    frame background w h list = ⟨6, [.u32 background]⟩ :: ⟨7, [.u32 0]⟩ :: ⟨3, [.u32 0]⟩ ::
      (compileCmds (tessellate ⟨0, 0⟩) {} [tile w h list]).2 := rfl

theorem bytes_data (background : UInt32) (w h : Nat) (list : DisplayList) :
    (bytes background w h list).data.toList = encode (frame background w h list) := by
  simp [bytes]

end Inkproof.Demo.Draw
