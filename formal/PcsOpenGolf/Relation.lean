import PcsOpenGolf.Keccak

/-! # The withdrawal relation

Every app entry proves the same statement: "I know a secret whose leaf is in the tree with this
root, and this nullifier belongs to it". The public input is `root ‖ nullifier ‖ context`;
`context` stands for the transaction's signature hash and is not part of the relation, but the
verifier's transcript absorbs it first, which binds a proof to one transaction. -/

namespace PcsOpenGolf
open Keccak

/-- 32 bytes, all zero except the last, which is 1. -/
def TAG_LEAF : Bytes 32 := ofBytes 32 (List.replicate 31 0 ++ [1])

/-- 32 bytes, all zero except the last, which is 2. -/
def TAG_NULLIFIER : Bytes 32 := ofBytes 32 (List.replicate 31 0 ++ [2])

namespace PublicInput

def root (x : PublicInput) : Bytes 32 := x.extractLsb' 0 256
def nullifier (x : PublicInput) : Bytes 32 := x.extractLsb' 256 256
def context (x : PublicInput) : Bytes 32 := x.extractLsb' 512 256

end PublicInput

namespace Witness

def secret (w : Witness) : Bytes 32 := w.extractLsb' 0 256

/-- The leaf's position, a little-endian `u32`; bit `i` chooses the side at level `i`. -/
def index (w : Witness) : BitVec 32 := w.extractLsb' 256 32

def sibling (w : Witness) (i : Nat) : Bytes 32 := w.extractLsb' (288 + 256 * i) 256

end Witness

def leaf (w : Witness) : Bytes 32 := H64 w.secret TAG_LEAF

/-- Hash up the tree: at level `i`, the current node goes left when bit `i` of the index is 0. -/
def merkleRoot (w : Witness) : Bytes 32 :=
  (List.range DEPTH).foldl
    (fun node i =>
      if w.index.getLsbD i then H64 (w.sibling i) node else H64 node (w.sibling i))
    (leaf w)

/-- `R(x, w)`. -/
def Relation (x : PublicInput) (w : Witness) : Prop :=
  merkleRoot w = x.root ∧ H64 w.secret TAG_NULLIFIER = x.nullifier

instance (x : PublicInput) (w : Witness) : Decidable (Relation x w) := by
  unfold Relation; infer_instance

end PcsOpenGolf
