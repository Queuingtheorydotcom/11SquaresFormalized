import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned06_01Part000
import ElevenSquare.Tasks.T03.Initialization.Owned06_01Part001

namespace ElevenSquare.Pending.T03.Initialization.Owned06_01
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 6 point 0 (1/4) = true :=
  OwnershipTree.leaf_checked leaf000 6 point 0 (1/4) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 6 point (1/4) (5/16) = true :=
  OwnershipTree.leaf_checked leaf001 6 point (1/4) (5/16) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/4) node000 node001

theorem node002_checked : node002.check 6 point 0 (5/16) = true :=
  OwnershipTree.split_checked node000 node001 6 point 0 (1/4) (5/16) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 6 point (5/16) (11/32) = true :=
  OwnershipTree.leaf_checked leaf002 6 point (5/16) (11/32) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 6 point (11/32) (3/8) = true :=
  OwnershipTree.leaf_checked leaf003 6 point (11/32) (3/8) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 6 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf004 6 point (3/8) (1/2) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (3/8) node004 node005

theorem node006_checked : node006.check 6 point (11/32) (1/2) = true :=
  OwnershipTree.split_checked node004 node005 6 point (11/32) (3/8) (1/2) node004_checked node005_checked

def node007 : OwnershipTree := .split (11/32) node003 node006

theorem node007_checked : node007.check 6 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node003 node006 6 point (5/16) (11/32) (1/2) node003_checked node006_checked

def node008 : OwnershipTree := .split (5/16) node002 node007

theorem node008_checked : node008.check 6 point 0 (1/2) = true :=
  OwnershipTree.split_checked node002 node007 6 point 0 (5/16) (1/2) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 6 point (1/2) (17/32) = true :=
  OwnershipTree.leaf_checked leaf005 6 point (1/2) (17/32) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 6 point (17/32) (9/16) = true :=
  OwnershipTree.leaf_checked leaf006 6 point (17/32) (9/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .split (17/32) node009 node010

theorem node011_checked : node011.check 6 point (1/2) (9/16) = true :=
  OwnershipTree.split_checked node009 node010 6 point (1/2) (17/32) (9/16) node009_checked node010_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 6 point (9/16) (5/8) = true :=
  OwnershipTree.leaf_checked leaf007 6 point (9/16) (5/8) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 6 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf008 6 point (5/8) (3/4) rfl rfl leaf008_checked

def node014 : OwnershipTree := .leaf leaf009

theorem node014_checked : node014.check 6 point (3/4) 1 = true :=
  OwnershipTree.leaf_checked leaf009 6 point (3/4) 1 rfl rfl leaf009_checked

def node015 : OwnershipTree := .split (3/4) node013 node014

theorem node015_checked : node015.check 6 point (5/8) 1 = true :=
  OwnershipTree.split_checked node013 node014 6 point (5/8) (3/4) 1 node013_checked node014_checked

def node016 : OwnershipTree := .split (5/8) node012 node015

theorem node016_checked : node016.check 6 point (9/16) 1 = true :=
  OwnershipTree.split_checked node012 node015 6 point (9/16) (5/8) 1 node012_checked node015_checked

def node017 : OwnershipTree := .split (9/16) node011 node016

theorem node017_checked : node017.check 6 point (1/2) 1 = true :=
  OwnershipTree.split_checked node011 node016 6 point (1/2) (9/16) 1 node011_checked node016_checked

def node018 : OwnershipTree := .split (1/2) node008 node017

theorem node018_checked : node018.check 6 point 0 1 = true :=
  OwnershipTree.split_checked node008 node017 6 point 0 (1/2) 1 node008_checked node017_checked

def certificate : OwnershipTree := node018

theorem checked : certificate.check 6 point 0 1 = true := node018_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 6 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 6 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned06_01
