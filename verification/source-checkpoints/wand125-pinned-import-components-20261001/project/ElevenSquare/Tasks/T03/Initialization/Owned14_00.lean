import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned14_00Part000
import ElevenSquare.Tasks.T03.Initialization.Owned14_00Part001

namespace ElevenSquare.Pending.T03.Initialization.Owned14_00
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 14 point 0 (1/512) = true :=
  OwnershipTree.leaf_checked leaf000 14 point 0 (1/512) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 14 point (1/512) (1/256) = true :=
  OwnershipTree.leaf_checked leaf001 14 point (1/512) (1/256) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 14 point (1/256) (3/512) = true :=
  OwnershipTree.leaf_checked leaf002 14 point (1/256) (3/512) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (1/256) node001 node002

theorem node003_checked : node003.check 14 point (1/512) (3/512) = true :=
  OwnershipTree.split_checked node001 node002 14 point (1/512) (1/256) (3/512) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/512) node000 node003

theorem node004_checked : node004.check 14 point 0 (3/512) = true :=
  OwnershipTree.split_checked node000 node003 14 point 0 (1/512) (3/512) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 14 point (3/512) (1/128) = true :=
  OwnershipTree.leaf_checked leaf003 14 point (3/512) (1/128) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 14 point (1/128) (3/256) = true :=
  OwnershipTree.leaf_checked leaf004 14 point (1/128) (3/256) rfl rfl leaf004_checked

def node007 : OwnershipTree := .split (1/128) node005 node006

theorem node007_checked : node007.check 14 point (3/512) (3/256) = true :=
  OwnershipTree.split_checked node005 node006 14 point (3/512) (1/128) (3/256) node005_checked node006_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 14 point (3/256) (1/64) = true :=
  OwnershipTree.leaf_checked leaf005 14 point (3/256) (1/64) rfl rfl leaf005_checked

def node009 : OwnershipTree := .leaf leaf006

theorem node009_checked : node009.check 14 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf006 14 point (1/64) (3/128) rfl rfl leaf006_checked

def node010 : OwnershipTree := .split (1/64) node008 node009

theorem node010_checked : node010.check 14 point (3/256) (3/128) = true :=
  OwnershipTree.split_checked node008 node009 14 point (3/256) (1/64) (3/128) node008_checked node009_checked

def node011 : OwnershipTree := .split (3/256) node007 node010

theorem node011_checked : node011.check 14 point (3/512) (3/128) = true :=
  OwnershipTree.split_checked node007 node010 14 point (3/512) (3/256) (3/128) node007_checked node010_checked

def node012 : OwnershipTree := .split (3/512) node004 node011

theorem node012_checked : node012.check 14 point 0 (3/128) = true :=
  OwnershipTree.split_checked node004 node011 14 point 0 (3/512) (3/128) node004_checked node011_checked

def node013 : OwnershipTree := .leaf leaf007

theorem node013_checked : node013.check 14 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf007 14 point (3/128) (1/32) rfl rfl leaf007_checked

def node014 : OwnershipTree := .leaf leaf008

theorem node014_checked : node014.check 14 point (1/32) (1/16) = true :=
  OwnershipTree.leaf_checked leaf008 14 point (1/32) (1/16) rfl rfl leaf008_checked

def node015 : OwnershipTree := .split (1/32) node013 node014

theorem node015_checked : node015.check 14 point (3/128) (1/16) = true :=
  OwnershipTree.split_checked node013 node014 14 point (3/128) (1/32) (1/16) node013_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 14 point (1/16) (1/8) = true :=
  OwnershipTree.leaf_checked leaf009 14 point (1/16) (1/8) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 14 point (1/8) (1/4) = true :=
  OwnershipTree.leaf_checked leaf010 14 point (1/8) (1/4) rfl rfl leaf010_checked

def node018 : OwnershipTree := .split (1/8) node016 node017

theorem node018_checked : node018.check 14 point (1/16) (1/4) = true :=
  OwnershipTree.split_checked node016 node017 14 point (1/16) (1/8) (1/4) node016_checked node017_checked

def node019 : OwnershipTree := .split (1/16) node015 node018

theorem node019_checked : node019.check 14 point (3/128) (1/4) = true :=
  OwnershipTree.split_checked node015 node018 14 point (3/128) (1/16) (1/4) node015_checked node018_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 14 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf011 14 point (1/4) (3/8) rfl rfl leaf011_checked

def node021 : OwnershipTree := .leaf leaf012

theorem node021_checked : node021.check 14 point (3/8) (7/16) = true :=
  OwnershipTree.leaf_checked leaf012 14 point (3/8) (7/16) rfl rfl leaf012_checked

def node022 : OwnershipTree := .split (3/8) node020 node021

theorem node022_checked : node022.check 14 point (1/4) (7/16) = true :=
  OwnershipTree.split_checked node020 node021 14 point (1/4) (3/8) (7/16) node020_checked node021_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 14 point (7/16) (1/2) = true :=
  OwnershipTree.leaf_checked leaf013 14 point (7/16) (1/2) rfl rfl leaf013_checked

def node024 : OwnershipTree := .leaf leaf014

theorem node024_checked : node024.check 14 point (1/2) 1 = true :=
  OwnershipTree.leaf_checked leaf014 14 point (1/2) 1 rfl rfl leaf014_checked

def node025 : OwnershipTree := .split (1/2) node023 node024

theorem node025_checked : node025.check 14 point (7/16) 1 = true :=
  OwnershipTree.split_checked node023 node024 14 point (7/16) (1/2) 1 node023_checked node024_checked

def node026 : OwnershipTree := .split (7/16) node022 node025

theorem node026_checked : node026.check 14 point (1/4) 1 = true :=
  OwnershipTree.split_checked node022 node025 14 point (1/4) (7/16) 1 node022_checked node025_checked

def node027 : OwnershipTree := .split (1/4) node019 node026

theorem node027_checked : node027.check 14 point (3/128) 1 = true :=
  OwnershipTree.split_checked node019 node026 14 point (3/128) (1/4) 1 node019_checked node026_checked

def node028 : OwnershipTree := .split (3/128) node012 node027

theorem node028_checked : node028.check 14 point 0 1 = true :=
  OwnershipTree.split_checked node012 node027 14 point 0 (3/128) 1 node012_checked node027_checked

def certificate : OwnershipTree := node028

theorem checked : certificate.check 14 point 0 1 = true := node028_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 14 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 14 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned14_00
