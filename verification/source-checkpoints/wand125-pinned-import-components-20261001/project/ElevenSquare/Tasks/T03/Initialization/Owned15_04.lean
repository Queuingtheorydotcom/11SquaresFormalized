import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned15_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned15_04Part001
import ElevenSquare.Tasks.T03.Initialization.Owned15_04Part002

namespace ElevenSquare.Pending.T03.Initialization.Owned15_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 15 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 15 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 15 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf001 15 point (1/16) (3/32) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/16) node000 node001

theorem node002_checked : node002.check 15 point 0 (3/32) = true :=
  OwnershipTree.split_checked node000 node001 15 point 0 (1/16) (3/32) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 15 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf002 15 point (3/32) (1/8) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 15 point (1/8) (9/64) = true :=
  OwnershipTree.leaf_checked leaf003 15 point (1/8) (9/64) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 15 point (9/64) (5/32) = true :=
  OwnershipTree.leaf_checked leaf004 15 point (9/64) (5/32) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (9/64) node004 node005

theorem node006_checked : node006.check 15 point (1/8) (5/32) = true :=
  OwnershipTree.split_checked node004 node005 15 point (1/8) (9/64) (5/32) node004_checked node005_checked

def node007 : OwnershipTree := .split (1/8) node003 node006

theorem node007_checked : node007.check 15 point (3/32) (5/32) = true :=
  OwnershipTree.split_checked node003 node006 15 point (3/32) (1/8) (5/32) node003_checked node006_checked

def node008 : OwnershipTree := .split (3/32) node002 node007

theorem node008_checked : node008.check 15 point 0 (5/32) = true :=
  OwnershipTree.split_checked node002 node007 15 point 0 (3/32) (5/32) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 15 point (5/32) (21/128) = true :=
  OwnershipTree.leaf_checked leaf005 15 point (5/32) (21/128) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 15 point (21/128) (11/64) = true :=
  OwnershipTree.leaf_checked leaf006 15 point (21/128) (11/64) rfl rfl leaf006_checked

def node011 : OwnershipTree := .split (21/128) node009 node010

theorem node011_checked : node011.check 15 point (5/32) (11/64) = true :=
  OwnershipTree.split_checked node009 node010 15 point (5/32) (21/128) (11/64) node009_checked node010_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 15 point (11/64) (23/128) = true :=
  OwnershipTree.leaf_checked leaf007 15 point (11/64) (23/128) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 15 point (23/128) (3/16) = true :=
  OwnershipTree.leaf_checked leaf008 15 point (23/128) (3/16) rfl rfl leaf008_checked

def node014 : OwnershipTree := .leaf leaf009

theorem node014_checked : node014.check 15 point (3/16) (25/128) = true :=
  OwnershipTree.leaf_checked leaf009 15 point (3/16) (25/128) rfl rfl leaf009_checked

def node015 : OwnershipTree := .split (3/16) node013 node014

theorem node015_checked : node015.check 15 point (23/128) (25/128) = true :=
  OwnershipTree.split_checked node013 node014 15 point (23/128) (3/16) (25/128) node013_checked node014_checked

def node016 : OwnershipTree := .split (23/128) node012 node015

theorem node016_checked : node016.check 15 point (11/64) (25/128) = true :=
  OwnershipTree.split_checked node012 node015 15 point (11/64) (23/128) (25/128) node012_checked node015_checked

def node017 : OwnershipTree := .split (11/64) node011 node016

theorem node017_checked : node017.check 15 point (5/32) (25/128) = true :=
  OwnershipTree.split_checked node011 node016 15 point (5/32) (11/64) (25/128) node011_checked node016_checked

def node018 : OwnershipTree := .split (5/32) node008 node017

theorem node018_checked : node018.check 15 point 0 (25/128) = true :=
  OwnershipTree.split_checked node008 node017 15 point 0 (5/32) (25/128) node008_checked node017_checked

def node019 : OwnershipTree := .leaf leaf010

theorem node019_checked : node019.check 15 point (25/128) (13/64) = true :=
  OwnershipTree.leaf_checked leaf010 15 point (25/128) (13/64) rfl rfl leaf010_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 15 point (13/64) (27/128) = true :=
  OwnershipTree.leaf_checked leaf011 15 point (13/64) (27/128) rfl rfl leaf011_checked

def node021 : OwnershipTree := .split (13/64) node019 node020

theorem node021_checked : node021.check 15 point (25/128) (27/128) = true :=
  OwnershipTree.split_checked node019 node020 15 point (25/128) (13/64) (27/128) node019_checked node020_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 15 point (27/128) (7/32) = true :=
  OwnershipTree.leaf_checked leaf012 15 point (27/128) (7/32) rfl rfl leaf012_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 15 point (7/32) (15/64) = true :=
  OwnershipTree.leaf_checked leaf013 15 point (7/32) (15/64) rfl rfl leaf013_checked

def node024 : OwnershipTree := .leaf leaf014

theorem node024_checked : node024.check 15 point (15/64) (1/4) = true :=
  OwnershipTree.leaf_checked leaf014 15 point (15/64) (1/4) rfl rfl leaf014_checked

def node025 : OwnershipTree := .split (15/64) node023 node024

theorem node025_checked : node025.check 15 point (7/32) (1/4) = true :=
  OwnershipTree.split_checked node023 node024 15 point (7/32) (15/64) (1/4) node023_checked node024_checked

def node026 : OwnershipTree := .split (7/32) node022 node025

theorem node026_checked : node026.check 15 point (27/128) (1/4) = true :=
  OwnershipTree.split_checked node022 node025 15 point (27/128) (7/32) (1/4) node022_checked node025_checked

def node027 : OwnershipTree := .split (27/128) node021 node026

theorem node027_checked : node027.check 15 point (25/128) (1/4) = true :=
  OwnershipTree.split_checked node021 node026 15 point (25/128) (27/128) (1/4) node021_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 15 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf015 15 point (1/4) (3/8) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 15 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf016 15 point (3/8) (1/2) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 15 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf017 15 point (1/2) (5/8) rfl rfl leaf017_checked

def node031 : OwnershipTree := .split (1/2) node029 node030

theorem node031_checked : node031.check 15 point (3/8) (5/8) = true :=
  OwnershipTree.split_checked node029 node030 15 point (3/8) (1/2) (5/8) node029_checked node030_checked

def node032 : OwnershipTree := .split (3/8) node028 node031

theorem node032_checked : node032.check 15 point (1/4) (5/8) = true :=
  OwnershipTree.split_checked node028 node031 15 point (1/4) (3/8) (5/8) node028_checked node031_checked

def node033 : OwnershipTree := .leaf leaf018

theorem node033_checked : node033.check 15 point (5/8) (3/4) = true :=
  OwnershipTree.leaf_checked leaf018 15 point (5/8) (3/4) rfl rfl leaf018_checked

def node034 : OwnershipTree := .leaf leaf019

theorem node034_checked : node034.check 15 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf019 15 point (3/4) (7/8) rfl rfl leaf019_checked

def node035 : OwnershipTree := .leaf leaf020

theorem node035_checked : node035.check 15 point (7/8) 1 = true :=
  OwnershipTree.leaf_checked leaf020 15 point (7/8) 1 rfl rfl leaf020_checked

def node036 : OwnershipTree := .split (7/8) node034 node035

theorem node036_checked : node036.check 15 point (3/4) 1 = true :=
  OwnershipTree.split_checked node034 node035 15 point (3/4) (7/8) 1 node034_checked node035_checked

def node037 : OwnershipTree := .split (3/4) node033 node036

theorem node037_checked : node037.check 15 point (5/8) 1 = true :=
  OwnershipTree.split_checked node033 node036 15 point (5/8) (3/4) 1 node033_checked node036_checked

def node038 : OwnershipTree := .split (5/8) node032 node037

theorem node038_checked : node038.check 15 point (1/4) 1 = true :=
  OwnershipTree.split_checked node032 node037 15 point (1/4) (5/8) 1 node032_checked node037_checked

def node039 : OwnershipTree := .split (1/4) node027 node038

theorem node039_checked : node039.check 15 point (25/128) 1 = true :=
  OwnershipTree.split_checked node027 node038 15 point (25/128) (1/4) 1 node027_checked node038_checked

def node040 : OwnershipTree := .split (25/128) node018 node039

theorem node040_checked : node040.check 15 point 0 1 = true :=
  OwnershipTree.split_checked node018 node039 15 point 0 (25/128) 1 node018_checked node039_checked

def certificate : OwnershipTree := node040

theorem checked : certificate.check 15 point 0 1 = true := node040_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 15 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 15 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned15_04
