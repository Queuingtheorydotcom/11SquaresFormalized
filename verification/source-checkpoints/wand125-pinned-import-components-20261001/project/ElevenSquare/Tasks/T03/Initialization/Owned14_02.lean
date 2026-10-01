import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned14_02Part000
import ElevenSquare.Tasks.T03.Initialization.Owned14_02Part001
import ElevenSquare.Tasks.T03.Initialization.Owned14_02Part002

namespace ElevenSquare.Pending.T03.Initialization.Owned14_02
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 14 point 0 (1/4) = true :=
  OwnershipTree.leaf_checked leaf000 14 point 0 (1/4) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 14 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf001 14 point (1/4) (1/2) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/4) node000 node001

theorem node002_checked : node002.check 14 point 0 (1/2) = true :=
  OwnershipTree.split_checked node000 node001 14 point 0 (1/4) (1/2) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 14 point (1/2) (3/4) = true :=
  OwnershipTree.leaf_checked leaf002 14 point (1/2) (3/4) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 14 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf003 14 point (3/4) (7/8) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 14 point (7/8) (29/32) = true :=
  OwnershipTree.leaf_checked leaf004 14 point (7/8) (29/32) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (7/8) node004 node005

theorem node006_checked : node006.check 14 point (3/4) (29/32) = true :=
  OwnershipTree.split_checked node004 node005 14 point (3/4) (7/8) (29/32) node004_checked node005_checked

def node007 : OwnershipTree := .split (3/4) node003 node006

theorem node007_checked : node007.check 14 point (1/2) (29/32) = true :=
  OwnershipTree.split_checked node003 node006 14 point (1/2) (3/4) (29/32) node003_checked node006_checked

def node008 : OwnershipTree := .split (1/2) node002 node007

theorem node008_checked : node008.check 14 point 0 (29/32) = true :=
  OwnershipTree.split_checked node002 node007 14 point 0 (1/2) (29/32) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 14 point (29/32) (59/64) = true :=
  OwnershipTree.leaf_checked leaf005 14 point (29/32) (59/64) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 14 point (59/64) (15/16) = true :=
  OwnershipTree.leaf_checked leaf006 14 point (59/64) (15/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .split (59/64) node009 node010

theorem node011_checked : node011.check 14 point (29/32) (15/16) = true :=
  OwnershipTree.split_checked node009 node010 14 point (29/32) (59/64) (15/16) node009_checked node010_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 14 point (15/16) (61/64) = true :=
  OwnershipTree.leaf_checked leaf007 14 point (15/16) (61/64) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 14 point (61/64) (123/128) = true :=
  OwnershipTree.leaf_checked leaf008 14 point (61/64) (123/128) rfl rfl leaf008_checked

def node014 : OwnershipTree := .leaf leaf009

theorem node014_checked : node014.check 14 point (123/128) (31/32) = true :=
  OwnershipTree.leaf_checked leaf009 14 point (123/128) (31/32) rfl rfl leaf009_checked

def node015 : OwnershipTree := .split (123/128) node013 node014

theorem node015_checked : node015.check 14 point (61/64) (31/32) = true :=
  OwnershipTree.split_checked node013 node014 14 point (61/64) (123/128) (31/32) node013_checked node014_checked

def node016 : OwnershipTree := .split (61/64) node012 node015

theorem node016_checked : node016.check 14 point (15/16) (31/32) = true :=
  OwnershipTree.split_checked node012 node015 14 point (15/16) (61/64) (31/32) node012_checked node015_checked

def node017 : OwnershipTree := .split (15/16) node011 node016

theorem node017_checked : node017.check 14 point (29/32) (31/32) = true :=
  OwnershipTree.split_checked node011 node016 14 point (29/32) (15/16) (31/32) node011_checked node016_checked

def node018 : OwnershipTree := .split (29/32) node008 node017

theorem node018_checked : node018.check 14 point 0 (31/32) = true :=
  OwnershipTree.split_checked node008 node017 14 point 0 (29/32) (31/32) node008_checked node017_checked

def node019 : OwnershipTree := .leaf leaf010

theorem node019_checked : node019.check 14 point (31/32) (249/256) = true :=
  OwnershipTree.leaf_checked leaf010 14 point (31/32) (249/256) rfl rfl leaf010_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 14 point (249/256) (125/128) = true :=
  OwnershipTree.leaf_checked leaf011 14 point (249/256) (125/128) rfl rfl leaf011_checked

def node021 : OwnershipTree := .split (249/256) node019 node020

theorem node021_checked : node021.check 14 point (31/32) (125/128) = true :=
  OwnershipTree.split_checked node019 node020 14 point (31/32) (249/256) (125/128) node019_checked node020_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 14 point (125/128) (251/256) = true :=
  OwnershipTree.leaf_checked leaf012 14 point (125/128) (251/256) rfl rfl leaf012_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 14 point (251/256) (63/64) = true :=
  OwnershipTree.leaf_checked leaf013 14 point (251/256) (63/64) rfl rfl leaf013_checked

def node024 : OwnershipTree := .leaf leaf014

theorem node024_checked : node024.check 14 point (63/64) (253/256) = true :=
  OwnershipTree.leaf_checked leaf014 14 point (63/64) (253/256) rfl rfl leaf014_checked

def node025 : OwnershipTree := .split (63/64) node023 node024

theorem node025_checked : node025.check 14 point (251/256) (253/256) = true :=
  OwnershipTree.split_checked node023 node024 14 point (251/256) (63/64) (253/256) node023_checked node024_checked

def node026 : OwnershipTree := .split (251/256) node022 node025

theorem node026_checked : node026.check 14 point (125/128) (253/256) = true :=
  OwnershipTree.split_checked node022 node025 14 point (125/128) (251/256) (253/256) node022_checked node025_checked

def node027 : OwnershipTree := .split (125/128) node021 node026

theorem node027_checked : node027.check 14 point (31/32) (253/256) = true :=
  OwnershipTree.split_checked node021 node026 14 point (31/32) (125/128) (253/256) node021_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 14 point (253/256) (507/512) = true :=
  OwnershipTree.leaf_checked leaf015 14 point (253/256) (507/512) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 14 point (507/512) (127/128) = true :=
  OwnershipTree.leaf_checked leaf016 14 point (507/512) (127/128) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 14 point (127/128) (509/512) = true :=
  OwnershipTree.leaf_checked leaf017 14 point (127/128) (509/512) rfl rfl leaf017_checked

def node031 : OwnershipTree := .split (127/128) node029 node030

theorem node031_checked : node031.check 14 point (507/512) (509/512) = true :=
  OwnershipTree.split_checked node029 node030 14 point (507/512) (127/128) (509/512) node029_checked node030_checked

def node032 : OwnershipTree := .split (507/512) node028 node031

theorem node032_checked : node032.check 14 point (253/256) (509/512) = true :=
  OwnershipTree.split_checked node028 node031 14 point (253/256) (507/512) (509/512) node028_checked node031_checked

def node033 : OwnershipTree := .leaf leaf018

theorem node033_checked : node033.check 14 point (509/512) (255/256) = true :=
  OwnershipTree.leaf_checked leaf018 14 point (509/512) (255/256) rfl rfl leaf018_checked

def node034 : OwnershipTree := .leaf leaf019

theorem node034_checked : node034.check 14 point (255/256) (511/512) = true :=
  OwnershipTree.leaf_checked leaf019 14 point (255/256) (511/512) rfl rfl leaf019_checked

def node035 : OwnershipTree := .leaf leaf020

theorem node035_checked : node035.check 14 point (511/512) 1 = true :=
  OwnershipTree.leaf_checked leaf020 14 point (511/512) 1 rfl rfl leaf020_checked

def node036 : OwnershipTree := .split (511/512) node034 node035

theorem node036_checked : node036.check 14 point (255/256) 1 = true :=
  OwnershipTree.split_checked node034 node035 14 point (255/256) (511/512) 1 node034_checked node035_checked

def node037 : OwnershipTree := .split (255/256) node033 node036

theorem node037_checked : node037.check 14 point (509/512) 1 = true :=
  OwnershipTree.split_checked node033 node036 14 point (509/512) (255/256) 1 node033_checked node036_checked

def node038 : OwnershipTree := .split (509/512) node032 node037

theorem node038_checked : node038.check 14 point (253/256) 1 = true :=
  OwnershipTree.split_checked node032 node037 14 point (253/256) (509/512) 1 node032_checked node037_checked

def node039 : OwnershipTree := .split (253/256) node027 node038

theorem node039_checked : node039.check 14 point (31/32) 1 = true :=
  OwnershipTree.split_checked node027 node038 14 point (31/32) (253/256) 1 node027_checked node038_checked

def node040 : OwnershipTree := .split (31/32) node018 node039

theorem node040_checked : node040.check 14 point 0 1 = true :=
  OwnershipTree.split_checked node018 node039 14 point 0 (31/32) 1 node018_checked node039_checked

def certificate : OwnershipTree := node040

theorem checked : certificate.check 14 point 0 1 = true := node040_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 14 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 14 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned14_02
