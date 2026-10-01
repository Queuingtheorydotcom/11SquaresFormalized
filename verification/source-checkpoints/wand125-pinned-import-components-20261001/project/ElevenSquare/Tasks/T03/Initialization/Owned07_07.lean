import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned07_07Part000
import ElevenSquare.Tasks.T03.Initialization.Owned07_07Part001
import ElevenSquare.Tasks.T03.Initialization.Owned07_07Part002
import ElevenSquare.Tasks.T03.Initialization.Owned07_07Part003

namespace ElevenSquare.Pending.T03.Initialization.Owned07_07
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 7 point 0 (1/16) = true :=
  OwnershipTree.leaf_checked leaf000 7 point 0 (1/16) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 7 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf001 7 point (1/16) (3/32) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 7 point (3/32) (7/64) = true :=
  OwnershipTree.leaf_checked leaf002 7 point (3/32) (7/64) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (3/32) node001 node002

theorem node003_checked : node003.check 7 point (1/16) (7/64) = true :=
  OwnershipTree.split_checked node001 node002 7 point (1/16) (3/32) (7/64) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/16) node000 node003

theorem node004_checked : node004.check 7 point 0 (7/64) = true :=
  OwnershipTree.split_checked node000 node003 7 point 0 (1/16) (7/64) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 7 point (7/64) (15/128) = true :=
  OwnershipTree.leaf_checked leaf003 7 point (7/64) (15/128) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 7 point (15/128) (1/8) = true :=
  OwnershipTree.leaf_checked leaf004 7 point (15/128) (1/8) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 7 point (1/8) (33/256) = true :=
  OwnershipTree.leaf_checked leaf005 7 point (1/8) (33/256) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (1/8) node006 node007

theorem node008_checked : node008.check 7 point (15/128) (33/256) = true :=
  OwnershipTree.split_checked node006 node007 7 point (15/128) (1/8) (33/256) node006_checked node007_checked

def node009 : OwnershipTree := .split (15/128) node005 node008

theorem node009_checked : node009.check 7 point (7/64) (33/256) = true :=
  OwnershipTree.split_checked node005 node008 7 point (7/64) (15/128) (33/256) node005_checked node008_checked

def node010 : OwnershipTree := .split (7/64) node004 node009

theorem node010_checked : node010.check 7 point 0 (33/256) = true :=
  OwnershipTree.split_checked node004 node009 7 point 0 (7/64) (33/256) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 7 point (33/256) (17/128) = true :=
  OwnershipTree.leaf_checked leaf006 7 point (33/256) (17/128) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 7 point (17/128) (35/256) = true :=
  OwnershipTree.leaf_checked leaf007 7 point (17/128) (35/256) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 7 point (35/256) (9/64) = true :=
  OwnershipTree.leaf_checked leaf008 7 point (35/256) (9/64) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (35/256) node012 node013

theorem node014_checked : node014.check 7 point (17/128) (9/64) = true :=
  OwnershipTree.split_checked node012 node013 7 point (17/128) (35/256) (9/64) node012_checked node013_checked

def node015 : OwnershipTree := .split (17/128) node011 node014

theorem node015_checked : node015.check 7 point (33/256) (9/64) = true :=
  OwnershipTree.split_checked node011 node014 7 point (33/256) (17/128) (9/64) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 7 point (9/64) (37/256) = true :=
  OwnershipTree.leaf_checked leaf009 7 point (9/64) (37/256) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 7 point (37/256) (19/128) = true :=
  OwnershipTree.leaf_checked leaf010 7 point (37/256) (19/128) rfl rfl leaf010_checked

def node018 : OwnershipTree := .split (37/256) node016 node017

theorem node018_checked : node018.check 7 point (9/64) (19/128) = true :=
  OwnershipTree.split_checked node016 node017 7 point (9/64) (37/256) (19/128) node016_checked node017_checked

def node019 : OwnershipTree := .leaf leaf011

theorem node019_checked : node019.check 7 point (19/128) (39/256) = true :=
  OwnershipTree.leaf_checked leaf011 7 point (19/128) (39/256) rfl rfl leaf011_checked

def node020 : OwnershipTree := .leaf leaf012

theorem node020_checked : node020.check 7 point (39/256) (5/32) = true :=
  OwnershipTree.leaf_checked leaf012 7 point (39/256) (5/32) rfl rfl leaf012_checked

def node021 : OwnershipTree := .split (39/256) node019 node020

theorem node021_checked : node021.check 7 point (19/128) (5/32) = true :=
  OwnershipTree.split_checked node019 node020 7 point (19/128) (39/256) (5/32) node019_checked node020_checked

def node022 : OwnershipTree := .split (19/128) node018 node021

theorem node022_checked : node022.check 7 point (9/64) (5/32) = true :=
  OwnershipTree.split_checked node018 node021 7 point (9/64) (19/128) (5/32) node018_checked node021_checked

def node023 : OwnershipTree := .split (9/64) node015 node022

theorem node023_checked : node023.check 7 point (33/256) (5/32) = true :=
  OwnershipTree.split_checked node015 node022 7 point (33/256) (9/64) (5/32) node015_checked node022_checked

def node024 : OwnershipTree := .split (33/256) node010 node023

theorem node024_checked : node024.check 7 point 0 (5/32) = true :=
  OwnershipTree.split_checked node010 node023 7 point 0 (33/256) (5/32) node010_checked node023_checked

def node025 : OwnershipTree := .leaf leaf013

theorem node025_checked : node025.check 7 point (5/32) (41/256) = true :=
  OwnershipTree.leaf_checked leaf013 7 point (5/32) (41/256) rfl rfl leaf013_checked

def node026 : OwnershipTree := .leaf leaf014

theorem node026_checked : node026.check 7 point (41/256) (21/128) = true :=
  OwnershipTree.leaf_checked leaf014 7 point (41/256) (21/128) rfl rfl leaf014_checked

def node027 : OwnershipTree := .leaf leaf015

theorem node027_checked : node027.check 7 point (21/128) (43/256) = true :=
  OwnershipTree.leaf_checked leaf015 7 point (21/128) (43/256) rfl rfl leaf015_checked

def node028 : OwnershipTree := .split (21/128) node026 node027

theorem node028_checked : node028.check 7 point (41/256) (43/256) = true :=
  OwnershipTree.split_checked node026 node027 7 point (41/256) (21/128) (43/256) node026_checked node027_checked

def node029 : OwnershipTree := .split (41/256) node025 node028

theorem node029_checked : node029.check 7 point (5/32) (43/256) = true :=
  OwnershipTree.split_checked node025 node028 7 point (5/32) (41/256) (43/256) node025_checked node028_checked

def node030 : OwnershipTree := .leaf leaf016

theorem node030_checked : node030.check 7 point (43/256) (11/64) = true :=
  OwnershipTree.leaf_checked leaf016 7 point (43/256) (11/64) rfl rfl leaf016_checked

def node031 : OwnershipTree := .leaf leaf017

theorem node031_checked : node031.check 7 point (11/64) (23/128) = true :=
  OwnershipTree.leaf_checked leaf017 7 point (11/64) (23/128) rfl rfl leaf017_checked

def node032 : OwnershipTree := .leaf leaf018

theorem node032_checked : node032.check 7 point (23/128) (3/16) = true :=
  OwnershipTree.leaf_checked leaf018 7 point (23/128) (3/16) rfl rfl leaf018_checked

def node033 : OwnershipTree := .split (23/128) node031 node032

theorem node033_checked : node033.check 7 point (11/64) (3/16) = true :=
  OwnershipTree.split_checked node031 node032 7 point (11/64) (23/128) (3/16) node031_checked node032_checked

def node034 : OwnershipTree := .split (11/64) node030 node033

theorem node034_checked : node034.check 7 point (43/256) (3/16) = true :=
  OwnershipTree.split_checked node030 node033 7 point (43/256) (11/64) (3/16) node030_checked node033_checked

def node035 : OwnershipTree := .split (43/256) node029 node034

theorem node035_checked : node035.check 7 point (5/32) (3/16) = true :=
  OwnershipTree.split_checked node029 node034 7 point (5/32) (43/256) (3/16) node029_checked node034_checked

def node036 : OwnershipTree := .leaf leaf019

theorem node036_checked : node036.check 7 point (3/16) (13/64) = true :=
  OwnershipTree.leaf_checked leaf019 7 point (3/16) (13/64) rfl rfl leaf019_checked

def node037 : OwnershipTree := .leaf leaf020

theorem node037_checked : node037.check 7 point (13/64) (7/32) = true :=
  OwnershipTree.leaf_checked leaf020 7 point (13/64) (7/32) rfl rfl leaf020_checked

def node038 : OwnershipTree := .leaf leaf021

theorem node038_checked : node038.check 7 point (7/32) (1/4) = true :=
  OwnershipTree.leaf_checked leaf021 7 point (7/32) (1/4) rfl rfl leaf021_checked

def node039 : OwnershipTree := .split (7/32) node037 node038

theorem node039_checked : node039.check 7 point (13/64) (1/4) = true :=
  OwnershipTree.split_checked node037 node038 7 point (13/64) (7/32) (1/4) node037_checked node038_checked

def node040 : OwnershipTree := .split (13/64) node036 node039

theorem node040_checked : node040.check 7 point (3/16) (1/4) = true :=
  OwnershipTree.split_checked node036 node039 7 point (3/16) (13/64) (1/4) node036_checked node039_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 7 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf022 7 point (1/4) (1/2) rfl rfl leaf022_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 7 point (1/2) (3/4) = true :=
  OwnershipTree.leaf_checked leaf023 7 point (1/2) (3/4) rfl rfl leaf023_checked

def node043 : OwnershipTree := .split (1/2) node041 node042

theorem node043_checked : node043.check 7 point (1/4) (3/4) = true :=
  OwnershipTree.split_checked node041 node042 7 point (1/4) (1/2) (3/4) node041_checked node042_checked

def node044 : OwnershipTree := .leaf leaf024

theorem node044_checked : node044.check 7 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf024 7 point (3/4) (7/8) rfl rfl leaf024_checked

def node045 : OwnershipTree := .leaf leaf025

theorem node045_checked : node045.check 7 point (7/8) 1 = true :=
  OwnershipTree.leaf_checked leaf025 7 point (7/8) 1 rfl rfl leaf025_checked

def node046 : OwnershipTree := .split (7/8) node044 node045

theorem node046_checked : node046.check 7 point (3/4) 1 = true :=
  OwnershipTree.split_checked node044 node045 7 point (3/4) (7/8) 1 node044_checked node045_checked

def node047 : OwnershipTree := .split (3/4) node043 node046

theorem node047_checked : node047.check 7 point (1/4) 1 = true :=
  OwnershipTree.split_checked node043 node046 7 point (1/4) (3/4) 1 node043_checked node046_checked

def node048 : OwnershipTree := .split (1/4) node040 node047

theorem node048_checked : node048.check 7 point (3/16) 1 = true :=
  OwnershipTree.split_checked node040 node047 7 point (3/16) (1/4) 1 node040_checked node047_checked

def node049 : OwnershipTree := .split (3/16) node035 node048

theorem node049_checked : node049.check 7 point (5/32) 1 = true :=
  OwnershipTree.split_checked node035 node048 7 point (5/32) (3/16) 1 node035_checked node048_checked

def node050 : OwnershipTree := .split (5/32) node024 node049

theorem node050_checked : node050.check 7 point 0 1 = true :=
  OwnershipTree.split_checked node024 node049 7 point 0 (5/32) 1 node024_checked node049_checked

def certificate : OwnershipTree := node050

theorem checked : certificate.check 7 point 0 1 = true := node050_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 7 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned07_07
