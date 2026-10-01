import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned02_00Part000
import ElevenSquare.Tasks.T03.Initialization.Owned02_00Part001
import ElevenSquare.Tasks.T03.Initialization.Owned02_00Part002
import ElevenSquare.Tasks.T03.Initialization.Owned02_00Part003

namespace ElevenSquare.Pending.T03.Initialization.Owned02_00
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 2 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 2 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 2 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 2 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 2 point (1/128) (1/64) = true :=
  OwnershipTree.leaf_checked leaf002 2 point (1/128) (1/64) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (1/128) node001 node002

theorem node003_checked : node003.check 2 point (1/256) (1/64) = true :=
  OwnershipTree.split_checked node001 node002 2 point (1/256) (1/128) (1/64) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/256) node000 node003

theorem node004_checked : node004.check 2 point 0 (1/64) = true :=
  OwnershipTree.split_checked node000 node003 2 point 0 (1/256) (1/64) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 2 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf003 2 point (1/64) (3/128) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 2 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf004 2 point (3/128) (1/32) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 2 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf005 2 point (1/32) (3/64) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (1/32) node006 node007

theorem node008_checked : node008.check 2 point (3/128) (3/64) = true :=
  OwnershipTree.split_checked node006 node007 2 point (3/128) (1/32) (3/64) node006_checked node007_checked

def node009 : OwnershipTree := .split (3/128) node005 node008

theorem node009_checked : node009.check 2 point (1/64) (3/64) = true :=
  OwnershipTree.split_checked node005 node008 2 point (1/64) (3/128) (3/64) node005_checked node008_checked

def node010 : OwnershipTree := .split (1/64) node004 node009

theorem node010_checked : node010.check 2 point 0 (3/64) = true :=
  OwnershipTree.split_checked node004 node009 2 point 0 (1/64) (3/64) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 2 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf006 2 point (3/64) (1/16) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 2 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf007 2 point (1/16) (3/32) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 2 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf008 2 point (3/32) (1/8) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (3/32) node012 node013

theorem node014_checked : node014.check 2 point (1/16) (1/8) = true :=
  OwnershipTree.split_checked node012 node013 2 point (1/16) (3/32) (1/8) node012_checked node013_checked

def node015 : OwnershipTree := .split (1/16) node011 node014

theorem node015_checked : node015.check 2 point (3/64) (1/8) = true :=
  OwnershipTree.split_checked node011 node014 2 point (3/64) (1/16) (1/8) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 2 point (1/8) (3/16) = true :=
  OwnershipTree.leaf_checked leaf009 2 point (1/8) (3/16) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 2 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf010 2 point (3/16) (1/4) rfl rfl leaf010_checked

def node018 : OwnershipTree := .split (3/16) node016 node017

theorem node018_checked : node018.check 2 point (1/8) (1/4) = true :=
  OwnershipTree.split_checked node016 node017 2 point (1/8) (3/16) (1/4) node016_checked node017_checked

def node019 : OwnershipTree := .leaf leaf011

theorem node019_checked : node019.check 2 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf011 2 point (1/4) (3/8) rfl rfl leaf011_checked

def node020 : OwnershipTree := .leaf leaf012

theorem node020_checked : node020.check 2 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf012 2 point (3/8) (1/2) rfl rfl leaf012_checked

def node021 : OwnershipTree := .split (3/8) node019 node020

theorem node021_checked : node021.check 2 point (1/4) (1/2) = true :=
  OwnershipTree.split_checked node019 node020 2 point (1/4) (3/8) (1/2) node019_checked node020_checked

def node022 : OwnershipTree := .split (1/4) node018 node021

theorem node022_checked : node022.check 2 point (1/8) (1/2) = true :=
  OwnershipTree.split_checked node018 node021 2 point (1/8) (1/4) (1/2) node018_checked node021_checked

def node023 : OwnershipTree := .split (1/8) node015 node022

theorem node023_checked : node023.check 2 point (3/64) (1/2) = true :=
  OwnershipTree.split_checked node015 node022 2 point (3/64) (1/8) (1/2) node015_checked node022_checked

def node024 : OwnershipTree := .split (3/64) node010 node023

theorem node024_checked : node024.check 2 point 0 (1/2) = true :=
  OwnershipTree.split_checked node010 node023 2 point 0 (3/64) (1/2) node010_checked node023_checked

def node025 : OwnershipTree := .leaf leaf013

theorem node025_checked : node025.check 2 point (1/2) (17/32) = true :=
  OwnershipTree.leaf_checked leaf013 2 point (1/2) (17/32) rfl rfl leaf013_checked

def node026 : OwnershipTree := .leaf leaf014

theorem node026_checked : node026.check 2 point (17/32) (9/16) = true :=
  OwnershipTree.leaf_checked leaf014 2 point (17/32) (9/16) rfl rfl leaf014_checked

def node027 : OwnershipTree := .leaf leaf015

theorem node027_checked : node027.check 2 point (9/16) (37/64) = true :=
  OwnershipTree.leaf_checked leaf015 2 point (9/16) (37/64) rfl rfl leaf015_checked

def node028 : OwnershipTree := .split (9/16) node026 node027

theorem node028_checked : node028.check 2 point (17/32) (37/64) = true :=
  OwnershipTree.split_checked node026 node027 2 point (17/32) (9/16) (37/64) node026_checked node027_checked

def node029 : OwnershipTree := .split (17/32) node025 node028

theorem node029_checked : node029.check 2 point (1/2) (37/64) = true :=
  OwnershipTree.split_checked node025 node028 2 point (1/2) (17/32) (37/64) node025_checked node028_checked

def node030 : OwnershipTree := .leaf leaf016

theorem node030_checked : node030.check 2 point (37/64) (19/32) = true :=
  OwnershipTree.leaf_checked leaf016 2 point (37/64) (19/32) rfl rfl leaf016_checked

def node031 : OwnershipTree := .leaf leaf017

theorem node031_checked : node031.check 2 point (19/32) (39/64) = true :=
  OwnershipTree.leaf_checked leaf017 2 point (19/32) (39/64) rfl rfl leaf017_checked

def node032 : OwnershipTree := .split (19/32) node030 node031

theorem node032_checked : node032.check 2 point (37/64) (39/64) = true :=
  OwnershipTree.split_checked node030 node031 2 point (37/64) (19/32) (39/64) node030_checked node031_checked

def node033 : OwnershipTree := .leaf leaf018

theorem node033_checked : node033.check 2 point (39/64) (5/8) = true :=
  OwnershipTree.leaf_checked leaf018 2 point (39/64) (5/8) rfl rfl leaf018_checked

def node034 : OwnershipTree := .leaf leaf019

theorem node034_checked : node034.check 2 point (5/8) (21/32) = true :=
  OwnershipTree.leaf_checked leaf019 2 point (5/8) (21/32) rfl rfl leaf019_checked

def node035 : OwnershipTree := .split (5/8) node033 node034

theorem node035_checked : node035.check 2 point (39/64) (21/32) = true :=
  OwnershipTree.split_checked node033 node034 2 point (39/64) (5/8) (21/32) node033_checked node034_checked

def node036 : OwnershipTree := .split (39/64) node032 node035

theorem node036_checked : node036.check 2 point (37/64) (21/32) = true :=
  OwnershipTree.split_checked node032 node035 2 point (37/64) (39/64) (21/32) node032_checked node035_checked

def node037 : OwnershipTree := .split (37/64) node029 node036

theorem node037_checked : node037.check 2 point (1/2) (21/32) = true :=
  OwnershipTree.split_checked node029 node036 2 point (1/2) (37/64) (21/32) node029_checked node036_checked

def node038 : OwnershipTree := .leaf leaf020

theorem node038_checked : node038.check 2 point (21/32) (11/16) = true :=
  OwnershipTree.leaf_checked leaf020 2 point (21/32) (11/16) rfl rfl leaf020_checked

def node039 : OwnershipTree := .leaf leaf021

theorem node039_checked : node039.check 2 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf021 2 point (11/16) (3/4) rfl rfl leaf021_checked

def node040 : OwnershipTree := .leaf leaf022

theorem node040_checked : node040.check 2 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf022 2 point (3/4) (7/8) rfl rfl leaf022_checked

def node041 : OwnershipTree := .split (3/4) node039 node040

theorem node041_checked : node041.check 2 point (11/16) (7/8) = true :=
  OwnershipTree.split_checked node039 node040 2 point (11/16) (3/4) (7/8) node039_checked node040_checked

def node042 : OwnershipTree := .split (11/16) node038 node041

theorem node042_checked : node042.check 2 point (21/32) (7/8) = true :=
  OwnershipTree.split_checked node038 node041 2 point (21/32) (11/16) (7/8) node038_checked node041_checked

def node043 : OwnershipTree := .leaf leaf023

theorem node043_checked : node043.check 2 point (7/8) (15/16) = true :=
  OwnershipTree.leaf_checked leaf023 2 point (7/8) (15/16) rfl rfl leaf023_checked

def node044 : OwnershipTree := .leaf leaf024

theorem node044_checked : node044.check 2 point (15/16) (31/32) = true :=
  OwnershipTree.leaf_checked leaf024 2 point (15/16) (31/32) rfl rfl leaf024_checked

def node045 : OwnershipTree := .split (15/16) node043 node044

theorem node045_checked : node045.check 2 point (7/8) (31/32) = true :=
  OwnershipTree.split_checked node043 node044 2 point (7/8) (15/16) (31/32) node043_checked node044_checked

def node046 : OwnershipTree := .leaf leaf025

theorem node046_checked : node046.check 2 point (31/32) (63/64) = true :=
  OwnershipTree.leaf_checked leaf025 2 point (31/32) (63/64) rfl rfl leaf025_checked

def node047 : OwnershipTree := .leaf leaf026

theorem node047_checked : node047.check 2 point (63/64) 1 = true :=
  OwnershipTree.leaf_checked leaf026 2 point (63/64) 1 rfl rfl leaf026_checked

def node048 : OwnershipTree := .split (63/64) node046 node047

theorem node048_checked : node048.check 2 point (31/32) 1 = true :=
  OwnershipTree.split_checked node046 node047 2 point (31/32) (63/64) 1 node046_checked node047_checked

def node049 : OwnershipTree := .split (31/32) node045 node048

theorem node049_checked : node049.check 2 point (7/8) 1 = true :=
  OwnershipTree.split_checked node045 node048 2 point (7/8) (31/32) 1 node045_checked node048_checked

def node050 : OwnershipTree := .split (7/8) node042 node049

theorem node050_checked : node050.check 2 point (21/32) 1 = true :=
  OwnershipTree.split_checked node042 node049 2 point (21/32) (7/8) 1 node042_checked node049_checked

def node051 : OwnershipTree := .split (21/32) node037 node050

theorem node051_checked : node051.check 2 point (1/2) 1 = true :=
  OwnershipTree.split_checked node037 node050 2 point (1/2) (21/32) 1 node037_checked node050_checked

def node052 : OwnershipTree := .split (1/2) node024 node051

theorem node052_checked : node052.check 2 point 0 1 = true :=
  OwnershipTree.split_checked node024 node051 2 point 0 (1/2) 1 node024_checked node051_checked

def certificate : OwnershipTree := node052

theorem checked : certificate.check 2 point 0 1 = true := node052_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 2 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 2 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned02_00
