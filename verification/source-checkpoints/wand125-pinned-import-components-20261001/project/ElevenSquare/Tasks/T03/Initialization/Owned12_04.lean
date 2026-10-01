import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned12_04Part000
import ElevenSquare.Tasks.T03.Initialization.Owned12_04Part001
import ElevenSquare.Tasks.T03.Initialization.Owned12_04Part002
import ElevenSquare.Tasks.T03.Initialization.Owned12_04Part003
import ElevenSquare.Tasks.T03.Initialization.Owned12_04Part004

namespace ElevenSquare.Pending.T03.Initialization.Owned12_04
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 12 point 0 (1/512) = true :=
  OwnershipTree.leaf_checked leaf000 12 point 0 (1/512) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 12 point (1/512) (1/256) = true :=
  OwnershipTree.leaf_checked leaf001 12 point (1/512) (1/256) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/512) node000 node001

theorem node002_checked : node002.check 12 point 0 (1/256) = true :=
  OwnershipTree.split_checked node000 node001 12 point 0 (1/512) (1/256) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 12 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf002 12 point (1/256) (1/128) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 12 point (1/128) (3/256) = true :=
  OwnershipTree.leaf_checked leaf003 12 point (1/128) (3/256) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (1/128) node003 node004

theorem node005_checked : node005.check 12 point (1/256) (3/256) = true :=
  OwnershipTree.split_checked node003 node004 12 point (1/256) (1/128) (3/256) node003_checked node004_checked

def node006 : OwnershipTree := .split (1/256) node002 node005

theorem node006_checked : node006.check 12 point 0 (3/256) = true :=
  OwnershipTree.split_checked node002 node005 12 point 0 (1/256) (3/256) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 12 point (3/256) (1/64) = true :=
  OwnershipTree.leaf_checked leaf004 12 point (3/256) (1/64) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 12 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf005 12 point (1/64) (3/128) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (1/64) node007 node008

theorem node009_checked : node009.check 12 point (3/256) (3/128) = true :=
  OwnershipTree.split_checked node007 node008 12 point (3/256) (1/64) (3/128) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 12 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf006 12 point (3/128) (1/32) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 12 point (1/32) (5/128) = true :=
  OwnershipTree.leaf_checked leaf007 12 point (1/32) (5/128) rfl rfl leaf007_checked

def node012 : OwnershipTree := .split (1/32) node010 node011

theorem node012_checked : node012.check 12 point (3/128) (5/128) = true :=
  OwnershipTree.split_checked node010 node011 12 point (3/128) (1/32) (5/128) node010_checked node011_checked

def node013 : OwnershipTree := .split (3/128) node009 node012

theorem node013_checked : node013.check 12 point (3/256) (5/128) = true :=
  OwnershipTree.split_checked node009 node012 12 point (3/256) (3/128) (5/128) node009_checked node012_checked

def node014 : OwnershipTree := .split (3/256) node006 node013

theorem node014_checked : node014.check 12 point 0 (5/128) = true :=
  OwnershipTree.split_checked node006 node013 12 point 0 (3/256) (5/128) node006_checked node013_checked

def node015 : OwnershipTree := .leaf leaf008

theorem node015_checked : node015.check 12 point (5/128) (3/64) = true :=
  OwnershipTree.leaf_checked leaf008 12 point (5/128) (3/64) rfl rfl leaf008_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 12 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf009 12 point (3/64) (1/16) rfl rfl leaf009_checked

def node017 : OwnershipTree := .split (3/64) node015 node016

theorem node017_checked : node017.check 12 point (5/128) (1/16) = true :=
  OwnershipTree.split_checked node015 node016 12 point (5/128) (3/64) (1/16) node015_checked node016_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 12 point (1/16) (5/64) = true :=
  OwnershipTree.leaf_checked leaf010 12 point (1/16) (5/64) rfl rfl leaf010_checked

def node019 : OwnershipTree := .leaf leaf011

theorem node019_checked : node019.check 12 point (5/64) (3/32) = true :=
  OwnershipTree.leaf_checked leaf011 12 point (5/64) (3/32) rfl rfl leaf011_checked

def node020 : OwnershipTree := .split (5/64) node018 node019

theorem node020_checked : node020.check 12 point (1/16) (3/32) = true :=
  OwnershipTree.split_checked node018 node019 12 point (1/16) (5/64) (3/32) node018_checked node019_checked

def node021 : OwnershipTree := .split (1/16) node017 node020

theorem node021_checked : node021.check 12 point (5/128) (3/32) = true :=
  OwnershipTree.split_checked node017 node020 12 point (5/128) (1/16) (3/32) node017_checked node020_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 12 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf012 12 point (3/32) (1/8) rfl rfl leaf012_checked

def node023 : OwnershipTree := .leaf leaf013

theorem node023_checked : node023.check 12 point (1/8) (5/32) = true :=
  OwnershipTree.leaf_checked leaf013 12 point (1/8) (5/32) rfl rfl leaf013_checked

def node024 : OwnershipTree := .split (1/8) node022 node023

theorem node024_checked : node024.check 12 point (3/32) (5/32) = true :=
  OwnershipTree.split_checked node022 node023 12 point (3/32) (1/8) (5/32) node022_checked node023_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 12 point (5/32) (3/16) = true :=
  OwnershipTree.leaf_checked leaf014 12 point (5/32) (3/16) rfl rfl leaf014_checked

def node026 : OwnershipTree := .leaf leaf015

theorem node026_checked : node026.check 12 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf015 12 point (3/16) (1/4) rfl rfl leaf015_checked

def node027 : OwnershipTree := .split (3/16) node025 node026

theorem node027_checked : node027.check 12 point (5/32) (1/4) = true :=
  OwnershipTree.split_checked node025 node026 12 point (5/32) (3/16) (1/4) node025_checked node026_checked

def node028 : OwnershipTree := .split (5/32) node024 node027

theorem node028_checked : node028.check 12 point (3/32) (1/4) = true :=
  OwnershipTree.split_checked node024 node027 12 point (3/32) (5/32) (1/4) node024_checked node027_checked

def node029 : OwnershipTree := .split (3/32) node021 node028

theorem node029_checked : node029.check 12 point (5/128) (1/4) = true :=
  OwnershipTree.split_checked node021 node028 12 point (5/128) (3/32) (1/4) node021_checked node028_checked

def node030 : OwnershipTree := .split (5/128) node014 node029

theorem node030_checked : node030.check 12 point 0 (1/4) = true :=
  OwnershipTree.split_checked node014 node029 12 point 0 (5/128) (1/4) node014_checked node029_checked

def node031 : OwnershipTree := .leaf leaf016

theorem node031_checked : node031.check 12 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf016 12 point (1/4) (3/8) rfl rfl leaf016_checked

def node032 : OwnershipTree := .leaf leaf017

theorem node032_checked : node032.check 12 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf017 12 point (3/8) (1/2) rfl rfl leaf017_checked

def node033 : OwnershipTree := .split (3/8) node031 node032

theorem node033_checked : node033.check 12 point (1/4) (1/2) = true :=
  OwnershipTree.split_checked node031 node032 12 point (1/4) (3/8) (1/2) node031_checked node032_checked

def node034 : OwnershipTree := .leaf leaf018

theorem node034_checked : node034.check 12 point (1/2) (17/32) = true :=
  OwnershipTree.leaf_checked leaf018 12 point (1/2) (17/32) rfl rfl leaf018_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 12 point (17/32) (9/16) = true :=
  OwnershipTree.leaf_checked leaf019 12 point (17/32) (9/16) rfl rfl leaf019_checked

def node036 : OwnershipTree := .split (17/32) node034 node035

theorem node036_checked : node036.check 12 point (1/2) (9/16) = true :=
  OwnershipTree.split_checked node034 node035 12 point (1/2) (17/32) (9/16) node034_checked node035_checked

def node037 : OwnershipTree := .split (1/2) node033 node036

theorem node037_checked : node037.check 12 point (1/4) (9/16) = true :=
  OwnershipTree.split_checked node033 node036 12 point (1/4) (1/2) (9/16) node033_checked node036_checked

def node038 : OwnershipTree := .leaf leaf020

theorem node038_checked : node038.check 12 point (9/16) (37/64) = true :=
  OwnershipTree.leaf_checked leaf020 12 point (9/16) (37/64) rfl rfl leaf020_checked

def node039 : OwnershipTree := .leaf leaf021

theorem node039_checked : node039.check 12 point (37/64) (19/32) = true :=
  OwnershipTree.leaf_checked leaf021 12 point (37/64) (19/32) rfl rfl leaf021_checked

def node040 : OwnershipTree := .split (37/64) node038 node039

theorem node040_checked : node040.check 12 point (9/16) (19/32) = true :=
  OwnershipTree.split_checked node038 node039 12 point (9/16) (37/64) (19/32) node038_checked node039_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 12 point (19/32) (39/64) = true :=
  OwnershipTree.leaf_checked leaf022 12 point (19/32) (39/64) rfl rfl leaf022_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 12 point (39/64) (5/8) = true :=
  OwnershipTree.leaf_checked leaf023 12 point (39/64) (5/8) rfl rfl leaf023_checked

def node043 : OwnershipTree := .split (39/64) node041 node042

theorem node043_checked : node043.check 12 point (19/32) (5/8) = true :=
  OwnershipTree.split_checked node041 node042 12 point (19/32) (39/64) (5/8) node041_checked node042_checked

def node044 : OwnershipTree := .split (19/32) node040 node043

theorem node044_checked : node044.check 12 point (9/16) (5/8) = true :=
  OwnershipTree.split_checked node040 node043 12 point (9/16) (19/32) (5/8) node040_checked node043_checked

def node045 : OwnershipTree := .split (9/16) node037 node044

theorem node045_checked : node045.check 12 point (1/4) (5/8) = true :=
  OwnershipTree.split_checked node037 node044 12 point (1/4) (9/16) (5/8) node037_checked node044_checked

def node046 : OwnershipTree := .leaf leaf024

theorem node046_checked : node046.check 12 point (5/8) (21/32) = true :=
  OwnershipTree.leaf_checked leaf024 12 point (5/8) (21/32) rfl rfl leaf024_checked

def node047 : OwnershipTree := .leaf leaf025

theorem node047_checked : node047.check 12 point (21/32) (11/16) = true :=
  OwnershipTree.leaf_checked leaf025 12 point (21/32) (11/16) rfl rfl leaf025_checked

def node048 : OwnershipTree := .split (21/32) node046 node047

theorem node048_checked : node048.check 12 point (5/8) (11/16) = true :=
  OwnershipTree.split_checked node046 node047 12 point (5/8) (21/32) (11/16) node046_checked node047_checked

def node049 : OwnershipTree := .leaf leaf026

theorem node049_checked : node049.check 12 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf026 12 point (11/16) (3/4) rfl rfl leaf026_checked

def node050 : OwnershipTree := .leaf leaf027

theorem node050_checked : node050.check 12 point (3/4) (7/8) = true :=
  OwnershipTree.leaf_checked leaf027 12 point (3/4) (7/8) rfl rfl leaf027_checked

def node051 : OwnershipTree := .split (3/4) node049 node050

theorem node051_checked : node051.check 12 point (11/16) (7/8) = true :=
  OwnershipTree.split_checked node049 node050 12 point (11/16) (3/4) (7/8) node049_checked node050_checked

def node052 : OwnershipTree := .split (11/16) node048 node051

theorem node052_checked : node052.check 12 point (5/8) (7/8) = true :=
  OwnershipTree.split_checked node048 node051 12 point (5/8) (11/16) (7/8) node048_checked node051_checked

def node053 : OwnershipTree := .leaf leaf028

theorem node053_checked : node053.check 12 point (7/8) (15/16) = true :=
  OwnershipTree.leaf_checked leaf028 12 point (7/8) (15/16) rfl rfl leaf028_checked

def node054 : OwnershipTree := .leaf leaf029

theorem node054_checked : node054.check 12 point (15/16) (31/32) = true :=
  OwnershipTree.leaf_checked leaf029 12 point (15/16) (31/32) rfl rfl leaf029_checked

def node055 : OwnershipTree := .split (15/16) node053 node054

theorem node055_checked : node055.check 12 point (7/8) (31/32) = true :=
  OwnershipTree.split_checked node053 node054 12 point (7/8) (15/16) (31/32) node053_checked node054_checked

def node056 : OwnershipTree := .leaf leaf030

theorem node056_checked : node056.check 12 point (31/32) (63/64) = true :=
  OwnershipTree.leaf_checked leaf030 12 point (31/32) (63/64) rfl rfl leaf030_checked

def node057 : OwnershipTree := .leaf leaf031

theorem node057_checked : node057.check 12 point (63/64) (127/128) = true :=
  OwnershipTree.leaf_checked leaf031 12 point (63/64) (127/128) rfl rfl leaf031_checked

def node058 : OwnershipTree := .leaf leaf032

theorem node058_checked : node058.check 12 point (127/128) 1 = true :=
  OwnershipTree.leaf_checked leaf032 12 point (127/128) 1 rfl rfl leaf032_checked

def node059 : OwnershipTree := .split (127/128) node057 node058

theorem node059_checked : node059.check 12 point (63/64) 1 = true :=
  OwnershipTree.split_checked node057 node058 12 point (63/64) (127/128) 1 node057_checked node058_checked

def node060 : OwnershipTree := .split (63/64) node056 node059

theorem node060_checked : node060.check 12 point (31/32) 1 = true :=
  OwnershipTree.split_checked node056 node059 12 point (31/32) (63/64) 1 node056_checked node059_checked

def node061 : OwnershipTree := .split (31/32) node055 node060

theorem node061_checked : node061.check 12 point (7/8) 1 = true :=
  OwnershipTree.split_checked node055 node060 12 point (7/8) (31/32) 1 node055_checked node060_checked

def node062 : OwnershipTree := .split (7/8) node052 node061

theorem node062_checked : node062.check 12 point (5/8) 1 = true :=
  OwnershipTree.split_checked node052 node061 12 point (5/8) (7/8) 1 node052_checked node061_checked

def node063 : OwnershipTree := .split (5/8) node045 node062

theorem node063_checked : node063.check 12 point (1/4) 1 = true :=
  OwnershipTree.split_checked node045 node062 12 point (1/4) (5/8) 1 node045_checked node062_checked

def node064 : OwnershipTree := .split (1/4) node030 node063

theorem node064_checked : node064.check 12 point 0 1 = true :=
  OwnershipTree.split_checked node030 node063 12 point 0 (1/4) 1 node030_checked node063_checked

def certificate : OwnershipTree := node064

theorem checked : certificate.check 12 point 0 1 = true := node064_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 12 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 12 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned12_04
