import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned07_00Part000
import ElevenSquare.Tasks.T03.Initialization.Owned07_00Part001
import ElevenSquare.Tasks.T03.Initialization.Owned07_00Part002
import ElevenSquare.Tasks.T03.Initialization.Owned07_00Part003
import ElevenSquare.Tasks.T03.Initialization.Owned07_00Part004

namespace ElevenSquare.Pending.T03.Initialization.Owned07_00
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 7 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 7 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 7 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 7 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/256) node000 node001

theorem node002_checked : node002.check 7 point 0 (1/128) = true :=
  OwnershipTree.split_checked node000 node001 7 point 0 (1/256) (1/128) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 7 point (1/128) (3/256) = true :=
  OwnershipTree.leaf_checked leaf002 7 point (1/128) (3/256) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 7 point (3/256) (1/64) = true :=
  OwnershipTree.leaf_checked leaf003 7 point (3/256) (1/64) rfl rfl leaf003_checked

def node005 : OwnershipTree := .split (3/256) node003 node004

theorem node005_checked : node005.check 7 point (1/128) (1/64) = true :=
  OwnershipTree.split_checked node003 node004 7 point (1/128) (3/256) (1/64) node003_checked node004_checked

def node006 : OwnershipTree := .split (1/128) node002 node005

theorem node006_checked : node006.check 7 point 0 (1/64) = true :=
  OwnershipTree.split_checked node002 node005 7 point 0 (1/128) (1/64) node002_checked node005_checked

def node007 : OwnershipTree := .leaf leaf004

theorem node007_checked : node007.check 7 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf004 7 point (1/64) (3/128) rfl rfl leaf004_checked

def node008 : OwnershipTree := .leaf leaf005

theorem node008_checked : node008.check 7 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf005 7 point (3/128) (1/32) rfl rfl leaf005_checked

def node009 : OwnershipTree := .split (3/128) node007 node008

theorem node009_checked : node009.check 7 point (1/64) (1/32) = true :=
  OwnershipTree.split_checked node007 node008 7 point (1/64) (3/128) (1/32) node007_checked node008_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 7 point (1/32) (5/128) = true :=
  OwnershipTree.leaf_checked leaf006 7 point (1/32) (5/128) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 7 point (5/128) (3/64) = true :=
  OwnershipTree.leaf_checked leaf007 7 point (5/128) (3/64) rfl rfl leaf007_checked

def node012 : OwnershipTree := .leaf leaf008

theorem node012_checked : node012.check 7 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf008 7 point (3/64) (1/16) rfl rfl leaf008_checked

def node013 : OwnershipTree := .split (3/64) node011 node012

theorem node013_checked : node013.check 7 point (5/128) (1/16) = true :=
  OwnershipTree.split_checked node011 node012 7 point (5/128) (3/64) (1/16) node011_checked node012_checked

def node014 : OwnershipTree := .split (5/128) node010 node013

theorem node014_checked : node014.check 7 point (1/32) (1/16) = true :=
  OwnershipTree.split_checked node010 node013 7 point (1/32) (5/128) (1/16) node010_checked node013_checked

def node015 : OwnershipTree := .split (1/32) node009 node014

theorem node015_checked : node015.check 7 point (1/64) (1/16) = true :=
  OwnershipTree.split_checked node009 node014 7 point (1/64) (1/32) (1/16) node009_checked node014_checked

def node016 : OwnershipTree := .split (1/64) node006 node015

theorem node016_checked : node016.check 7 point 0 (1/16) = true :=
  OwnershipTree.split_checked node006 node015 7 point 0 (1/64) (1/16) node006_checked node015_checked

def node017 : OwnershipTree := .leaf leaf009

theorem node017_checked : node017.check 7 point (1/16) (5/64) = true :=
  OwnershipTree.leaf_checked leaf009 7 point (1/16) (5/64) rfl rfl leaf009_checked

def node018 : OwnershipTree := .leaf leaf010

theorem node018_checked : node018.check 7 point (5/64) (3/32) = true :=
  OwnershipTree.leaf_checked leaf010 7 point (5/64) (3/32) rfl rfl leaf010_checked

def node019 : OwnershipTree := .split (5/64) node017 node018

theorem node019_checked : node019.check 7 point (1/16) (3/32) = true :=
  OwnershipTree.split_checked node017 node018 7 point (1/16) (5/64) (3/32) node017_checked node018_checked

def node020 : OwnershipTree := .leaf leaf011

theorem node020_checked : node020.check 7 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf011 7 point (3/32) (1/8) rfl rfl leaf011_checked

def node021 : OwnershipTree := .leaf leaf012

theorem node021_checked : node021.check 7 point (1/8) (5/32) = true :=
  OwnershipTree.leaf_checked leaf012 7 point (1/8) (5/32) rfl rfl leaf012_checked

def node022 : OwnershipTree := .leaf leaf013

theorem node022_checked : node022.check 7 point (5/32) (3/16) = true :=
  OwnershipTree.leaf_checked leaf013 7 point (5/32) (3/16) rfl rfl leaf013_checked

def node023 : OwnershipTree := .split (5/32) node021 node022

theorem node023_checked : node023.check 7 point (1/8) (3/16) = true :=
  OwnershipTree.split_checked node021 node022 7 point (1/8) (5/32) (3/16) node021_checked node022_checked

def node024 : OwnershipTree := .split (1/8) node020 node023

theorem node024_checked : node024.check 7 point (3/32) (3/16) = true :=
  OwnershipTree.split_checked node020 node023 7 point (3/32) (1/8) (3/16) node020_checked node023_checked

def node025 : OwnershipTree := .split (3/32) node019 node024

theorem node025_checked : node025.check 7 point (1/16) (3/16) = true :=
  OwnershipTree.split_checked node019 node024 7 point (1/16) (3/32) (3/16) node019_checked node024_checked

def node026 : OwnershipTree := .leaf leaf014

theorem node026_checked : node026.check 7 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf014 7 point (3/16) (1/4) rfl rfl leaf014_checked

def node027 : OwnershipTree := .leaf leaf015

theorem node027_checked : node027.check 7 point (1/4) (3/8) = true :=
  OwnershipTree.leaf_checked leaf015 7 point (1/4) (3/8) rfl rfl leaf015_checked

def node028 : OwnershipTree := .split (1/4) node026 node027

theorem node028_checked : node028.check 7 point (3/16) (3/8) = true :=
  OwnershipTree.split_checked node026 node027 7 point (3/16) (1/4) (3/8) node026_checked node027_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 7 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf016 7 point (3/8) (1/2) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 7 point (1/2) (17/32) = true :=
  OwnershipTree.leaf_checked leaf017 7 point (1/2) (17/32) rfl rfl leaf017_checked

def node031 : OwnershipTree := .leaf leaf018

theorem node031_checked : node031.check 7 point (17/32) (9/16) = true :=
  OwnershipTree.leaf_checked leaf018 7 point (17/32) (9/16) rfl rfl leaf018_checked

def node032 : OwnershipTree := .split (17/32) node030 node031

theorem node032_checked : node032.check 7 point (1/2) (9/16) = true :=
  OwnershipTree.split_checked node030 node031 7 point (1/2) (17/32) (9/16) node030_checked node031_checked

def node033 : OwnershipTree := .split (1/2) node029 node032

theorem node033_checked : node033.check 7 point (3/8) (9/16) = true :=
  OwnershipTree.split_checked node029 node032 7 point (3/8) (1/2) (9/16) node029_checked node032_checked

def node034 : OwnershipTree := .split (3/8) node028 node033

theorem node034_checked : node034.check 7 point (3/16) (9/16) = true :=
  OwnershipTree.split_checked node028 node033 7 point (3/16) (3/8) (9/16) node028_checked node033_checked

def node035 : OwnershipTree := .split (3/16) node025 node034

theorem node035_checked : node035.check 7 point (1/16) (9/16) = true :=
  OwnershipTree.split_checked node025 node034 7 point (1/16) (3/16) (9/16) node025_checked node034_checked

def node036 : OwnershipTree := .split (1/16) node016 node035

theorem node036_checked : node036.check 7 point 0 (9/16) = true :=
  OwnershipTree.split_checked node016 node035 7 point 0 (1/16) (9/16) node016_checked node035_checked

def node037 : OwnershipTree := .leaf leaf019

theorem node037_checked : node037.check 7 point (9/16) (37/64) = true :=
  OwnershipTree.leaf_checked leaf019 7 point (9/16) (37/64) rfl rfl leaf019_checked

def node038 : OwnershipTree := .leaf leaf020

theorem node038_checked : node038.check 7 point (37/64) (19/32) = true :=
  OwnershipTree.leaf_checked leaf020 7 point (37/64) (19/32) rfl rfl leaf020_checked

def node039 : OwnershipTree := .split (37/64) node037 node038

theorem node039_checked : node039.check 7 point (9/16) (19/32) = true :=
  OwnershipTree.split_checked node037 node038 7 point (9/16) (37/64) (19/32) node037_checked node038_checked

def node040 : OwnershipTree := .leaf leaf021

theorem node040_checked : node040.check 7 point (19/32) (77/128) = true :=
  OwnershipTree.leaf_checked leaf021 7 point (19/32) (77/128) rfl rfl leaf021_checked

def node041 : OwnershipTree := .leaf leaf022

theorem node041_checked : node041.check 7 point (77/128) (39/64) = true :=
  OwnershipTree.leaf_checked leaf022 7 point (77/128) (39/64) rfl rfl leaf022_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 7 point (39/64) (5/8) = true :=
  OwnershipTree.leaf_checked leaf023 7 point (39/64) (5/8) rfl rfl leaf023_checked

def node043 : OwnershipTree := .split (39/64) node041 node042

theorem node043_checked : node043.check 7 point (77/128) (5/8) = true :=
  OwnershipTree.split_checked node041 node042 7 point (77/128) (39/64) (5/8) node041_checked node042_checked

def node044 : OwnershipTree := .split (77/128) node040 node043

theorem node044_checked : node044.check 7 point (19/32) (5/8) = true :=
  OwnershipTree.split_checked node040 node043 7 point (19/32) (77/128) (5/8) node040_checked node043_checked

def node045 : OwnershipTree := .split (19/32) node039 node044

theorem node045_checked : node045.check 7 point (9/16) (5/8) = true :=
  OwnershipTree.split_checked node039 node044 7 point (9/16) (19/32) (5/8) node039_checked node044_checked

def node046 : OwnershipTree := .leaf leaf024

theorem node046_checked : node046.check 7 point (5/8) (41/64) = true :=
  OwnershipTree.leaf_checked leaf024 7 point (5/8) (41/64) rfl rfl leaf024_checked

def node047 : OwnershipTree := .leaf leaf025

theorem node047_checked : node047.check 7 point (41/64) (21/32) = true :=
  OwnershipTree.leaf_checked leaf025 7 point (41/64) (21/32) rfl rfl leaf025_checked

def node048 : OwnershipTree := .split (41/64) node046 node047

theorem node048_checked : node048.check 7 point (5/8) (21/32) = true :=
  OwnershipTree.split_checked node046 node047 7 point (5/8) (41/64) (21/32) node046_checked node047_checked

def node049 : OwnershipTree := .leaf leaf026

theorem node049_checked : node049.check 7 point (21/32) (43/64) = true :=
  OwnershipTree.leaf_checked leaf026 7 point (21/32) (43/64) rfl rfl leaf026_checked

def node050 : OwnershipTree := .leaf leaf027

theorem node050_checked : node050.check 7 point (43/64) (11/16) = true :=
  OwnershipTree.leaf_checked leaf027 7 point (43/64) (11/16) rfl rfl leaf027_checked

def node051 : OwnershipTree := .leaf leaf028

theorem node051_checked : node051.check 7 point (11/16) (23/32) = true :=
  OwnershipTree.leaf_checked leaf028 7 point (11/16) (23/32) rfl rfl leaf028_checked

def node052 : OwnershipTree := .split (11/16) node050 node051

theorem node052_checked : node052.check 7 point (43/64) (23/32) = true :=
  OwnershipTree.split_checked node050 node051 7 point (43/64) (11/16) (23/32) node050_checked node051_checked

def node053 : OwnershipTree := .split (43/64) node049 node052

theorem node053_checked : node053.check 7 point (21/32) (23/32) = true :=
  OwnershipTree.split_checked node049 node052 7 point (21/32) (43/64) (23/32) node049_checked node052_checked

def node054 : OwnershipTree := .split (21/32) node048 node053

theorem node054_checked : node054.check 7 point (5/8) (23/32) = true :=
  OwnershipTree.split_checked node048 node053 7 point (5/8) (21/32) (23/32) node048_checked node053_checked

def node055 : OwnershipTree := .split (5/8) node045 node054

theorem node055_checked : node055.check 7 point (9/16) (23/32) = true :=
  OwnershipTree.split_checked node045 node054 7 point (9/16) (5/8) (23/32) node045_checked node054_checked

def node056 : OwnershipTree := .leaf leaf029

theorem node056_checked : node056.check 7 point (23/32) (3/4) = true :=
  OwnershipTree.leaf_checked leaf029 7 point (23/32) (3/4) rfl rfl leaf029_checked

def node057 : OwnershipTree := .leaf leaf030

theorem node057_checked : node057.check 7 point (3/4) (13/16) = true :=
  OwnershipTree.leaf_checked leaf030 7 point (3/4) (13/16) rfl rfl leaf030_checked

def node058 : OwnershipTree := .split (3/4) node056 node057

theorem node058_checked : node058.check 7 point (23/32) (13/16) = true :=
  OwnershipTree.split_checked node056 node057 7 point (23/32) (3/4) (13/16) node056_checked node057_checked

def node059 : OwnershipTree := .leaf leaf031

theorem node059_checked : node059.check 7 point (13/16) (7/8) = true :=
  OwnershipTree.leaf_checked leaf031 7 point (13/16) (7/8) rfl rfl leaf031_checked

def node060 : OwnershipTree := .leaf leaf032

theorem node060_checked : node060.check 7 point (7/8) (29/32) = true :=
  OwnershipTree.leaf_checked leaf032 7 point (7/8) (29/32) rfl rfl leaf032_checked

def node061 : OwnershipTree := .leaf leaf033

theorem node061_checked : node061.check 7 point (29/32) (15/16) = true :=
  OwnershipTree.leaf_checked leaf033 7 point (29/32) (15/16) rfl rfl leaf033_checked

def node062 : OwnershipTree := .split (29/32) node060 node061

theorem node062_checked : node062.check 7 point (7/8) (15/16) = true :=
  OwnershipTree.split_checked node060 node061 7 point (7/8) (29/32) (15/16) node060_checked node061_checked

def node063 : OwnershipTree := .split (7/8) node059 node062

theorem node063_checked : node063.check 7 point (13/16) (15/16) = true :=
  OwnershipTree.split_checked node059 node062 7 point (13/16) (7/8) (15/16) node059_checked node062_checked

def node064 : OwnershipTree := .split (13/16) node058 node063

theorem node064_checked : node064.check 7 point (23/32) (15/16) = true :=
  OwnershipTree.split_checked node058 node063 7 point (23/32) (13/16) (15/16) node058_checked node063_checked

def node065 : OwnershipTree := .leaf leaf034

theorem node065_checked : node065.check 7 point (15/16) (61/64) = true :=
  OwnershipTree.leaf_checked leaf034 7 point (15/16) (61/64) rfl rfl leaf034_checked

def node066 : OwnershipTree := .leaf leaf035

theorem node066_checked : node066.check 7 point (61/64) (31/32) = true :=
  OwnershipTree.leaf_checked leaf035 7 point (61/64) (31/32) rfl rfl leaf035_checked

def node067 : OwnershipTree := .split (61/64) node065 node066

theorem node067_checked : node067.check 7 point (15/16) (31/32) = true :=
  OwnershipTree.split_checked node065 node066 7 point (15/16) (61/64) (31/32) node065_checked node066_checked

def node068 : OwnershipTree := .leaf leaf036

theorem node068_checked : node068.check 7 point (31/32) (63/64) = true :=
  OwnershipTree.leaf_checked leaf036 7 point (31/32) (63/64) rfl rfl leaf036_checked

def node069 : OwnershipTree := .leaf leaf037

theorem node069_checked : node069.check 7 point (63/64) (127/128) = true :=
  OwnershipTree.leaf_checked leaf037 7 point (63/64) (127/128) rfl rfl leaf037_checked

def node070 : OwnershipTree := .leaf leaf038

theorem node070_checked : node070.check 7 point (127/128) 1 = true :=
  OwnershipTree.leaf_checked leaf038 7 point (127/128) 1 rfl rfl leaf038_checked

def node071 : OwnershipTree := .split (127/128) node069 node070

theorem node071_checked : node071.check 7 point (63/64) 1 = true :=
  OwnershipTree.split_checked node069 node070 7 point (63/64) (127/128) 1 node069_checked node070_checked

def node072 : OwnershipTree := .split (63/64) node068 node071

theorem node072_checked : node072.check 7 point (31/32) 1 = true :=
  OwnershipTree.split_checked node068 node071 7 point (31/32) (63/64) 1 node068_checked node071_checked

def node073 : OwnershipTree := .split (31/32) node067 node072

theorem node073_checked : node073.check 7 point (15/16) 1 = true :=
  OwnershipTree.split_checked node067 node072 7 point (15/16) (31/32) 1 node067_checked node072_checked

def node074 : OwnershipTree := .split (15/16) node064 node073

theorem node074_checked : node074.check 7 point (23/32) 1 = true :=
  OwnershipTree.split_checked node064 node073 7 point (23/32) (15/16) 1 node064_checked node073_checked

def node075 : OwnershipTree := .split (23/32) node055 node074

theorem node075_checked : node075.check 7 point (9/16) 1 = true :=
  OwnershipTree.split_checked node055 node074 7 point (9/16) (23/32) 1 node055_checked node074_checked

def node076 : OwnershipTree := .split (9/16) node036 node075

theorem node076_checked : node076.check 7 point 0 1 = true :=
  OwnershipTree.split_checked node036 node075 7 point 0 (9/16) 1 node036_checked node075_checked

def certificate : OwnershipTree := node076

theorem checked : certificate.check 7 point 0 1 = true := node076_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 7 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 7 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned07_00
