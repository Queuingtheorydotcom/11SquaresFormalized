import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part000
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part001
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part002
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part003
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part004
import ElevenSquare.Tasks.T03.Initialization.Owned03_05Part005

namespace ElevenSquare.Pending.T03.Initialization.Owned03_05
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 3 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 3 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 3 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 3 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .split (1/256) node000 node001

theorem node002_checked : node002.check 3 point 0 (1/128) = true :=
  OwnershipTree.split_checked node000 node001 3 point 0 (1/256) (1/128) node000_checked node001_checked

def node003 : OwnershipTree := .leaf leaf002

theorem node003_checked : node003.check 3 point (1/128) (1/64) = true :=
  OwnershipTree.leaf_checked leaf002 3 point (1/128) (1/64) rfl rfl leaf002_checked

def node004 : OwnershipTree := .leaf leaf003

theorem node004_checked : node004.check 3 point (1/64) (3/128) = true :=
  OwnershipTree.leaf_checked leaf003 3 point (1/64) (3/128) rfl rfl leaf003_checked

def node005 : OwnershipTree := .leaf leaf004

theorem node005_checked : node005.check 3 point (3/128) (1/32) = true :=
  OwnershipTree.leaf_checked leaf004 3 point (3/128) (1/32) rfl rfl leaf004_checked

def node006 : OwnershipTree := .split (3/128) node004 node005

theorem node006_checked : node006.check 3 point (1/64) (1/32) = true :=
  OwnershipTree.split_checked node004 node005 3 point (1/64) (3/128) (1/32) node004_checked node005_checked

def node007 : OwnershipTree := .split (1/64) node003 node006

theorem node007_checked : node007.check 3 point (1/128) (1/32) = true :=
  OwnershipTree.split_checked node003 node006 3 point (1/128) (1/64) (1/32) node003_checked node006_checked

def node008 : OwnershipTree := .split (1/128) node002 node007

theorem node008_checked : node008.check 3 point 0 (1/32) = true :=
  OwnershipTree.split_checked node002 node007 3 point 0 (1/128) (1/32) node002_checked node007_checked

def node009 : OwnershipTree := .leaf leaf005

theorem node009_checked : node009.check 3 point (1/32) (3/64) = true :=
  OwnershipTree.leaf_checked leaf005 3 point (1/32) (3/64) rfl rfl leaf005_checked

def node010 : OwnershipTree := .leaf leaf006

theorem node010_checked : node010.check 3 point (3/64) (1/16) = true :=
  OwnershipTree.leaf_checked leaf006 3 point (3/64) (1/16) rfl rfl leaf006_checked

def node011 : OwnershipTree := .leaf leaf007

theorem node011_checked : node011.check 3 point (1/16) (3/32) = true :=
  OwnershipTree.leaf_checked leaf007 3 point (1/16) (3/32) rfl rfl leaf007_checked

def node012 : OwnershipTree := .split (1/16) node010 node011

theorem node012_checked : node012.check 3 point (3/64) (3/32) = true :=
  OwnershipTree.split_checked node010 node011 3 point (3/64) (1/16) (3/32) node010_checked node011_checked

def node013 : OwnershipTree := .split (3/64) node009 node012

theorem node013_checked : node013.check 3 point (1/32) (3/32) = true :=
  OwnershipTree.split_checked node009 node012 3 point (1/32) (3/64) (3/32) node009_checked node012_checked

def node014 : OwnershipTree := .leaf leaf008

theorem node014_checked : node014.check 3 point (3/32) (1/8) = true :=
  OwnershipTree.leaf_checked leaf008 3 point (3/32) (1/8) rfl rfl leaf008_checked

def node015 : OwnershipTree := .leaf leaf009

theorem node015_checked : node015.check 3 point (1/8) (9/64) = true :=
  OwnershipTree.leaf_checked leaf009 3 point (1/8) (9/64) rfl rfl leaf009_checked

def node016 : OwnershipTree := .leaf leaf010

theorem node016_checked : node016.check 3 point (9/64) (5/32) = true :=
  OwnershipTree.leaf_checked leaf010 3 point (9/64) (5/32) rfl rfl leaf010_checked

def node017 : OwnershipTree := .split (9/64) node015 node016

theorem node017_checked : node017.check 3 point (1/8) (5/32) = true :=
  OwnershipTree.split_checked node015 node016 3 point (1/8) (9/64) (5/32) node015_checked node016_checked

def node018 : OwnershipTree := .split (1/8) node014 node017

theorem node018_checked : node018.check 3 point (3/32) (5/32) = true :=
  OwnershipTree.split_checked node014 node017 3 point (3/32) (1/8) (5/32) node014_checked node017_checked

def node019 : OwnershipTree := .split (3/32) node013 node018

theorem node019_checked : node019.check 3 point (1/32) (5/32) = true :=
  OwnershipTree.split_checked node013 node018 3 point (1/32) (3/32) (5/32) node013_checked node018_checked

def node020 : OwnershipTree := .split (1/32) node008 node019

theorem node020_checked : node020.check 3 point 0 (5/32) = true :=
  OwnershipTree.split_checked node008 node019 3 point 0 (1/32) (5/32) node008_checked node019_checked

def node021 : OwnershipTree := .leaf leaf011

theorem node021_checked : node021.check 3 point (5/32) (11/64) = true :=
  OwnershipTree.leaf_checked leaf011 3 point (5/32) (11/64) rfl rfl leaf011_checked

def node022 : OwnershipTree := .leaf leaf012

theorem node022_checked : node022.check 3 point (11/64) (23/128) = true :=
  OwnershipTree.leaf_checked leaf012 3 point (11/64) (23/128) rfl rfl leaf012_checked

def node023 : OwnershipTree := .split (11/64) node021 node022

theorem node023_checked : node023.check 3 point (5/32) (23/128) = true :=
  OwnershipTree.split_checked node021 node022 3 point (5/32) (11/64) (23/128) node021_checked node022_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 3 point (23/128) (3/16) = true :=
  OwnershipTree.leaf_checked leaf013 3 point (23/128) (3/16) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 3 point (3/16) (25/128) = true :=
  OwnershipTree.leaf_checked leaf014 3 point (3/16) (25/128) rfl rfl leaf014_checked

def node026 : OwnershipTree := .leaf leaf015

theorem node026_checked : node026.check 3 point (25/128) (13/64) = true :=
  OwnershipTree.leaf_checked leaf015 3 point (25/128) (13/64) rfl rfl leaf015_checked

def node027 : OwnershipTree := .split (25/128) node025 node026

theorem node027_checked : node027.check 3 point (3/16) (13/64) = true :=
  OwnershipTree.split_checked node025 node026 3 point (3/16) (25/128) (13/64) node025_checked node026_checked

def node028 : OwnershipTree := .split (3/16) node024 node027

theorem node028_checked : node028.check 3 point (23/128) (13/64) = true :=
  OwnershipTree.split_checked node024 node027 3 point (23/128) (3/16) (13/64) node024_checked node027_checked

def node029 : OwnershipTree := .split (23/128) node023 node028

theorem node029_checked : node029.check 3 point (5/32) (13/64) = true :=
  OwnershipTree.split_checked node023 node028 3 point (5/32) (23/128) (13/64) node023_checked node028_checked

def node030 : OwnershipTree := .leaf leaf016

theorem node030_checked : node030.check 3 point (13/64) (27/128) = true :=
  OwnershipTree.leaf_checked leaf016 3 point (13/64) (27/128) rfl rfl leaf016_checked

def node031 : OwnershipTree := .leaf leaf017

theorem node031_checked : node031.check 3 point (27/128) (7/32) = true :=
  OwnershipTree.leaf_checked leaf017 3 point (27/128) (7/32) rfl rfl leaf017_checked

def node032 : OwnershipTree := .leaf leaf018

theorem node032_checked : node032.check 3 point (7/32) (29/128) = true :=
  OwnershipTree.leaf_checked leaf018 3 point (7/32) (29/128) rfl rfl leaf018_checked

def node033 : OwnershipTree := .split (7/32) node031 node032

theorem node033_checked : node033.check 3 point (27/128) (29/128) = true :=
  OwnershipTree.split_checked node031 node032 3 point (27/128) (7/32) (29/128) node031_checked node032_checked

def node034 : OwnershipTree := .split (27/128) node030 node033

theorem node034_checked : node034.check 3 point (13/64) (29/128) = true :=
  OwnershipTree.split_checked node030 node033 3 point (13/64) (27/128) (29/128) node030_checked node033_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 3 point (29/128) (15/64) = true :=
  OwnershipTree.leaf_checked leaf019 3 point (29/128) (15/64) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 3 point (15/64) (31/128) = true :=
  OwnershipTree.leaf_checked leaf020 3 point (15/64) (31/128) rfl rfl leaf020_checked

def node037 : OwnershipTree := .leaf leaf021

theorem node037_checked : node037.check 3 point (31/128) (1/4) = true :=
  OwnershipTree.leaf_checked leaf021 3 point (31/128) (1/4) rfl rfl leaf021_checked

def node038 : OwnershipTree := .split (31/128) node036 node037

theorem node038_checked : node038.check 3 point (15/64) (1/4) = true :=
  OwnershipTree.split_checked node036 node037 3 point (15/64) (31/128) (1/4) node036_checked node037_checked

def node039 : OwnershipTree := .split (15/64) node035 node038

theorem node039_checked : node039.check 3 point (29/128) (1/4) = true :=
  OwnershipTree.split_checked node035 node038 3 point (29/128) (15/64) (1/4) node035_checked node038_checked

def node040 : OwnershipTree := .split (29/128) node034 node039

theorem node040_checked : node040.check 3 point (13/64) (1/4) = true :=
  OwnershipTree.split_checked node034 node039 3 point (13/64) (29/128) (1/4) node034_checked node039_checked

def node041 : OwnershipTree := .split (13/64) node029 node040

theorem node041_checked : node041.check 3 point (5/32) (1/4) = true :=
  OwnershipTree.split_checked node029 node040 3 point (5/32) (13/64) (1/4) node029_checked node040_checked

def node042 : OwnershipTree := .split (5/32) node020 node041

theorem node042_checked : node042.check 3 point 0 (1/4) = true :=
  OwnershipTree.split_checked node020 node041 3 point 0 (5/32) (1/4) node020_checked node041_checked

def node043 : OwnershipTree := .leaf leaf022

theorem node043_checked : node043.check 3 point (1/4) (17/64) = true :=
  OwnershipTree.leaf_checked leaf022 3 point (1/4) (17/64) rfl rfl leaf022_checked

def node044 : OwnershipTree := .leaf leaf023

theorem node044_checked : node044.check 3 point (17/64) (9/32) = true :=
  OwnershipTree.leaf_checked leaf023 3 point (17/64) (9/32) rfl rfl leaf023_checked

def node045 : OwnershipTree := .split (17/64) node043 node044

theorem node045_checked : node045.check 3 point (1/4) (9/32) = true :=
  OwnershipTree.split_checked node043 node044 3 point (1/4) (17/64) (9/32) node043_checked node044_checked

def node046 : OwnershipTree := .leaf leaf024

theorem node046_checked : node046.check 3 point (9/32) (5/16) = true :=
  OwnershipTree.leaf_checked leaf024 3 point (9/32) (5/16) rfl rfl leaf024_checked

def node047 : OwnershipTree := .leaf leaf025

theorem node047_checked : node047.check 3 point (5/16) (3/8) = true :=
  OwnershipTree.leaf_checked leaf025 3 point (5/16) (3/8) rfl rfl leaf025_checked

def node048 : OwnershipTree := .leaf leaf026

theorem node048_checked : node048.check 3 point (3/8) (1/2) = true :=
  OwnershipTree.leaf_checked leaf026 3 point (3/8) (1/2) rfl rfl leaf026_checked

def node049 : OwnershipTree := .split (3/8) node047 node048

theorem node049_checked : node049.check 3 point (5/16) (1/2) = true :=
  OwnershipTree.split_checked node047 node048 3 point (5/16) (3/8) (1/2) node047_checked node048_checked

def node050 : OwnershipTree := .split (5/16) node046 node049

theorem node050_checked : node050.check 3 point (9/32) (1/2) = true :=
  OwnershipTree.split_checked node046 node049 3 point (9/32) (5/16) (1/2) node046_checked node049_checked

def node051 : OwnershipTree := .split (9/32) node045 node050

theorem node051_checked : node051.check 3 point (1/4) (1/2) = true :=
  OwnershipTree.split_checked node045 node050 3 point (1/4) (9/32) (1/2) node045_checked node050_checked

def node052 : OwnershipTree := .leaf leaf027

theorem node052_checked : node052.check 3 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf027 3 point (1/2) (5/8) rfl rfl leaf027_checked

def node053 : OwnershipTree := .leaf leaf028

theorem node053_checked : node053.check 3 point (5/8) (11/16) = true :=
  OwnershipTree.leaf_checked leaf028 3 point (5/8) (11/16) rfl rfl leaf028_checked

def node054 : OwnershipTree := .leaf leaf029

theorem node054_checked : node054.check 3 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf029 3 point (11/16) (3/4) rfl rfl leaf029_checked

def node055 : OwnershipTree := .split (11/16) node053 node054

theorem node055_checked : node055.check 3 point (5/8) (3/4) = true :=
  OwnershipTree.split_checked node053 node054 3 point (5/8) (11/16) (3/4) node053_checked node054_checked

def node056 : OwnershipTree := .split (5/8) node052 node055

theorem node056_checked : node056.check 3 point (1/2) (3/4) = true :=
  OwnershipTree.split_checked node052 node055 3 point (1/2) (5/8) (3/4) node052_checked node055_checked

def node057 : OwnershipTree := .leaf leaf030

theorem node057_checked : node057.check 3 point (3/4) (25/32) = true :=
  OwnershipTree.leaf_checked leaf030 3 point (3/4) (25/32) rfl rfl leaf030_checked

def node058 : OwnershipTree := .leaf leaf031

theorem node058_checked : node058.check 3 point (25/32) (13/16) = true :=
  OwnershipTree.leaf_checked leaf031 3 point (25/32) (13/16) rfl rfl leaf031_checked

def node059 : OwnershipTree := .leaf leaf032

theorem node059_checked : node059.check 3 point (13/16) (27/32) = true :=
  OwnershipTree.leaf_checked leaf032 3 point (13/16) (27/32) rfl rfl leaf032_checked

def node060 : OwnershipTree := .split (13/16) node058 node059

theorem node060_checked : node060.check 3 point (25/32) (27/32) = true :=
  OwnershipTree.split_checked node058 node059 3 point (25/32) (13/16) (27/32) node058_checked node059_checked

def node061 : OwnershipTree := .split (25/32) node057 node060

theorem node061_checked : node061.check 3 point (3/4) (27/32) = true :=
  OwnershipTree.split_checked node057 node060 3 point (3/4) (25/32) (27/32) node057_checked node060_checked

def node062 : OwnershipTree := .split (3/4) node056 node061

theorem node062_checked : node062.check 3 point (1/2) (27/32) = true :=
  OwnershipTree.split_checked node056 node061 3 point (1/2) (3/4) (27/32) node056_checked node061_checked

def node063 : OwnershipTree := .split (1/2) node051 node062

theorem node063_checked : node063.check 3 point (1/4) (27/32) = true :=
  OwnershipTree.split_checked node051 node062 3 point (1/4) (1/2) (27/32) node051_checked node062_checked

def node064 : OwnershipTree := .leaf leaf033

theorem node064_checked : node064.check 3 point (27/32) (7/8) = true :=
  OwnershipTree.leaf_checked leaf033 3 point (27/32) (7/8) rfl rfl leaf033_checked

def node065 : OwnershipTree := .leaf leaf034

theorem node065_checked : node065.check 3 point (7/8) (57/64) = true :=
  OwnershipTree.leaf_checked leaf034 3 point (7/8) (57/64) rfl rfl leaf034_checked

def node066 : OwnershipTree := .split (7/8) node064 node065

theorem node066_checked : node066.check 3 point (27/32) (57/64) = true :=
  OwnershipTree.split_checked node064 node065 3 point (27/32) (7/8) (57/64) node064_checked node065_checked

def node067 : OwnershipTree := .leaf leaf035

theorem node067_checked : node067.check 3 point (57/64) (29/32) = true :=
  OwnershipTree.leaf_checked leaf035 3 point (57/64) (29/32) rfl rfl leaf035_checked

def node068 : OwnershipTree := .leaf leaf036

theorem node068_checked : node068.check 3 point (29/32) (59/64) = true :=
  OwnershipTree.leaf_checked leaf036 3 point (29/32) (59/64) rfl rfl leaf036_checked

def node069 : OwnershipTree := .leaf leaf037

theorem node069_checked : node069.check 3 point (59/64) (15/16) = true :=
  OwnershipTree.leaf_checked leaf037 3 point (59/64) (15/16) rfl rfl leaf037_checked

def node070 : OwnershipTree := .split (59/64) node068 node069

theorem node070_checked : node070.check 3 point (29/32) (15/16) = true :=
  OwnershipTree.split_checked node068 node069 3 point (29/32) (59/64) (15/16) node068_checked node069_checked

def node071 : OwnershipTree := .split (29/32) node067 node070

theorem node071_checked : node071.check 3 point (57/64) (15/16) = true :=
  OwnershipTree.split_checked node067 node070 3 point (57/64) (29/32) (15/16) node067_checked node070_checked

def node072 : OwnershipTree := .split (57/64) node066 node071

theorem node072_checked : node072.check 3 point (27/32) (15/16) = true :=
  OwnershipTree.split_checked node066 node071 3 point (27/32) (57/64) (15/16) node066_checked node071_checked

def node073 : OwnershipTree := .leaf leaf038

theorem node073_checked : node073.check 3 point (15/16) (61/64) = true :=
  OwnershipTree.leaf_checked leaf038 3 point (15/16) (61/64) rfl rfl leaf038_checked

def node074 : OwnershipTree := .leaf leaf039

theorem node074_checked : node074.check 3 point (61/64) (31/32) = true :=
  OwnershipTree.leaf_checked leaf039 3 point (61/64) (31/32) rfl rfl leaf039_checked

def node075 : OwnershipTree := .leaf leaf040

theorem node075_checked : node075.check 3 point (31/32) (125/128) = true :=
  OwnershipTree.leaf_checked leaf040 3 point (31/32) (125/128) rfl rfl leaf040_checked

def node076 : OwnershipTree := .split (31/32) node074 node075

theorem node076_checked : node076.check 3 point (61/64) (125/128) = true :=
  OwnershipTree.split_checked node074 node075 3 point (61/64) (31/32) (125/128) node074_checked node075_checked

def node077 : OwnershipTree := .split (61/64) node073 node076

theorem node077_checked : node077.check 3 point (15/16) (125/128) = true :=
  OwnershipTree.split_checked node073 node076 3 point (15/16) (61/64) (125/128) node073_checked node076_checked

def node078 : OwnershipTree := .leaf leaf041

theorem node078_checked : node078.check 3 point (125/128) (63/64) = true :=
  OwnershipTree.leaf_checked leaf041 3 point (125/128) (63/64) rfl rfl leaf041_checked

def node079 : OwnershipTree := .leaf leaf042

theorem node079_checked : node079.check 3 point (63/64) (127/128) = true :=
  OwnershipTree.leaf_checked leaf042 3 point (63/64) (127/128) rfl rfl leaf042_checked

def node080 : OwnershipTree := .leaf leaf043

theorem node080_checked : node080.check 3 point (127/128) 1 = true :=
  OwnershipTree.leaf_checked leaf043 3 point (127/128) 1 rfl rfl leaf043_checked

def node081 : OwnershipTree := .split (127/128) node079 node080

theorem node081_checked : node081.check 3 point (63/64) 1 = true :=
  OwnershipTree.split_checked node079 node080 3 point (63/64) (127/128) 1 node079_checked node080_checked

def node082 : OwnershipTree := .split (63/64) node078 node081

theorem node082_checked : node082.check 3 point (125/128) 1 = true :=
  OwnershipTree.split_checked node078 node081 3 point (125/128) (63/64) 1 node078_checked node081_checked

def node083 : OwnershipTree := .split (125/128) node077 node082

theorem node083_checked : node083.check 3 point (15/16) 1 = true :=
  OwnershipTree.split_checked node077 node082 3 point (15/16) (125/128) 1 node077_checked node082_checked

def node084 : OwnershipTree := .split (15/16) node072 node083

theorem node084_checked : node084.check 3 point (27/32) 1 = true :=
  OwnershipTree.split_checked node072 node083 3 point (27/32) (15/16) 1 node072_checked node083_checked

def node085 : OwnershipTree := .split (27/32) node063 node084

theorem node085_checked : node085.check 3 point (1/4) 1 = true :=
  OwnershipTree.split_checked node063 node084 3 point (1/4) (27/32) 1 node063_checked node084_checked

def node086 : OwnershipTree := .split (1/4) node042 node085

theorem node086_checked : node086.check 3 point 0 1 = true :=
  OwnershipTree.split_checked node042 node085 3 point 0 (1/4) 1 node042_checked node085_checked

def certificate : OwnershipTree := node086

theorem checked : certificate.check 3 point 0 1 = true := node086_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 3 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 3 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned03_05
