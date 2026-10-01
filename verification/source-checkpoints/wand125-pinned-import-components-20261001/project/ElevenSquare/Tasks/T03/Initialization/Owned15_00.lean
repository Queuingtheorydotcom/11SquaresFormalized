import ElevenSquare.Tasks.T03.TreeChecks
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part000
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part001
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part002
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part003
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part004
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part005
import ElevenSquare.Tasks.T03.Initialization.Owned15_00Part006

namespace ElevenSquare.Pending.T03.Initialization.Owned15_00
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def node000 : OwnershipTree := .leaf leaf000

theorem node000_checked : node000.check 15 point 0 (1/256) = true :=
  OwnershipTree.leaf_checked leaf000 15 point 0 (1/256) rfl rfl leaf000_checked

def node001 : OwnershipTree := .leaf leaf001

theorem node001_checked : node001.check 15 point (1/256) (1/128) = true :=
  OwnershipTree.leaf_checked leaf001 15 point (1/256) (1/128) rfl rfl leaf001_checked

def node002 : OwnershipTree := .leaf leaf002

theorem node002_checked : node002.check 15 point (1/128) (3/256) = true :=
  OwnershipTree.leaf_checked leaf002 15 point (1/128) (3/256) rfl rfl leaf002_checked

def node003 : OwnershipTree := .split (1/128) node001 node002

theorem node003_checked : node003.check 15 point (1/256) (3/256) = true :=
  OwnershipTree.split_checked node001 node002 15 point (1/256) (1/128) (3/256) node001_checked node002_checked

def node004 : OwnershipTree := .split (1/256) node000 node003

theorem node004_checked : node004.check 15 point 0 (3/256) = true :=
  OwnershipTree.split_checked node000 node003 15 point 0 (1/256) (3/256) node000_checked node003_checked

def node005 : OwnershipTree := .leaf leaf003

theorem node005_checked : node005.check 15 point (3/256) (1/64) = true :=
  OwnershipTree.leaf_checked leaf003 15 point (3/256) (1/64) rfl rfl leaf003_checked

def node006 : OwnershipTree := .leaf leaf004

theorem node006_checked : node006.check 15 point (1/64) (5/256) = true :=
  OwnershipTree.leaf_checked leaf004 15 point (1/64) (5/256) rfl rfl leaf004_checked

def node007 : OwnershipTree := .leaf leaf005

theorem node007_checked : node007.check 15 point (5/256) (3/128) = true :=
  OwnershipTree.leaf_checked leaf005 15 point (5/256) (3/128) rfl rfl leaf005_checked

def node008 : OwnershipTree := .split (5/256) node006 node007

theorem node008_checked : node008.check 15 point (1/64) (3/128) = true :=
  OwnershipTree.split_checked node006 node007 15 point (1/64) (5/256) (3/128) node006_checked node007_checked

def node009 : OwnershipTree := .split (1/64) node005 node008

theorem node009_checked : node009.check 15 point (3/256) (3/128) = true :=
  OwnershipTree.split_checked node005 node008 15 point (3/256) (1/64) (3/128) node005_checked node008_checked

def node010 : OwnershipTree := .split (3/256) node004 node009

theorem node010_checked : node010.check 15 point 0 (3/128) = true :=
  OwnershipTree.split_checked node004 node009 15 point 0 (3/256) (3/128) node004_checked node009_checked

def node011 : OwnershipTree := .leaf leaf006

theorem node011_checked : node011.check 15 point (3/128) (7/256) = true :=
  OwnershipTree.leaf_checked leaf006 15 point (3/128) (7/256) rfl rfl leaf006_checked

def node012 : OwnershipTree := .leaf leaf007

theorem node012_checked : node012.check 15 point (7/256) (1/32) = true :=
  OwnershipTree.leaf_checked leaf007 15 point (7/256) (1/32) rfl rfl leaf007_checked

def node013 : OwnershipTree := .leaf leaf008

theorem node013_checked : node013.check 15 point (1/32) (9/256) = true :=
  OwnershipTree.leaf_checked leaf008 15 point (1/32) (9/256) rfl rfl leaf008_checked

def node014 : OwnershipTree := .split (1/32) node012 node013

theorem node014_checked : node014.check 15 point (7/256) (9/256) = true :=
  OwnershipTree.split_checked node012 node013 15 point (7/256) (1/32) (9/256) node012_checked node013_checked

def node015 : OwnershipTree := .split (7/256) node011 node014

theorem node015_checked : node015.check 15 point (3/128) (9/256) = true :=
  OwnershipTree.split_checked node011 node014 15 point (3/128) (7/256) (9/256) node011_checked node014_checked

def node016 : OwnershipTree := .leaf leaf009

theorem node016_checked : node016.check 15 point (9/256) (5/128) = true :=
  OwnershipTree.leaf_checked leaf009 15 point (9/256) (5/128) rfl rfl leaf009_checked

def node017 : OwnershipTree := .leaf leaf010

theorem node017_checked : node017.check 15 point (5/128) (3/64) = true :=
  OwnershipTree.leaf_checked leaf010 15 point (5/128) (3/64) rfl rfl leaf010_checked

def node018 : OwnershipTree := .leaf leaf011

theorem node018_checked : node018.check 15 point (3/64) (7/128) = true :=
  OwnershipTree.leaf_checked leaf011 15 point (3/64) (7/128) rfl rfl leaf011_checked

def node019 : OwnershipTree := .split (3/64) node017 node018

theorem node019_checked : node019.check 15 point (5/128) (7/128) = true :=
  OwnershipTree.split_checked node017 node018 15 point (5/128) (3/64) (7/128) node017_checked node018_checked

def node020 : OwnershipTree := .split (5/128) node016 node019

theorem node020_checked : node020.check 15 point (9/256) (7/128) = true :=
  OwnershipTree.split_checked node016 node019 15 point (9/256) (5/128) (7/128) node016_checked node019_checked

def node021 : OwnershipTree := .split (9/256) node015 node020

theorem node021_checked : node021.check 15 point (3/128) (7/128) = true :=
  OwnershipTree.split_checked node015 node020 15 point (3/128) (9/256) (7/128) node015_checked node020_checked

def node022 : OwnershipTree := .split (3/128) node010 node021

theorem node022_checked : node022.check 15 point 0 (7/128) = true :=
  OwnershipTree.split_checked node010 node021 15 point 0 (3/128) (7/128) node010_checked node021_checked

def node023 : OwnershipTree := .leaf leaf012

theorem node023_checked : node023.check 15 point (7/128) (1/16) = true :=
  OwnershipTree.leaf_checked leaf012 15 point (7/128) (1/16) rfl rfl leaf012_checked

def node024 : OwnershipTree := .leaf leaf013

theorem node024_checked : node024.check 15 point (1/16) (9/128) = true :=
  OwnershipTree.leaf_checked leaf013 15 point (1/16) (9/128) rfl rfl leaf013_checked

def node025 : OwnershipTree := .leaf leaf014

theorem node025_checked : node025.check 15 point (9/128) (5/64) = true :=
  OwnershipTree.leaf_checked leaf014 15 point (9/128) (5/64) rfl rfl leaf014_checked

def node026 : OwnershipTree := .split (9/128) node024 node025

theorem node026_checked : node026.check 15 point (1/16) (5/64) = true :=
  OwnershipTree.split_checked node024 node025 15 point (1/16) (9/128) (5/64) node024_checked node025_checked

def node027 : OwnershipTree := .split (1/16) node023 node026

theorem node027_checked : node027.check 15 point (7/128) (5/64) = true :=
  OwnershipTree.split_checked node023 node026 15 point (7/128) (1/16) (5/64) node023_checked node026_checked

def node028 : OwnershipTree := .leaf leaf015

theorem node028_checked : node028.check 15 point (5/64) (3/32) = true :=
  OwnershipTree.leaf_checked leaf015 15 point (5/64) (3/32) rfl rfl leaf015_checked

def node029 : OwnershipTree := .leaf leaf016

theorem node029_checked : node029.check 15 point (3/32) (7/64) = true :=
  OwnershipTree.leaf_checked leaf016 15 point (3/32) (7/64) rfl rfl leaf016_checked

def node030 : OwnershipTree := .leaf leaf017

theorem node030_checked : node030.check 15 point (7/64) (1/8) = true :=
  OwnershipTree.leaf_checked leaf017 15 point (7/64) (1/8) rfl rfl leaf017_checked

def node031 : OwnershipTree := .split (7/64) node029 node030

theorem node031_checked : node031.check 15 point (3/32) (1/8) = true :=
  OwnershipTree.split_checked node029 node030 15 point (3/32) (7/64) (1/8) node029_checked node030_checked

def node032 : OwnershipTree := .split (3/32) node028 node031

theorem node032_checked : node032.check 15 point (5/64) (1/8) = true :=
  OwnershipTree.split_checked node028 node031 15 point (5/64) (3/32) (1/8) node028_checked node031_checked

def node033 : OwnershipTree := .split (5/64) node027 node032

theorem node033_checked : node033.check 15 point (7/128) (1/8) = true :=
  OwnershipTree.split_checked node027 node032 15 point (7/128) (5/64) (1/8) node027_checked node032_checked

def node034 : OwnershipTree := .leaf leaf018

theorem node034_checked : node034.check 15 point (1/8) (5/32) = true :=
  OwnershipTree.leaf_checked leaf018 15 point (1/8) (5/32) rfl rfl leaf018_checked

def node035 : OwnershipTree := .leaf leaf019

theorem node035_checked : node035.check 15 point (5/32) (3/16) = true :=
  OwnershipTree.leaf_checked leaf019 15 point (5/32) (3/16) rfl rfl leaf019_checked

def node036 : OwnershipTree := .leaf leaf020

theorem node036_checked : node036.check 15 point (3/16) (1/4) = true :=
  OwnershipTree.leaf_checked leaf020 15 point (3/16) (1/4) rfl rfl leaf020_checked

def node037 : OwnershipTree := .split (3/16) node035 node036

theorem node037_checked : node037.check 15 point (5/32) (1/4) = true :=
  OwnershipTree.split_checked node035 node036 15 point (5/32) (3/16) (1/4) node035_checked node036_checked

def node038 : OwnershipTree := .split (5/32) node034 node037

theorem node038_checked : node038.check 15 point (1/8) (1/4) = true :=
  OwnershipTree.split_checked node034 node037 15 point (1/8) (5/32) (1/4) node034_checked node037_checked

def node039 : OwnershipTree := .leaf leaf021

theorem node039_checked : node039.check 15 point (1/4) (1/2) = true :=
  OwnershipTree.leaf_checked leaf021 15 point (1/4) (1/2) rfl rfl leaf021_checked

def node040 : OwnershipTree := .leaf leaf022

theorem node040_checked : node040.check 15 point (1/2) (5/8) = true :=
  OwnershipTree.leaf_checked leaf022 15 point (1/2) (5/8) rfl rfl leaf022_checked

def node041 : OwnershipTree := .split (1/2) node039 node040

theorem node041_checked : node041.check 15 point (1/4) (5/8) = true :=
  OwnershipTree.split_checked node039 node040 15 point (1/4) (1/2) (5/8) node039_checked node040_checked

def node042 : OwnershipTree := .leaf leaf023

theorem node042_checked : node042.check 15 point (5/8) (11/16) = true :=
  OwnershipTree.leaf_checked leaf023 15 point (5/8) (11/16) rfl rfl leaf023_checked

def node043 : OwnershipTree := .leaf leaf024

theorem node043_checked : node043.check 15 point (11/16) (3/4) = true :=
  OwnershipTree.leaf_checked leaf024 15 point (11/16) (3/4) rfl rfl leaf024_checked

def node044 : OwnershipTree := .split (11/16) node042 node043

theorem node044_checked : node044.check 15 point (5/8) (3/4) = true :=
  OwnershipTree.split_checked node042 node043 15 point (5/8) (11/16) (3/4) node042_checked node043_checked

def node045 : OwnershipTree := .split (5/8) node041 node044

theorem node045_checked : node045.check 15 point (1/4) (3/4) = true :=
  OwnershipTree.split_checked node041 node044 15 point (1/4) (5/8) (3/4) node041_checked node044_checked

def node046 : OwnershipTree := .split (1/4) node038 node045

theorem node046_checked : node046.check 15 point (1/8) (3/4) = true :=
  OwnershipTree.split_checked node038 node045 15 point (1/8) (1/4) (3/4) node038_checked node045_checked

def node047 : OwnershipTree := .split (1/8) node033 node046

theorem node047_checked : node047.check 15 point (7/128) (3/4) = true :=
  OwnershipTree.split_checked node033 node046 15 point (7/128) (1/8) (3/4) node033_checked node046_checked

def node048 : OwnershipTree := .split (7/128) node022 node047

theorem node048_checked : node048.check 15 point 0 (3/4) = true :=
  OwnershipTree.split_checked node022 node047 15 point 0 (7/128) (3/4) node022_checked node047_checked

def node049 : OwnershipTree := .leaf leaf025

theorem node049_checked : node049.check 15 point (3/4) (25/32) = true :=
  OwnershipTree.leaf_checked leaf025 15 point (3/4) (25/32) rfl rfl leaf025_checked

def node050 : OwnershipTree := .leaf leaf026

theorem node050_checked : node050.check 15 point (25/32) (13/16) = true :=
  OwnershipTree.leaf_checked leaf026 15 point (25/32) (13/16) rfl rfl leaf026_checked

def node051 : OwnershipTree := .leaf leaf027

theorem node051_checked : node051.check 15 point (13/16) (27/32) = true :=
  OwnershipTree.leaf_checked leaf027 15 point (13/16) (27/32) rfl rfl leaf027_checked

def node052 : OwnershipTree := .split (13/16) node050 node051

theorem node052_checked : node052.check 15 point (25/32) (27/32) = true :=
  OwnershipTree.split_checked node050 node051 15 point (25/32) (13/16) (27/32) node050_checked node051_checked

def node053 : OwnershipTree := .split (25/32) node049 node052

theorem node053_checked : node053.check 15 point (3/4) (27/32) = true :=
  OwnershipTree.split_checked node049 node052 15 point (3/4) (25/32) (27/32) node049_checked node052_checked

def node054 : OwnershipTree := .leaf leaf028

theorem node054_checked : node054.check 15 point (27/32) (55/64) = true :=
  OwnershipTree.leaf_checked leaf028 15 point (27/32) (55/64) rfl rfl leaf028_checked

def node055 : OwnershipTree := .leaf leaf029

theorem node055_checked : node055.check 15 point (55/64) (7/8) = true :=
  OwnershipTree.leaf_checked leaf029 15 point (55/64) (7/8) rfl rfl leaf029_checked

def node056 : OwnershipTree := .leaf leaf030

theorem node056_checked : node056.check 15 point (7/8) (57/64) = true :=
  OwnershipTree.leaf_checked leaf030 15 point (7/8) (57/64) rfl rfl leaf030_checked

def node057 : OwnershipTree := .split (7/8) node055 node056

theorem node057_checked : node057.check 15 point (55/64) (57/64) = true :=
  OwnershipTree.split_checked node055 node056 15 point (55/64) (7/8) (57/64) node055_checked node056_checked

def node058 : OwnershipTree := .split (55/64) node054 node057

theorem node058_checked : node058.check 15 point (27/32) (57/64) = true :=
  OwnershipTree.split_checked node054 node057 15 point (27/32) (55/64) (57/64) node054_checked node057_checked

def node059 : OwnershipTree := .split (27/32) node053 node058

theorem node059_checked : node059.check 15 point (3/4) (57/64) = true :=
  OwnershipTree.split_checked node053 node058 15 point (3/4) (27/32) (57/64) node053_checked node058_checked

def node060 : OwnershipTree := .leaf leaf031

theorem node060_checked : node060.check 15 point (57/64) (29/32) = true :=
  OwnershipTree.leaf_checked leaf031 15 point (57/64) (29/32) rfl rfl leaf031_checked

def node061 : OwnershipTree := .leaf leaf032

theorem node061_checked : node061.check 15 point (29/32) (117/128) = true :=
  OwnershipTree.leaf_checked leaf032 15 point (29/32) (117/128) rfl rfl leaf032_checked

def node062 : OwnershipTree := .leaf leaf033

theorem node062_checked : node062.check 15 point (117/128) (59/64) = true :=
  OwnershipTree.leaf_checked leaf033 15 point (117/128) (59/64) rfl rfl leaf033_checked

def node063 : OwnershipTree := .split (117/128) node061 node062

theorem node063_checked : node063.check 15 point (29/32) (59/64) = true :=
  OwnershipTree.split_checked node061 node062 15 point (29/32) (117/128) (59/64) node061_checked node062_checked

def node064 : OwnershipTree := .split (29/32) node060 node063

theorem node064_checked : node064.check 15 point (57/64) (59/64) = true :=
  OwnershipTree.split_checked node060 node063 15 point (57/64) (29/32) (59/64) node060_checked node063_checked

def node065 : OwnershipTree := .leaf leaf034

theorem node065_checked : node065.check 15 point (59/64) (119/128) = true :=
  OwnershipTree.leaf_checked leaf034 15 point (59/64) (119/128) rfl rfl leaf034_checked

def node066 : OwnershipTree := .leaf leaf035

theorem node066_checked : node066.check 15 point (119/128) (15/16) = true :=
  OwnershipTree.leaf_checked leaf035 15 point (119/128) (15/16) rfl rfl leaf035_checked

def node067 : OwnershipTree := .split (119/128) node065 node066

theorem node067_checked : node067.check 15 point (59/64) (15/16) = true :=
  OwnershipTree.split_checked node065 node066 15 point (59/64) (119/128) (15/16) node065_checked node066_checked

def node068 : OwnershipTree := .leaf leaf036

theorem node068_checked : node068.check 15 point (15/16) (121/128) = true :=
  OwnershipTree.leaf_checked leaf036 15 point (15/16) (121/128) rfl rfl leaf036_checked

def node069 : OwnershipTree := .leaf leaf037

theorem node069_checked : node069.check 15 point (121/128) (243/256) = true :=
  OwnershipTree.leaf_checked leaf037 15 point (121/128) (243/256) rfl rfl leaf037_checked

def node070 : OwnershipTree := .split (121/128) node068 node069

theorem node070_checked : node070.check 15 point (15/16) (243/256) = true :=
  OwnershipTree.split_checked node068 node069 15 point (15/16) (121/128) (243/256) node068_checked node069_checked

def node071 : OwnershipTree := .split (15/16) node067 node070

theorem node071_checked : node071.check 15 point (59/64) (243/256) = true :=
  OwnershipTree.split_checked node067 node070 15 point (59/64) (15/16) (243/256) node067_checked node070_checked

def node072 : OwnershipTree := .split (59/64) node064 node071

theorem node072_checked : node072.check 15 point (57/64) (243/256) = true :=
  OwnershipTree.split_checked node064 node071 15 point (57/64) (59/64) (243/256) node064_checked node071_checked

def node073 : OwnershipTree := .split (57/64) node059 node072

theorem node073_checked : node073.check 15 point (3/4) (243/256) = true :=
  OwnershipTree.split_checked node059 node072 15 point (3/4) (57/64) (243/256) node059_checked node072_checked

def node074 : OwnershipTree := .leaf leaf038

theorem node074_checked : node074.check 15 point (243/256) (61/64) = true :=
  OwnershipTree.leaf_checked leaf038 15 point (243/256) (61/64) rfl rfl leaf038_checked

def node075 : OwnershipTree := .leaf leaf039

theorem node075_checked : node075.check 15 point (61/64) (245/256) = true :=
  OwnershipTree.leaf_checked leaf039 15 point (61/64) (245/256) rfl rfl leaf039_checked

def node076 : OwnershipTree := .leaf leaf040

theorem node076_checked : node076.check 15 point (245/256) (123/128) = true :=
  OwnershipTree.leaf_checked leaf040 15 point (245/256) (123/128) rfl rfl leaf040_checked

def node077 : OwnershipTree := .split (245/256) node075 node076

theorem node077_checked : node077.check 15 point (61/64) (123/128) = true :=
  OwnershipTree.split_checked node075 node076 15 point (61/64) (245/256) (123/128) node075_checked node076_checked

def node078 : OwnershipTree := .split (61/64) node074 node077

theorem node078_checked : node078.check 15 point (243/256) (123/128) = true :=
  OwnershipTree.split_checked node074 node077 15 point (243/256) (61/64) (123/128) node074_checked node077_checked

def node079 : OwnershipTree := .leaf leaf041

theorem node079_checked : node079.check 15 point (123/128) (247/256) = true :=
  OwnershipTree.leaf_checked leaf041 15 point (123/128) (247/256) rfl rfl leaf041_checked

def node080 : OwnershipTree := .leaf leaf042

theorem node080_checked : node080.check 15 point (247/256) (31/32) = true :=
  OwnershipTree.leaf_checked leaf042 15 point (247/256) (31/32) rfl rfl leaf042_checked

def node081 : OwnershipTree := .leaf leaf043

theorem node081_checked : node081.check 15 point (31/32) (249/256) = true :=
  OwnershipTree.leaf_checked leaf043 15 point (31/32) (249/256) rfl rfl leaf043_checked

def node082 : OwnershipTree := .split (31/32) node080 node081

theorem node082_checked : node082.check 15 point (247/256) (249/256) = true :=
  OwnershipTree.split_checked node080 node081 15 point (247/256) (31/32) (249/256) node080_checked node081_checked

def node083 : OwnershipTree := .split (247/256) node079 node082

theorem node083_checked : node083.check 15 point (123/128) (249/256) = true :=
  OwnershipTree.split_checked node079 node082 15 point (123/128) (247/256) (249/256) node079_checked node082_checked

def node084 : OwnershipTree := .split (123/128) node078 node083

theorem node084_checked : node084.check 15 point (243/256) (249/256) = true :=
  OwnershipTree.split_checked node078 node083 15 point (243/256) (123/128) (249/256) node078_checked node083_checked

def node085 : OwnershipTree := .leaf leaf044

theorem node085_checked : node085.check 15 point (249/256) (125/128) = true :=
  OwnershipTree.leaf_checked leaf044 15 point (249/256) (125/128) rfl rfl leaf044_checked

def node086 : OwnershipTree := .leaf leaf045

theorem node086_checked : node086.check 15 point (125/128) (251/256) = true :=
  OwnershipTree.leaf_checked leaf045 15 point (125/128) (251/256) rfl rfl leaf045_checked

def node087 : OwnershipTree := .leaf leaf046

theorem node087_checked : node087.check 15 point (251/256) (63/64) = true :=
  OwnershipTree.leaf_checked leaf046 15 point (251/256) (63/64) rfl rfl leaf046_checked

def node088 : OwnershipTree := .split (251/256) node086 node087

theorem node088_checked : node088.check 15 point (125/128) (63/64) = true :=
  OwnershipTree.split_checked node086 node087 15 point (125/128) (251/256) (63/64) node086_checked node087_checked

def node089 : OwnershipTree := .split (125/128) node085 node088

theorem node089_checked : node089.check 15 point (249/256) (63/64) = true :=
  OwnershipTree.split_checked node085 node088 15 point (249/256) (125/128) (63/64) node085_checked node088_checked

def node090 : OwnershipTree := .leaf leaf047

theorem node090_checked : node090.check 15 point (63/64) (253/256) = true :=
  OwnershipTree.leaf_checked leaf047 15 point (63/64) (253/256) rfl rfl leaf047_checked

def node091 : OwnershipTree := .leaf leaf048

theorem node091_checked : node091.check 15 point (253/256) (127/128) = true :=
  OwnershipTree.leaf_checked leaf048 15 point (253/256) (127/128) rfl rfl leaf048_checked

def node092 : OwnershipTree := .split (253/256) node090 node091

theorem node092_checked : node092.check 15 point (63/64) (127/128) = true :=
  OwnershipTree.split_checked node090 node091 15 point (63/64) (253/256) (127/128) node090_checked node091_checked

def node093 : OwnershipTree := .leaf leaf049

theorem node093_checked : node093.check 15 point (127/128) (255/256) = true :=
  OwnershipTree.leaf_checked leaf049 15 point (127/128) (255/256) rfl rfl leaf049_checked

def node094 : OwnershipTree := .leaf leaf050

theorem node094_checked : node094.check 15 point (255/256) 1 = true :=
  OwnershipTree.leaf_checked leaf050 15 point (255/256) 1 rfl rfl leaf050_checked

def node095 : OwnershipTree := .split (255/256) node093 node094

theorem node095_checked : node095.check 15 point (127/128) 1 = true :=
  OwnershipTree.split_checked node093 node094 15 point (127/128) (255/256) 1 node093_checked node094_checked

def node096 : OwnershipTree := .split (127/128) node092 node095

theorem node096_checked : node096.check 15 point (63/64) 1 = true :=
  OwnershipTree.split_checked node092 node095 15 point (63/64) (127/128) 1 node092_checked node095_checked

def node097 : OwnershipTree := .split (63/64) node089 node096

theorem node097_checked : node097.check 15 point (249/256) 1 = true :=
  OwnershipTree.split_checked node089 node096 15 point (249/256) (63/64) 1 node089_checked node096_checked

def node098 : OwnershipTree := .split (249/256) node084 node097

theorem node098_checked : node098.check 15 point (243/256) 1 = true :=
  OwnershipTree.split_checked node084 node097 15 point (243/256) (249/256) 1 node084_checked node097_checked

def node099 : OwnershipTree := .split (243/256) node073 node098

theorem node099_checked : node099.check 15 point (3/4) 1 = true :=
  OwnershipTree.split_checked node073 node098 15 point (3/4) (243/256) 1 node073_checked node098_checked

def node100 : OwnershipTree := .split (3/4) node048 node099

theorem node100_checked : node100.check 15 point 0 1 = true :=
  OwnershipTree.split_checked node048 node099 15 point 0 (3/4) 1 node048_checked node099_checked

def certificate : OwnershipTree := node100

theorem checked : certificate.check 15 point 0 1 = true := node100_checked

theorem owned (q : UnitSquare) (t : ℝ)
    (hc : ∀ p, ClosedSquare q p → InContainer coverCap p)
    (hcell : ClosedCell 15 (normalizeCenter q.center))
    (hq : q.axis = chartAxis t) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    OpenSquare q (realPoint point) := by
  exact certificate.sound 15 point 0 1 checked q t hc hcell hq
    (by simpa using ht0) (by simpa using ht1)

end
end ElevenSquare.Pending.T03.Initialization.Owned15_00
