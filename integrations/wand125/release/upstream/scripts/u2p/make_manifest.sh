#!/bin/sh
# Final U2Prior MANIFEST: headers for regen.py, then sha256 of every generated .lean of the 76 cases.
cd $HOME/n11u2p/Sqpack/S11Opt/Split/U2P
{
echo "# U2Prior generated files (scripts/u2p), sha256 of the files checked by the kernel"
echo "# prefix U2P"
echo "# branch 655 3"
echo "# branch 761 5"
echo "# profile 761 fine"
echo "# branch 1383 5"
echo "# profile 1383 fine"
echo "# kmax 1383 0"
echo "# chunk 1383 300"
echo "# part 1383 40"
echo "# branch 1839 3"
for d in $(find . -maxdepth 1 -type d -name "C*" -printf "%f\n" | sort -V); do sha256sum $d/*.lean; done
} > $HOME/MANIFEST_U2P.sha256
